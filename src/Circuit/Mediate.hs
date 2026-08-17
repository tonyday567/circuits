-- | Mediator abstraction as a thin wrapper over 'Circuit.Process' and
-- 'Circuit.Ends'.
--
-- A mediator is a Mealy-style state machine with residual state @s@. It
-- consumes inputs of type @a@ and may produce outputs of type @b@. The
-- residual state is what persists between interactions.
--
-- Conceptually a mediator is just a 'Process' that may skip outputs:
--
-- @
--   Mediator s a b  ≈  Process a (Maybe b)
-- @
--
-- It is also a pole-unfused pair of channel ends over the ambient-state arrow
-- @SArr (s, Maybe b)@; see 'Circuit.Ends.mediatorToMed' and
-- 'Circuit.Ends.medToMediator' for the conversions.
--
-- The wrapper keeps the residual type @s@ exposed so that close certification
-- can inspect the final state. All streaming behaviour is delegated to the
-- underlying 'Process': 'runMediator' is 'scan' followed by 'catMaybes',
-- and 'mediateLoop' is 'Circuit.Process.encode'.
--
-- The shared-medium fusion ('mediateSharedBody') exposes the two poles of the
-- mediator as the store and emit bodies of an @Ends (Kleisli (State s))@
-- channel, threaded by a 'Circuit.Tensor.Fire' schedule.
module Circuit.Mediate
  ( -- * Mediator state machine
    Mediator (..),
    runMediator,
    runMediatorState,

    -- * Close certification
    LinearResidual (..),
    FlushableResidual (..),
    LinearityViolation (..),
    closeCertified,
    closeCertifiedWith,
    closeCertifiedWithBy,

    -- * ?-comonoid structure
    medCounit,
    medComult,

    -- * Stream / loop views
    mediateProcess,
    mediateLoop,

    -- * Reusable mediator configurations
    linear,
    pairSum,
    count,

    -- * Pair-sum residual (distinguishes held half-pair from ready output)
    PS (..),

    -- * Shared-medium fusion
    mediateSharedBody,
    mediateStoreBody,
    mediateEmitBody,

    -- * Shared-medium audit
    Debt (..),
    mediateSharedBodyChecked,
    runSharedBodyChecked,
  )
where

import Circuit.Loop (Loop)
import Circuit.Process (Process, scan)
import Circuit.Process qualified as Process
import Circuit.Tensor (Bias (..), Fire (..), Schedule (..), chooseS)
import Data.List (mapAccumL, uncons)
import Data.Maybe (catMaybes, isNothing)
import Data.These (These (..))

-- | A mediator with state @s@, input @a@, output @b@.
--
-- The step function consumes one input and updates the state. It may emit zero
-- or one output. A 'Nothing' output means the mediator is still accumulating
-- state.
--
-- The 'medOwed' predicate selects which states carry /resource debt/: a
-- certified close succeeds exactly when the final state is not owed. This
-- separates the state from the reading of the state. 'LinearResidual' is now
-- a convenience source of 'medOwed', not the definition of residual.
--
-- This record is a thin wrapper: the canonical stream view is obtained via
-- 'mediateProcess'.
data Mediator s a b = Mediator
  { -- | Initial state.
    medInit :: s,
    -- | Consume one input, update state, optionally emit output.
    medStep :: s -> a -> (s, Maybe b),
    -- | Predicate selecting states that are owed / residual at close time.
    medOwed :: s -> Bool,
    -- | Overdraw check for shared-medium ticks.  Given the state before and
    -- after a tick, return the overdraw amount if the step consumed more than
    -- one unit of resource.  'Nothing' means no overdraw.
    medDraw :: s -> s -> Maybe Int
  }

-- | Run a mediator over a list of inputs, collecting both the emitted outputs
-- and the final residual state.
--
-- This is the direct state-passing semantics; it is the reference against
-- which the 'Process'-derived 'runMediator' is checked.
runMediatorState :: Mediator s a b -> s -> [a] -> (s, [b])
runMediatorState m s0 xs =
  let (sFinal, mys) = mapAccumL (medStep m) s0 xs
   in (sFinal, catMaybes mys)

-- | Run a mediator over a list of inputs, collecting emitted outputs.
--
-- This delegates to the underlying 'Process' view: push inputs strictly and
-- pull whenever the mediator is willing to emit.
runMediator :: Mediator s a b -> [a] -> [b]
runMediator m = catMaybes . scan (mediateProcess m (medInit m))

-- | Types whose state has a canonical empty value.
--
-- This is a convenience source for the 'medOwed' predicate: when a mediator
-- is built from a 'LinearResidual' state, 'isEmptyResidual' is the natural
-- choice for 'medOwed'. It is no longer the definition of residualness;
-- 'closeCertified' uses 'medOwed' directly.
class LinearResidual s where
  -- | The canonical empty residual state.
  emptyResidual :: s

  -- | Test whether the residual is the canonical empty value.
  --
  -- This removes the 'Eq' requirement from 'closeCertified' and lets
  -- non-trivial equality tests (e.g. a predicate on a record) live with the
  -- instance.
  isEmptyResidual :: s -> Bool

instance LinearResidual () where
  emptyResidual = ()
  isEmptyResidual _ = True

instance LinearResidual (Maybe a) where
  emptyResidual = Nothing
  isEmptyResidual = isNothing

instance LinearResidual [a] where
  emptyResidual = []
  isEmptyResidual = null

-- | @Int@ is treated as a count residual; the empty value is @0@.
instance LinearResidual Int where
  emptyResidual = 0
  isEmptyResidual = (== 0)

-- | Product residuals are empty when both components are empty.
--
-- This supports the buffer-slot residual shape @(s, Maybe (Maybe b))@ used by
-- 'mediatorToMed'.
instance (LinearResidual s, LinearResidual t) => LinearResidual (s, t) where
  emptyResidual = (emptyResidual, emptyResidual)
  isEmptyResidual (s, t) = isEmptyResidual s && isEmptyResidual t

-- | Residuals that can be drained into output at close time.
--
-- A flushable residual is still a linear residual: if it is empty, close is
-- clean.  When it is non-empty, 'flushStep' may emit one output value and
-- leave a smaller residual.  If 'flushStep' returns 'Nothing', the residual is
-- a genuine violation.
--
-- 'count' and list buffers are flushable; a held half-pair ('PS.Held') is not.
class (LinearResidual s) => FlushableResidual s b where
  -- | Drain one output from the residual, returning the remaining residual.
  flushStep :: s -> Maybe (b, s)

-- | @Int@ count residual flushes its accumulated value once and resets to 0.
instance FlushableResidual Int Int where
  flushStep n = if isEmptyResidual n then Nothing else Just (n, 0)

-- | List residual flushes head-first.
instance FlushableResidual [a] a where
  flushStep = uncons

-- | @Maybe b@ residual flushes a held output value.
instance FlushableResidual (Maybe b) b where
  flushStep Nothing = Nothing
  flushStep (Just b) = Just (b, Nothing)

-- | Two-state residual for pair summation.
--
-- * 'Empty' : no buffered value.
-- * 'Held'  : one value buffered, not yet ready.
--
-- The Mealy-style 'pairSum' emits the sum in the same tick that completes the
-- pair and returns to 'Empty'.  A 'Held' value at close is a genuine half-pair
-- violation; there is no 'FlushableResidual' instance for 'PS'.
data PS = Empty | Held Int
  deriving (Eq, Show)

instance LinearResidual PS where
  emptyResidual = Empty
  isEmptyResidual Empty = True
  isEmptyResidual _ = False

-- | Convenience source for the 'medDraw' predicate.
--
-- A state may carry a notion of /debt/: how much resource was consumed in a
-- single tick beyond the one input the mediator is allowed to process.  This
-- class supplies a default 'medDraw' for such states.  Like 'LinearResidual',
-- it is a convenience, not the definition of overdraw — the per-mediator
-- 'medDraw' field can disagree with the class default.
class (LinearResidual s) => Debt s where
  -- | Return the overdraw amount if the state transition consumed more than
  -- one unit of resource.  'Nothing' means no overdraw.
  debtDraw :: s -> s -> Maybe Int

-- | @Int@ treated as a count residual: a single mediator step may increase it
-- by one; a transition that increases it by more than one is an overdraw.
--
-- This is the semantics of 'count', not a property of 'Int' in general.  A
-- budget mediator that decrements 'Int' should supply its own 'medDraw'.
instance Debt Int where
  debtDraw old new =
    let d = new - old - 1
     in if d > 0 then Just d else Nothing

-- | A violation reported when a certified close finds the residual state is not
-- empty.
newtype LinearityViolation = LinearityViolation String
  deriving (Eq, Show)

-- | Run a mediator over a stream and certify that the final state is not owed.
--
-- If @'medOwed' m sFinal@ is 'False', return the emitted outputs.  Otherwise
-- report a 'LinearityViolation' carrying the offending state.
--
-- This is the /strict/ close semantics: an owed state is a violation even if
-- it could be flushed into output.  For flushable states use
-- 'closeCertifiedWith'.
--
-- The seed @s0@ is a /resumption point/: it is the state at the start of the
-- certified fragment.  The canonical run 'runMediator' starts from 'medInit',
-- so certifying from any other state is valid only when that state is reachable
-- from 'medInit'.
closeCertified :: (Show s) => Mediator s a b -> s -> [a] -> Either LinearityViolation [b]
closeCertified m s0 as =
  let (sFinal, bs) = runMediatorState m s0 as
   in if medOwed m sFinal
        then Left (LinearityViolation ("close: state owed: " ++ show sFinal))
        else Right bs

-- | Run a mediator over a stream and certify that any remaining owed state can
-- be drained according to its 'FlushableResidual' instance.
--
-- This is the flush semantics: state is a violation only when it is owed (per
-- 'medOwed') and 'flushStep' cannot drain it.  The empty test is
-- @not . medOwed m@, so only owed states are flushed.  'count' is state, not
-- residual, and is not flushed; a list buffer flushes head-first; a 'Ready'
-- sum flushes; a 'Held' half-pair reports a violation.
--
-- The seed @s0@ is a /resumption point/; see 'closeCertified'.
closeCertifiedWith ::
  (FlushableResidual s b, Show s) =>
  Mediator s a b ->
  s ->
  [a] ->
  Either LinearityViolation [b]
closeCertifiedWith m = closeCertifiedWithBy (not . medOwed m) flushStep m

-- | Run a mediator over a stream and certify that any remaining state can be
-- drained via explicit empty/drain functions.
--
-- This is the escape hatch for custom state policies that do not have a
-- 'FlushableResidual' instance.
--
-- The seed @s0@ is a /resumption point/; see 'closeCertified'.
closeCertifiedWithBy ::
  (Show s) =>
  -- | Test for the empty / non-owed state.
  (s -> Bool) ->
  -- | Drain one output from the state, returning the remaining state.
  (s -> Maybe (b, s)) ->
  Mediator s a b ->
  s ->
  [a] ->
  Either LinearityViolation [b]
closeCertifiedWithBy isOwed drain m s0 as =
  let (sFinal, bs) = runMediatorState m s0 as
   in case drainAll sFinal of
        Just bs' -> Right (bs ++ bs')
        Nothing -> Left (LinearityViolation ("close: state not drainable: " ++ show sFinal))
  where
    drainAll s
      | isOwed s = Just []
      | otherwise = case drain s of
          Nothing -> Nothing
          Just (b, s') -> (b :) <$> drainAll s'

-- | Counit of the @?@-comonoid.
--
-- Closing a mediator with no further inputs is allowed only when the state is
-- not owed.  This is the discard law for the exponential: a buffered channel
-- cannot be silently dropped.
medCounit ::
  (Show s) =>
  Mediator s a b ->
  s ->
  Either LinearityViolation [b]
medCounit m s0 = closeCertified m s0 []

-- | Comultiplication of the @?@-comonoid.
--
-- A mediator policy can be duplicated into two independent consumers.  Each
-- copy starts from the same initial residual state, so the duplication is
-- performed on an empty buffer.
medComult :: Mediator s a b -> (Mediator s a b, Mediator s a b)
medComult m = (m, m)

-- | View a mediator as a 'Process' stream transformer.
--
-- A mediator step is Mealy-style: the output depends on the current state
-- /and/ input.  'Process' is Moore-style, so the output carrier is @Maybe b@
-- and the state remembers the output produced by the most recent step.  The
-- seed @s0@ is the initial residual, following the register pattern.
--
-- This is the honest stream cut: the residual state is carried by the
-- process's feedback wire, exactly as 'Process.encode' carries it in a
-- @Loop Either (->) [a] [Maybe b]@.
mediateProcess :: Mediator s a b -> s -> Process a (Maybe b)
mediateProcess med s0 =
  Process.Process
    (\a -> let (s', my) = medStep med s0 a in (s', my))
    (\(s, _) a -> let (s', my) = medStep med s a in (s', my))
    snd

-- | View a mediator as a 'Loop' over input / output lists.
--
-- This is the wrapper collapsed one layer further: the mediator is just a
-- traced state machine iterating over lists.
mediateLoop :: Mediator s a b -> Loop Either (->) [a] [Maybe b]
mediateLoop m = Process.encode (mediateProcess m (medInit m))

-- | Linear mediator: no state is owed, every input is forwarded immediately.
--
-- The state is @()@, so 'close' on a linear composition is yanking with no
-- debt.
linear :: Mediator () a a
linear = Mediator () (\() x -> ((), Just x)) (const False) (\_ _ -> Nothing)

-- | Pair-sum mediator: buffers the first integer, emits the sum on the second.
--
-- State is 'PS'; a held half-pair ('Held') is owed, 'Empty' is not.  The sum
-- is emitted in the same tick that completes the pair.
pairSum :: Mediator PS Int Int
pairSum =
  Mediator
    Empty
    ( \s x -> case s of
        Empty -> (Held x, Nothing)
        Held y -> (Empty, Just (x + y))
    )
    (\case Empty -> False; Held _ -> True)
    (\_ _ -> Nothing)

-- | Count mediator: emits the number of inputs seen so far.
--
-- The counter is state, not residual: nothing is owed at close.  (It can still
-- be flushed with 'closeCertifiedWith' if the caller wants the final value.)
count :: Mediator Int a Int
count = Mediator 0 (\n _ -> let n' = n + 1 in (n', Just n')) (const False) debtDraw

-- | Store an input into the mediator's residual, discarding any emitted
-- output.  This is the left factor on the shared medium.
mediateStoreBody :: Mediator s a b -> (s, a) -> (s, ())
mediateStoreBody med (s, x) =
  let (s', _) = medStep med s x
   in (s', ())

-- | Consume an input together with the current residual, returning whatever
-- the mediator emits.  This is the right factor on the shared medium.
mediateEmitBody :: Mediator s a b -> (s, a) -> (s, Maybe b)
mediateEmitBody med (s, x) = medStep med s x

-- | One step of the mediated composition, with an explicit seed.
--
-- The input pair is @(storedInput, triggerInput)@.  The left factor stores
-- @storedInput@ into the residual; the right factor feeds @triggerInput@
-- together with the updated residual to the mediator step.  The schedule
-- chooses which factor advances; the gated factor's input is discarded.
-- When only one factor advances the output is partial ('This' or 'That');
-- when both advance it is total ('These').
mediateSharedBody ::
  Mediator s a b ->
  Schedule s ->
  (s, (a, a)) ->
  (s, These () (Maybe b))
mediateSharedBody med sched (s, (x, y)) =
  let (s', fire) = chooseS sched s
   in case fire of
        L ->
          let (s'', ()) = mediateStoreBody med (s', x)
           in (s'', This ())
        R ->
          let (s'', mb) = mediateEmitBody med (s', y)
           in (s'', That mb)
        Both LeftFirst ->
          let (s'', ()) = mediateStoreBody med (s', x)
              (s''', mb) = mediateEmitBody med (s'', y)
           in (s''', These () mb)
        Both RightFirst ->
          let (s'', mb) = mediateEmitBody med (s', y)
              (s''', ()) = mediateStoreBody med (s'', x)
           in (s''', These () mb)

-- | Certified variant of 'mediateSharedBody' that checks for overdraw.
--
-- Under the 'Both' schedule the store and emit poles both advance in the same
-- tick.  The mediator's 'medDraw' predicate reports whether that transition
-- consumed more than one unit of resource.
mediateSharedBodyChecked ::
  Mediator s a b ->
  Schedule s ->
  (s, (a, a)) ->
  Either LinearityViolation (s, These () (Maybe b))
mediateSharedBodyChecked med sched (s, xy) =
  let (s', out) = mediateSharedBody med sched (s, xy)
   in case medDraw med s s' of
        Just d -> Left (LinearityViolation ("shared-body overdraw: state debt " ++ show d))
        Nothing -> Right (s', out)

-- | Run a shared-body mediator over a list of input pairs, checking for
-- overdraw at each tick.
runSharedBodyChecked ::
  Mediator s a b ->
  Schedule s ->
  s ->
  [(a, a)] ->
  Either LinearityViolation (s, [Maybe b])
runSharedBodyChecked _ _ s [] = Right (s, [])
runSharedBodyChecked med sched s (xy : xys) =
  case mediateSharedBodyChecked med sched (s, xy) of
    Left e -> Left e
    Right (s', out) -> fmap (\(s'', outs) -> (s'', extractOutput out : outs)) (runSharedBodyChecked med sched s' xys)
  where
    extractOutput :: These () (Maybe b) -> Maybe b
    extractOutput (This ()) = Nothing
    extractOutput (That mb) = mb
    extractOutput (These () mb) = mb
