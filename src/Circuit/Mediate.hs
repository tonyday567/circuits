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
  )
where

import Circuit.Loop (Loop)
import Circuit.Process (Process, scan)
import Circuit.Process qualified as Process
import Circuit.Tensor (Bias (..), Fire (..), Schedule (..), chooseS)
import Data.List (mapAccumL, uncons)
import Data.Maybe (catMaybes, isNothing)
import Data.These (These (..))

-- | A mediator with residual state @s@, input @a@, output @b@.
--
-- The step function consumes one input and updates the residual state. It may
-- emit zero or one output. A 'Nothing' output means the mediator is still
-- accumulating residual state.
--
-- This record is a thin wrapper: the canonical stream view is obtained via
-- 'mediateProcess'.
data Mediator s a b = Mediator
  { -- | Initial residual state.
    medInit :: s,
    -- | Consume one input, update residual state, optionally emit output.
    medStep :: s -> a -> (s, Maybe b)
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

-- | Types whose residual state has a canonical empty value. A 'closeCertified'
-- run asserts that the mediator's residual has returned to this value.
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

-- | A violation reported when a certified close finds the residual state is not
-- empty.
newtype LinearityViolation = LinearityViolation String
  deriving (Eq, Show)

-- | Run a mediator over a stream and certify that the residual is empty at
-- close.
--
-- If the final residual state is 'emptyResidual', return the emitted outputs.
-- Otherwise report a 'LinearityViolation' carrying the offending residual.
--
-- This is the /strict/ close semantics: a residual is a violation even if it
-- could be flushed into output.  For flushable residuals use
-- 'closeCertifiedWith'.
closeCertified :: (LinearResidual s, Show s) => Mediator s a b -> s -> [a] -> Either LinearityViolation [b]
closeCertified m s0 as =
  let (sFinal, bs) = runMediatorState m s0 as
   in if isEmptyResidual sFinal
        then Right bs
        else Left (LinearityViolation ("close: residual not empty: " ++ show sFinal))

-- | Run a mediator over a stream and certify that any remaining residual can
-- be drained according to its 'FlushableResidual' instance.
--
-- This is the flush semantics: a residual is a violation only when 'flushStep'
-- cannot drain it.  'count' flushes its accumulated value once; a list
-- residual flushes head-first; a 'Ready' sum flushes; a 'Held' half-pair
-- reports a violation.
closeCertifiedWith ::
  (FlushableResidual s b, Show s) =>
  Mediator s a b ->
  s ->
  [a] ->
  Either LinearityViolation [b]
closeCertifiedWith = closeCertifiedWithBy isEmptyResidual flushStep

-- | Run a mediator over a stream and certify that any remaining residual can
-- be drained via explicit empty/drain functions.
--
-- This is the escape hatch for custom residual policies that do not have a
-- 'FlushableResidual' instance.
closeCertifiedWithBy ::
  (Show s) =>
  -- | Test for the empty residual.
  (s -> Bool) ->
  -- | Drain one output from the residual, returning the remaining residual.
  (s -> Maybe (b, s)) ->
  Mediator s a b ->
  s ->
  [a] ->
  Either LinearityViolation [b]
closeCertifiedWithBy isEmpty drain m s0 as =
  let (sFinal, bs) = runMediatorState m s0 as
   in case drainAll sFinal of
        Just bs' -> Right (bs ++ bs')
        Nothing -> Left (LinearityViolation ("close: residual not drainable: " ++ show sFinal))
  where
    drainAll s
      | isEmpty s = Just []
      | otherwise = case drain s of
          Nothing -> Nothing
          Just (b, s') -> (b :) <$> drainAll s'

-- | Counit of the @?@-comonoid.
--
-- Closing a mediator with no further inputs is allowed only when the residual
-- state is already empty.  This is the discard law for the exponential:
-- a buffered channel cannot be silently dropped.
medCounit ::
  (LinearResidual s, Show s) =>
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

-- | Linear mediator: no residual, every input is forwarded immediately.
--
-- The residual state is @()@, so 'close' on a linear composition is yanking
-- with an empty residual.
linear :: Mediator () a a
linear = Mediator () $ \() x -> ((), Just x)

-- | Pair-sum mediator: buffers the first integer, emits the sum on the second.
--
-- Residual state is 'PS' so that a held half-pair ('Held') is a genuine
-- linearity violation on close.  The sum is emitted in the same tick that
-- completes the pair.
pairSum :: Mediator PS Int Int
pairSum =
  Mediator Empty $ \s x -> case s of
    Empty -> (Held x, Nothing)
    Held y -> (Empty, Just (x + y))

-- | Count mediator: emits the number of inputs seen so far.
--
-- A simple non-linear mediator with accumulating residual state.
count :: Mediator Int a Int
count = Mediator 0 $ \n _ -> let n' = n + 1 in (n', Just n')

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
