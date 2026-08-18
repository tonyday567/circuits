{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}

-- | Stateful processes as a 'Circuit' base arrow.
--
-- A 'Process' is a Moore machine packaged as a category morphism:
--
-- @
-- data Process a b = forall s. Process (a -> s) (s -> a -> s) (s -> b)
-- @
--
-- * @inject@ converts the first input into an initial state.
-- * @step@ updates the state given the current input.
-- * @extract@ produces the output from the current state.
--
-- This is the circuits-native carrier for streaming state machines. It is
-- intended to replace the hand-rolled state-machine arrow: stats packages
-- become boxes @Process a b@, while the arrow itself lives in the substrate
-- next to 'Circuit.Loop' and 'Circuit.Net'.
--
-- The semantics are intentionally tied to the circuits substrate:
--
-- * 'scan' is defined as @'run' . 'encode'@, where 'encode' maps the process
--   into a stream-level 'Loop' 'Either' @(->)@ over lists.
-- * A fused @scanl'@ implementation is provided as a fast path, verified by
--   oracle against the 'run' . 'encode' definition.
-- * The arrow-level 'Traced' Either instance is per-tick Conway/Elgot settle,
--   not cross-tick state feedback; see 'register' for the latter.
--
-- = Pointed systems
--
-- The pointed-Moore view of a stateful morphism is 'Circuit.Poly.System' with
-- an explicit seed.  Use 'Circuit.Poly.mooreSystem' to build such a system,
-- and 'systemToProcess' to turn it into a first-input-seeded 'Process'.
module Circuit.Process
  ( -- * Stream transformer (monomial special case)
    Process (..),
    pattern P,

    -- * System <-> Process conversions
    systemToProcess,
    markSystem,

    -- * Runners
    scan,
    fold,
    encode,

    -- * Cross-tick feedback
    delay,
    register,
  )
where

import Circuit.Boundary (Boundary (..))
import Circuit.Category (Category (..), Discrete (..), Ob)
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Dagger (Copy, CopyDiscard, Discard, Merge, MergeZero, Zero)
import Circuit.Dagger qualified as Dagger
import Circuit.Layer (run)
import Circuit.Loop (Loop (..))
import Circuit.Poly (Mono, Pos, System, mooreSystem, runSystem)
import Circuit.Tensor (Action (..), Bias (..), Fire (..), Schedule (..), Shared (..), Tensor (..), chooseS)
import Control.Category qualified as Cat
import Data.Bifunctor (bimap, first, second)
import Data.List (scanl')
import Data.Maybe (fromMaybe)
import Data.Profunctor (Costrong (..), Profunctor (..), Strong (..))
import Data.These (These (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Process
-- >>> import Prelude hiding (id, (.))

-- | A stateful process from @a@ to @b@.
--
-- The existential state type @s@ is hidden; the observable interface is the
-- triple @inject / step / extract@. Keeping the triple as the primitive (rather
-- than fusing @extract@ into the step) preserves the streaming-statistics
-- invariant that the first output is @extract (inject x)@, before any step.
data Process a b where
  Process ::
    forall s a b.
    (a -> s) ->
    (s -> a -> s) ->
    (s -> b) ->
    Process a b

-- | Bidirectional pattern synonym for the Moore triple.
pattern P :: (a -> s) -> (s -> a -> s) -> (s -> b) -> Process a b
pattern P i st ex = Process i st ex

{-# COMPLETE P #-}

-- | Convert a monomial 'System', an explicit seed, and a state observation
-- into a first-input-seeded 'Process'.
--
-- The observation @s -> b@ is applied to the /current/ state to produce each
-- output, including the first output from the seed.  The step system is used
-- only for state transitions.
systemToProcess :: s -> (s -> b) -> System (->) s (Mono a b) -> Process a b
systemToProcess s0 ex sys =
  Process
    (\a -> fst (runSystem sys (s0, Right a)))
    (\s a -> fst (runSystem sys (s, Right a)))
    ex

-- | Lift a monomial 'System' and a state observation into a boundary system
-- over 'Boundary' tokens.
--
-- Payloads are stepped through the inner system.  Marks satisfying the halt
-- predicate freeze the system and produce 'Nothing' thereafter; non-halt
-- marks leave the state unchanged and emit the current output.  The halted
-- state remembers the final inner state.
--
-- The returned system carries state @Either s s@: 'Left' is running, 'Right'
-- is halted.  This is the core combinator behind mark-driven halt: the finite
-- mark alphabet @k@ carries control tokens, while payloads carry data.
markSystem ::
  (k -> Bool) ->
  (s -> b) ->
  System (->) s (Mono a b) ->
  System (->) (Either s s) (Mono (Boundary k a) (Maybe b))
markSystem isHalt ex sys =
  mooreSystem
    ( \s tok -> case (s, tok) of
        (Left s', Payload a) -> Left (fst (runSystem sys (s', Right a)))
        (Left s', Mark k) -> if isHalt k then Right s' else Left s'
        (Right s', _) -> Right s'
    )
    ( \case
        Left s -> Just (ex s)
        Right _ -> Nothing
    )

-- | Strict pair, reused from the original mealy package for fused composition.
data Pair' a b = Pair' !a !b
  deriving (Eq, Ord, Show, Read)

instance (Semigroup a, Semigroup b) => Semigroup (Pair' a b) where
  Pair' a b <> Pair' c d = Pair' (a <> c) (b <> d)
  {-# INLINE (<>) #-}

instance (Monoid a, Monoid b) => Monoid (Pair' a b) where
  mempty = Pair' mempty mempty

-- ---------------------------------------------------------------------------
-- Functor / Applicative
-- ---------------------------------------------------------------------------

instance Functor (Process a) where
  fmap f (P i st ex) = P i st (f . ex)
  {-# INLINE fmap #-}

instance Applicative (Process a) where
  pure b = P (const ()) (\() _ -> ()) (\() -> b)
  {-# INLINE pure #-}

  P i1 st1 ex1 <*> P i2 st2 ex2 =
    P
      (\a -> Pair' (i1 a) (i2 a))
      (\(Pair' s1 s2) a -> Pair' (st1 s1 a) (st2 s2 a))
      (\(Pair' s1 s2) -> ex1 s1 (ex2 s2))
  {-# INLINE (<*>) #-}

-- ---------------------------------------------------------------------------
-- Category
-- ---------------------------------------------------------------------------

instance Category Process where
  type Ob Process a = ()

  id :: Process a a
  id = P id const id
  {-# INLINE id #-}

  (.) :: Process b c -> Process a b -> Process a c
  P i2 st2 ex2 . P i1 st1 ex1 =
    P
      (\a -> let s1 = i1 a in Pair' s1 (i2 (ex1 s1)))
      ( \(Pair' s1 s2) a ->
          let s1' = st1 s1 a
              s2' = st2 s2 (ex1 s1')
           in Pair' s1' s2'
      )
      (\(Pair' _ s2) -> ex2 s2)
  {-# INLINE (.) #-}

-- | Backwards-compatible 'Control.Category' instance.
--
-- This is a migration aid for code that still uses @(>>>)@ and the rest of
-- the standard arrow vocabulary. New circuits-native code should prefer the
-- 'Circuit.Category' methods.
instance Cat.Category Process where
  id = id
  (.) = (.)

-- | @Process@ has trivial object constraints, so it is discrete.
instance Discrete Process where
  withOb x = x

-- ---------------------------------------------------------------------------
-- Profunctor
-- ---------------------------------------------------------------------------

instance Profunctor Process where
  dimap f g (P i st ex) = P (i . f) (\s -> st s . f) (g . ex)
  {-# INLINE dimap #-}

  lmap f (P i st ex) = P (i . f) (\s -> st s . f) ex
  {-# INLINE lmap #-}

  rmap g (P i st ex) = P i st (g . ex)
  {-# INLINE rmap #-}

-- ---------------------------------------------------------------------------
-- Strong / Costrong (profunctors layer)
-- ---------------------------------------------------------------------------

-- | Cartesian strength from the 'profunctors' package.
--
-- 'first'' puts the active wire on the left; 'second'' puts it on the right.
-- Both are derivable from the circuits 'Strength (,) Process' instance.
instance Strong Process where
  first' p = dimap sw sw (strength p)
    where
      sw (a, b) = (b, a)
  {-# INLINE first' #-}
  second' = strength
  {-# INLINE second' #-}

-- | Costrength: closed feedback over the cartesian tensor.
--
-- 'unfirst' and 'unsecond' are exactly the cartesian 'trace' after swapping
-- the active wire into / out of the feedback position.
instance Costrong Process where
  unfirst p = trace (dimap sw sw p)
    where
      sw (a, b) = (b, a)
  {-# INLINE unfirst #-}
  unsecond = trace
  {-# INLINE unsecond #-}

-- ---------------------------------------------------------------------------
-- Channel / Strength / Traced for (,)
--
-- These instances make Process a traced monoidal category under the cartesian
-- tensor. The trace ties a lazy self-referential knot and is productive only
-- when the body is non-strict in the feedback channel. Strict accumulators
-- (e.g. moving averages) diverge under the (,) trace; use Either-trace 'run'
-- or the 'register' combinator for those.
-- ---------------------------------------------------------------------------

instance Channel (,) Process where
  assoc = P id (\_ x -> x) (\(~((a, b), c)) -> (a, (b, c)))
  assoc' = P id (\_ x -> x) (\(a, ~(b, c)) -> ((a, b), c))
  slide = P id (\_ x -> x) (\(a, ~(b, c)) -> (b, (a, c)))

instance Strength (,) Process where
  strength (P i st ex) =
    P
      (\(~(a, b)) -> (a, i b))
      (\(~(_, s)) (~(a', b)) -> (a', st s b))
      (\(~(a, s)) -> (a, ex s))

instance Traced (,) Process where
  trace (P i st ex) =
    P
      (\b -> let s0 = i (a0, b); a0 = fst (ex s0) in s0)
      ( \s b ->
          let (s', _a) = fix (\ ~(s'', a') -> (st s (a', b), fst (ex s'')))
           in s'
      )
      (snd . ex)
    where
      fix f = let x = f x in x

-- ---------------------------------------------------------------------------
-- Tensor / Action / Shared for (,)
--
-- These instances make @Process@ a cartesian monoidal category in its own
-- right, so it can serve as a base category for shared-medium fusion and
-- for @Loop (,) Process@.
-- ---------------------------------------------------------------------------

instance Tensor (,) Process where
  par (P i1 st1 ex1) (P i2 st2 ex2) =
    P
      (bimap i1 i2)
      (\(s1, s2) (a, c) -> (st1 s1 a, st2 s2 c))
      (bimap ex1 ex2)
  {-# INLINE par #-}

  unitl = P snd (\_ (_, a) -> a) id
  unitl' = P id const ((),)
  unitr = P fst (\_ (a, ()) -> a) id
  unitr' = P id const (,())

instance Action (,) Process where
  swap = P id (const id) sw
    where
      sw (a, b) = (b, a)
  {-# INLINE swap #-}

-- | Cartesian shared fusion on processes.
--
-- The two processes share one feedback channel @s@. At each tick the schedule
-- chooses which body advances; the gated body's input is discarded and it does
-- not step. Each process is injected lazily on its first firing, so a body that
-- is never scheduled consumes no inputs and produces no outputs.
instance Shared (,) Process where
  sharedBy sched (P iL stL exL) (P iR stR exR) =
    P inject step extract
    where
      inject (s, (a, c)) =
        let (s', fire) = chooseS sched s
         in runInject fire s' a c

      step (msL, msR, _, _) (sIn, (a, c)) =
        let (s', fire) = chooseS sched sIn
         in runStep fire msL msR s' a c

      extract (_, _, s, out) = (s, out)

      runInject fire s' a c = case fire of
        L ->
          let sL0 = iL (s', a)
              (s'', b) = exL sL0
           in (Just sL0, Nothing, s'', This b)
        R ->
          let sR0 = iR (s', c)
              (s'', d) = exR sR0
           in (Nothing, Just sR0, s'', That d)
        Both LeftFirst ->
          let sL0 = iL (s', a)
              (sMid, b) = exL sL0
              sR0 = iR (sMid, c)
              (sOut, d) = exR sR0
           in (Just sL0, Just sR0, sOut, These b d)
        Both RightFirst ->
          let sR0 = iR (s', c)
              (sMid, d) = exR sR0
              sL0 = iL (sMid, a)
              (sOut, b) = exL sL0
           in (Just sL0, Just sR0, sOut, These b d)

      runStep fire msL msR s' a c = case fire of
        L ->
          let sL = fromMaybe (iL (s', a)) msL
              sL' = stL sL (s', a)
              (s'', b) = exL sL'
           in (Just sL', msR, s'', This b)
        R ->
          let sR = fromMaybe (iR (s', c)) msR
              sR' = stR sR (s', c)
              (s'', d) = exR sR'
           in (msL, Just sR', s'', That d)
        Both LeftFirst ->
          let sL = fromMaybe (iL (s', a)) msL
              sL' = stL sL (s', a)
              (s'', b) = exL sL'
              sR = fromMaybe (iR (s'', c)) msR
              sR' = stR sR (s'', c)
              (s''', d) = exR sR'
           in (Just sL', Just sR', s''', These b d)
        Both RightFirst ->
          let sR = fromMaybe (iR (s', c)) msR
              sR' = stR sR (s', c)
              (s'', d) = exR sR'
              sL = fromMaybe (iL (s'', a)) msL
              sL' = stL sL (s'', a)
              (s''', b) = exL sL'
           in (Just sL', Just sR', s''', These b d)
  {-# INLINE sharedBy #-}

-- ---------------------------------------------------------------------------
-- Channel / Strength / Traced for Either
--
-- These instances make Process a traced monoidal category under the Either
-- tensor. The trace is per-tick Conway/Elgot settle: Right injects a value,
-- Left feeds intermediate state back within the same tick until Right exits.
-- This is the instance required by 'Net Either Process' knot bodies.
-- ---------------------------------------------------------------------------

instance Channel Either Process where
  assoc = P id (\_ x -> x) assocEither
    where
      assocEither (Left (Left a)) = Left a
      assocEither (Left (Right b)) = Right (Left b)
      assocEither (Right c) = Right (Right c)
  assoc' = P id (\_ x -> x) assocEither'
    where
      assocEither' (Left a) = Left (Left a)
      assocEither' (Right (Left b)) = Left (Right b)
      assocEither' (Right (Right c)) = Right c
  slide = P id (\_ x -> x) slideEither
    where
      slideEither (Left a) = Right (Left a)
      slideEither (Right (Left b)) = Left b
      slideEither (Right (Right c)) = Right (Right c)

instance Strength Either Process where
  strength (P i st ex) =
    P
      (\case Left a -> (Nothing, Left a); Right b -> let s0 = i b in (Just s0, Right (ex s0)))
      ( \(ms, _) -> \case
          Left a -> (ms, Left a)
          Right b -> case ms of
            Nothing -> let s0 = i b in (Just s0, Right (ex s0))
            Just s -> let s' = st s b in (Just s', Right (ex s'))
      )
      snd

instance Traced Either Process where
  trace (P i st ex) = P i' st' ex'
    where
      settle m = case ex m of
        Left s -> settle (st m (Left s))
        Right _ -> m

      i' a = settle (i (Right a))
      st' m a = settle (st m (Right a))
      ex' m = case ex m of
        Right b -> b
        Left _ -> error "Circuit.Process.Traced Either: unsettled state"

-- ---------------------------------------------------------------------------
-- Bimonoid instances (pointwise lift)
-- ---------------------------------------------------------------------------

instance (Copy (->) a) => Copy Process a where
  copy = P id (\_ x -> x) Dagger.copy

instance (Discard (->) a) => Discard Process a where
  discard = P id (\_ x -> x) (const ())

instance (Merge (->) a) => Merge Process a where
  plus = P id (\_ x -> x) Dagger.plus

instance (Zero (->) a) => Zero Process a where
  zero = P id (\_ x -> x) Dagger.zero

-- ---------------------------------------------------------------------------
-- Runners
-- ---------------------------------------------------------------------------

-- | Encode a 'Process' as a stream-level 'Loop Either (->)' over lists.
--
-- This is the definitional runner: 'scan' is 'run' composed with 'encode'.
-- The feedback channel carries @(state, remaining input, accumulated output)@.
encode :: Process a b -> Loop Either (->) [a] [b]
encode (P i st ex) = Knot body
  where
    body (Right []) = Right []
    body (Right (a : as)) =
      let s0 = i a
       in Left (s0, as, [ex s0])
    body (Left (_, [], bs)) = Right (reverse bs)
    body (Left (s, a : as, bs)) =
      let s' = st s a
       in Left (s', as, ex s' : bs)

-- | Run a process over a list, returning the output at each step.
--
-- Law: @scan p xs == 'run' ('encode' p) xs@.
scan :: Process a b -> [a] -> [b]
scan _ [] = []
scan (P i st ex) (x : xs) =
  let s0 = i x
   in ex <$> scanl' st s0 xs

-- | Run a process over a list, returning the final output (if any).
fold :: Process a b -> [a] -> Maybe b
fold _ [] = Nothing
fold p xs = Just (last (scan p xs))

-- ---------------------------------------------------------------------------
-- Cross-tick feedback
-- ---------------------------------------------------------------------------

-- | One-tick delay with an initial value.
--
-- Output is @s0@ on the first tick and the input from the previous tick
-- thereafter. This is the primitive that makes 'register' productive: the
-- feedback wire is observable one tick late.
delay :: s -> Process s s
delay s0 = P (const s0) (const id) id

-- | Cross-tick register feedback.
--
-- Given an initial feedback value @s0@ and a process @Process (a, s) (b, s)@,
-- close the @s@ wire so that the @s@ produced at one tick is fed back as
-- input at the next tick. This is the productive, strict-accumulator-safe
-- analogue of the cartesian trace: the delay is explicit in the wiring
-- rather than implicit in a lazy knot.
--
-- Compare with the cartesian 'trace' on 'Process', which ties a lazy knot
-- and diverges for strict state; 'register' keeps strict state cells sound
-- by making the one-tick delay observable.
--
-- For bodies whose fixed-point is independent of the initial feedback value
-- (e.g. affine/stateless feedback such as 'ewmaBody'), the same wiring can
-- be expressed using 'delay', 'strength' and 'trace':
--
-- @register s0 body == trace (dimap swap swap (body . strength (delay s0)))@,
-- where @swap (a, b) = (b, a)@.
register :: s -> Process (a, s) (b, s) -> Process a b
register s0 (P i st ex) = P i' st' ex'
  where
    i' a = i (a, s0)
    st' s a = st s (a, snd (ex s))
    ex' s = fst (ex s)
