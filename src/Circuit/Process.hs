{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

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
-- = Polymorphic generalisation
--
-- The polymorphic counterpart is 'Machine' @arr p@: a Moore coalgebra over an
-- arbitrary base arrow @arr@ and polynomial interface @p@.  'Process' @a b@
-- is isomorphic to @Machine (->) (Mono a b)@ via 'processToMachine' and
-- 'machineToProcess'; the two views round-trip exactly.
module Circuit.Process
  ( -- * Stream transformer (monomial special case)
    Process (..),
    data P,

    -- * Polymorphic process carrier
    Machine (..),
    processToMachine,
    machineToProcess,
    step0,

    -- * Runners
    scan,
    fold,
    encode,

    -- * Cross-tick feedback
    register,
  )
where

import Circuit.Category (Category (..), ObDict (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Dagger (CopyDiscard, MergeZero)
import qualified Circuit.Dagger as Dagger
import Circuit.Layer (run)
import Circuit.Loop (Loop (..))
import Circuit.Poly (Dir, Mono, Pos, System (..))
import Control.Category qualified as Cat
import Data.Bifunctor (first, second)
import Data.List (scanl')
import Data.Profunctor (Costrong (..), Profunctor (..), Strong (..))
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

-- | A Moore machine over base arrow @arr@ and polynomial interface @p@.
--
-- The existential state type @s@ is hidden; the observable interface is the
-- coalgebra consisting of an initial-state injector, a state-to-position
-- observation, and a step system.  For the monomial special case
-- @Machine (->) (Mono a b)@ this collapses to the classic Moore triple
-- @(inject, step, extract)@ carried by 'Process'.
data Machine arr p where
  Machine ::
    forall arr s p.
    (Ob arr s, Ob arr (Dir p), Ob arr (Pos p)) =>
    -- | Inject the first direction into an initial state.
    arr (Dir p) s ->
    -- | Observe the current position from the current state.
    arr s (Pos p) ->
    -- | Step the state and produce the current position.
    System arr s p ->
    Machine arr p

-- ---------------------------------------------------------------------------
-- Process <-> Machine isomorphism
-- ---------------------------------------------------------------------------

-- | Convert a monomial direction into the underlying input.
dirToA :: Dir (Mono a b) -> a
dirToA (Left v) = absurd v
dirToA (Right a) = a

-- | Inject an input into a monomial direction.
aToDir :: a -> Dir (Mono a b)
aToDir = Right

-- | Project a monomial position onto the underlying output.
posToB :: Pos (Mono a b) -> b
posToB = fst

-- | Inject an output into a monomial position.
bToPos :: b -> Pos (Mono a b)
bToPos b = (b, ())

-- | Convert a classic 'Process' triple into a monomial 'Machine'.
processToMachine :: Process a b -> Machine (->) (Mono a b)
processToMachine (P i st ex) =
  Machine
    (i . dirToA)
    (bToPos . ex)
    ( System $ \case
        (_, Left v) -> absurd v
        (s, Right a) ->
          let s' = st s a
           in (s', (ex s', ()))
    )

-- | Convert a monomial 'Machine' back into a classic 'Process' triple.
machineToProcess :: Machine (->) (Mono a b) -> Process a b
machineToProcess (Machine i ex (System sys)) =
  Process
    (i . aToDir)
    (\s a -> fst (sys (s, Right a)))
    (posToB . ex)

-- | First-step observation: the position produced from the initial state,
-- before any transition.
--
-- For a monomial stream transformer this is the first output emitted by
-- 'scan'.
step0 :: (Category arr) => Machine arr p -> arr (Dir p) (Pos p)
step0 (Machine inject extract _) = extract . inject

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
  id = P id (\s _ -> s) id
  {-# INLINE id #-}

  (.) :: Process b c -> Process a b -> Process a c
  P i2 st2 ex2 . P i1 st1 ex1 =
    P
      (\a -> let s1 = i1 a in Pair' s1 (i2 (ex1 s1)))
      (\(Pair' s1 s2) a ->
         let s1' = st1 s1 a
             s2' = st2 s2 (ex1 s1')
          in Pair' s1' s2')
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
  first' p = dimap swap swap (strength p)
    where
      swap (a, b) = (b, a)
  {-# INLINE first' #-}
  second' = strength
  {-# INLINE second' #-}

-- | Costrength: closed feedback over the cartesian tensor.
--
-- 'unfirst' and 'unsecond' are exactly the cartesian 'trace' after swapping
-- the active wire into / out of the feedback position.
instance Costrong Process where
  unfirst p = trace (dimap swap swap p)
    where
      swap (a, b) = (b, a)
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
  withTensorOb ObDict ObDict x = x

instance Strength (,) Process where
  strength (P i st ex) =
    P
      (\(~(a, b)) -> (a, i b))
      (\(~(_, s)) (~(a', b)) -> (a', st s b))
      (\(~(a, s)) -> (a, ex s))
  withStrengthOb ObDict ObDict ObDict x = x

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
  withTensorOb ObDict ObDict x = x

instance Strength Either Process where
  strength (P i st ex) =
    P
      (\case Left a -> (Nothing, Left a); Right b -> let s0 = i b in (Just s0, Right (ex s0)))
      (\(ms, _) -> \case
         Left a -> (ms, Left a)
         Right b -> case ms of
           Nothing -> let s0 = i b in (Just s0, Right (ex s0))
           Just s -> let s' = st s b in (Just s', Right (ex s')))
      (\(_, e) -> e)
  withStrengthOb ObDict ObDict ObDict x = x

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

instance CopyDiscard Process a where
  copy = P id (\_ x -> x) Dagger.copy
  discard = P id (\_ x -> x) (const ())

instance MergeZero (->) a => MergeZero Process a where
  plus = P id (\_ x -> x) Dagger.plus
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
register :: s -> Process (a, s) (b, s) -> Process a b
register s0 (P i st ex) = P i' st' ex'
  where
    i' a = i (a, s0)
    st' s a = st s (a, snd (ex s))
    ex' s = fst (ex s)
