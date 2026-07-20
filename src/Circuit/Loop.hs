{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The free traced monoidal category, in existential normal form.
--
-- @Loop t arr a b@ is the free traced monoidal category over a base
-- morphism @arr@ with tensor @t@. The two constructors encode:
--
--   * 'Lift' — a plain base arrow.
--   * 'Knot' — a feedback loop with a hidden feedback channel.
--
-- The laws of traced monoidal categories are performed by the 'Category'
-- and 'Traced' instances, so every value is already in normal form: at most
-- one 'Knot' at the top, over a base-arrow body.
--
-- For example, a @Loop (,) (->)@ is the initial traced monoidal cartesian
-- category over Haskell functions.
--
-- = Introduce / resolve
--
-- The vocabulary in this module follows the introduce/resolve pattern:
--
--   * 'Knot' introduces feedback; 'trace' resolves it. This is the gold
--     type-changing pair; composition fuses 'Knot's.
--
-- The polar channel ends ('Out', 'In'), their counit ('close'), and
-- their unit ('open') all live in "Circuit.Ends".
--
-- == Interpreting a 'Loop'
--
-- Use 'run' or 'bind' to interpret a 'Loop' into a target category.  The
-- 'Category' and 'Traced' instances of the target discharge the knot; for
-- @(->)@ this is lazy knot-tying, and for 'Either' it is iteration.
--
-- == Core Concepts
--
-- * __Tensor__ (@t@): The bifunctor that pairs a feedback value with a payload.
--   The two tensors provided are @(,)@ (simultaneous / lazy sharing) and
--   'Either' (sequential / iteration).
--
-- * __Feedback value__: The component that travels around the loop (the first
--   parameter of the tensor inside a 'Knot' body).
--
-- * __Payload__: The component that is transformed and emitted (the second
--   parameter of the tensor inside a 'Knot' body).
--
-- * __Feedback channel__: The hidden type @s@ in a 'Knot'. It is the value
--   the abstraction hides.
module Circuit.Loop
  ( -- * Loop
    Loop (..),

    -- * Stateful IO stages
    cellIO,

    -- * Layer witness
    FreeLoop,
  )
where

import Circuit.Category (Category (..), Discrete (..), (>>>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Layer (Layer (..), run, (:~>))
import Control.Arrow (Kleisli (..))
import Data.Bifunctor (Bifunctor (..))
import Data.IORef
import Data.Kind (Type)
import Data.Profunctor
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Tensor (Tensor (..))
-- >>> import Control.Arrow (Kleisli (..))
-- >>> import Circuit.Category ((.), (>>>))
-- >>> import Data.Void (Void)
-- >>> import Prelude hiding (id, (.))

-- | The free traced monoidal category over base morphism @arr@ and tensor @t@,
-- in existential normal form.
--
-- Two constructors:
--
--   * 'Lift' — a plain base arrow.
--   * 'Knot' — a feedback loop with hidden channel @s@.
data Loop (t :: Type -> Type -> Type) arr a b where
  -- | A plain base arrow.
  --
  -- >>> run (Lift (+1) :: Loop (,) (->) Int Int) 5
  -- 6
  Lift :: arr a b -> Loop t arr a b
  -- | Tie a feedback loop. The tensor @t@ carries the hidden channel type @s@.
  --
  -- The argument is the base arrow itself, /not/ a 'Lift'-wrapped stage:
  --
  -- >>> run (Knot (\(acc, x) -> (x, acc)) :: Loop (,) (->) Int Int) 42
  -- 42
  --
  -- For the @(,)@ tensor the channel value is self-referential, so the body
  -- must use an irrefutable pattern or otherwise avoid forcing the channel
  -- before producing its constructor:
  --
  -- >>> run (Knot (\ ~(ns, ()) -> (0 : ns, take 3 ns)) :: Loop (,) (->) () [Int]) ()
  -- [0,0,0]
  --
  -- The constructor carries the 'Ob' evidence for the feedback channel in
  -- the /source/ category.  Folding into a different target still needs
  -- 'Discrete' to manufacture the corresponding 'Ob' evidence there.
  Knot :: Ob arr s => arr (t s a) (t s b) -> Loop t arr a b

instance (Strength t arr, Discrete arr) => Category (Loop t arr) where
  type Ob (Loop t arr) a = Ob arr a
  id :: forall a. (Ob arr a) => Loop t arr a a
  id = Lift id
  (.) :: forall a b c. (Ob arr a, Ob arr b, Ob arr c) => Loop t arr b c -> Loop t arr a b -> Loop t arr a c
  Lift f . Lift g = Lift (f . g)
  Knot @_ @s @_ @_ @_ f . Lift g =
    withOb @arr @(t s a) $
      withOb @arr @(t s b) $
        withOb @arr @(t s c) $
          Knot (f . strength g)
  Lift f . Knot @_ @s @_ @_ @_ g =
    withOb @arr @(t s a) $
      withOb @arr @(t s b) $
        withOb @arr @(t s c) $
          Knot (strength f . g)
  Knot @_ @s2 @_ @_ @_ f . Knot @_ @s1 @_ @_ @_ g =
    withOb @arr @(t s2 s1) $
      withOb @arr @(t (t s2 s1) a) $
        withOb @arr @(t s2 (t s1 a)) $
          withOb @arr @(t s2 (t s1 b)) $
            withOb @arr @(t s2 (t s1 c)) $
              withOb @arr @(t s1 a) $
                withOb @arr @(t s1 b) $
                  withOb @arr @(t s1 (t s2 b)) $
                    withOb @arr @(t s2 b) $
                      withOb @arr @(t s2 c) $
                        withOb @arr @(t s1 (t s2 c)) $
                          withOb @arr @(t (t s2 s1) c) $
                            Knot (assoc >>> strength g >>> slide >>> strength f >>> slide >>> assoc')

-- | A discrete base yields a discrete free traced category.
instance (Strength t arr, Discrete arr) => Discrete (Loop t arr) where
  withOb @a x = withOb @arr @a x

instance (Profunctor arr, Bifunctor t) => Profunctor (Loop t arr) where
  dimap f g (Lift h) = Lift (dimap f g h)
  dimap f g (Knot h) = Knot (dimap (second f) (second g) h)
  lmap f (Lift h) = Lift (lmap f h)
  lmap f (Knot h) = Knot (lmap (second f) h)
  rmap g (Lift h) = Lift (rmap g h)
  rmap g (Knot h) = Knot (rmap (second g) h)

instance (Bifunctor t) => Functor (Loop t (->) a) where
  fmap f (Lift g) = Lift (f . g)
  fmap f (Knot g) = Knot (second f . g)

-- | Lift the 'Channel' structure of the base arrow into 'Loop t arr'.
--
-- The 'withOb' ladder is written out inline rather than using
-- 'Circuit.Discrete.assocD' / 'slideD' because importing that kit here would
-- create a cycle: 'Circuit.Discrete' needs 'Traced' (and hence this module).
instance (Strength t arr, Discrete arr) => Channel t (Loop t arr) where
  assoc :: forall a b c. Loop t arr (t (t a b) c) (t a (t b c))
  assoc =
    Lift $
      withOb @arr @a $
        withOb @arr @b $
          withOb @arr @c $
            withOb @arr @(t a b) $
              withOb @arr @(t b c) $
                withOb @arr @(t (t a b) c) $
                  withOb @arr @(t a (t b c)) $
                    assoc
  assoc' :: forall a b c. Loop t arr (t a (t b c)) (t (t a b) c)
  assoc' =
    Lift $
      withOb @arr @a $
        withOb @arr @b $
          withOb @arr @c $
            withOb @arr @(t a b) $
              withOb @arr @(t b c) $
                withOb @arr @(t a (t b c)) $
                  withOb @arr @(t (t a b) c) $
                    assoc'
  slide :: forall a b c. Loop t arr (t a (t b c)) (t b (t a c))
  slide =
    Lift $
      withOb @arr @a $
        withOb @arr @b $
          withOb @arr @c $
            withOb @arr @(t b c) $
              withOb @arr @(t a c) $
                withOb @arr @(t a (t b c)) $
                  withOb @arr @(t b (t a c)) $
                    slide

-- | Lift the 'Strength' class through 'Loop t'.
instance (Strength t arr, Discrete arr) => Strength t (Loop t arr) where
  strength :: forall a b c. (Ob arr a, Ob arr b, Ob arr c, Ob arr (t a b), Ob arr (t a c)) => Loop t arr b c -> Loop t arr (t a b) (t a c)
  strength (Lift f) =
    Lift $
      withOb @arr @a $
        withOb @arr @b $
          withOb @arr @c $
            withOb @arr @(t a b) $
              withOb @arr @(t a c) $
                strength f
  strength (Knot @_ @s @_ @_ @_ f) =
    withOb @arr @(t s (t a b)) $
      withOb @arr @(t a (t s b)) $
        withOb @arr @(t a (t s c)) $
      withOb @arr @(t s b) $
        withOb @arr @(t s c) $
          withOb @arr @(t s (t a c)) $
            Knot (slide >>> strength f >>> slide)

-- | Lift the 'Traced' class through 'Loop t'.
--
-- 'trace' hides a wire as a 'Knot'.
instance (Traced t arr, Discrete arr) => Traced t (Loop t arr) where
  trace ::
    forall a b c.
    (Ob arr a) =>
    Loop t arr (t a b) (t a c) ->
    Loop t arr b c
  trace (Lift f) = Knot f
  trace (Knot @_ @s @_ @_ @_ f) =
    withOb @arr @(t (t s a) b) $
      withOb @arr @(t s (t a b)) $
        withOb @arr @(t s (t a c)) $
          withOb @arr @(t (t s a) c) $
            withOb @arr @(t s a) $
              Knot (assoc >>> f >>> assoc')

-- * Stateful stages via IORef

-- | Create a stateful 'Kleisli' 'IO' arrow backed by 'IORef'.
--
-- Allocates a mutable reference once, then each invocation reads the
-- current state, applies the transfer function, writes the new state
-- back, and returns the output. The 'IORef' is hidden inside the
-- arrow — callers see a pure @Kleisli IO a b@.
--
-- This breaks the circular dependency that 'MonadFix' requires for
-- the 'Traced' @(,)@ instance: the feedback value is stored in the
-- mutable cell rather than being self-referential. Strict accumulators
-- (counters, frequency tables, running sums) work without diverging.
--
-- >>> acc <- cellIO (0 :: Int) (\s a -> let s' = s + a in pure (s', s'))
-- >>> runKleisli acc 5
-- 5
-- >>> runKleisli acc 3
-- 8
-- >>> runKleisli acc 2
-- 10
cellIO ::
  -- | initial state
  s ->
  -- | transfer: current state and input yield next state and output
  (s -> a -> IO (s, b)) ->
  IO (Kleisli IO a b)
cellIO s0 step = do
  ref <- newIORef s0
  pure $
    Kleisli $ \a -> do
      s <- readIORef ref
      (s', b) <- step s a
      writeIORef ref s'
      pure b

-- | 'Traced' plus 'Discrete' — required to fold free 'Loop'
-- (existential feedback channels need trivial 'Ob' on every type).
class (Traced t arr, Discrete arr) => FreeLoop t arr

instance (Traced t arr, Discrete arr) => FreeLoop t arr

-- | Free traced monoidal category.
instance Layer (Loop t) where
  type Law (Loop t) arr' = FreeLoop t arr'
  type Run (Loop t) arr = (Traced t arr, Discrete arr)
  type Bind (Loop t) arr = ()
  unit = Lift
  run :: forall arr a b. (Run (Loop t) arr, Ob arr a, Ob arr b) => Loop t arr a b -> arr a b
  run (Lift f) = f
  run (Knot @_ @s @_ @_ @_ f) =
    withOb @arr @(t s a) $
      withOb @arr @(t s b) $
        trace f
  bind :: forall arr arr' a b. (Law (Loop t) arr', Ob arr' a, Ob arr' b) => (arr :~> arr') -> Loop t arr a b -> arr' a b
  bind h (Lift f) = h f
  bind h (Knot @_ @s @_ @_ @_ f) =
    withOb @arr' @s $
      withOb @arr' @(t s a) $
        withOb @arr' @(t s b) $
          trace (h f)
