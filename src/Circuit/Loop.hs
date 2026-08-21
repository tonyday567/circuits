{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The free traced monoidal category, in existential normal form.
--
-- @Loop t arr a b@ is the free traced monoidal category over a /monoidal/
-- base morphism @arr@ with tensor @t@. The two constructors encode:
--
--   * 'Lift' — a plain base arrow.
--   * 'Knot' — a feedback loop with a hidden feedback channel.
--
-- The laws of traced monoidal categories are performed by the 'Category'
-- and 'Traced' instances, so every value is already in normal form: at most
-- one 'Knot' at the top, over a base-arrow body.
--
-- Over a premonoidal base the normal form is sound only when the 'Channel'
-- structural maps ('assoc', 'slide', etc.) are central. This is the
-- Benton–Hyland Central Sliding side-condition; see 'Circuit.Channel.Traced'
-- and the @circuits-axioma@ oracle "Loop trace requires centrality over
-- K IO".
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
-- The polar channel ends (@Out@, @In@), their counit (@close@), and
-- their unit (@open@) all live in "Circuit.Ends".
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

    -- * Layer witness
    FreeLoop,
  )
where

import Circuit.Category (Category (..), K (..), (.>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Layer (Layer (..), run, (:~>))
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.Profunctor
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Layer (run)

-- | The free traced monoidal category over base morphism @arr@ and tensor @t@,
-- in existential normal form.
--
-- Two constructors:
--
--   * 'Lift' — a plain base arrow.
--   * 'Knot' — a feedback loop with hidden channel @s@.
data Loop (t :: Type -> Type -> Type) arr a b where
  -- | A plain base arrow.
  Lift :: arr a b -> Loop t arr a b
  -- | Tie a feedback loop. The tensor @t@ carries the hidden channel type @s@.
  --
  -- The argument is the base arrow itself, /not/ a 'Lift'-wrapped stage.
  Knot ::
    arr (t s a) (t s b) ->
    Loop t arr a b

-- $examples
--
-- >>> run (Lift (+1) :: Loop (,) (->) Int Int) 5
-- 6
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

instance (Strength t arr) => Category (Loop t arr) where
  id :: forall a. Loop t arr a a
  id = Lift id
  (.) :: forall a b c. Loop t arr b c -> Loop t arr a b -> Loop t arr a c
  Lift f . Lift g = Lift (f . g)
  Knot f . Lift g = Knot (f . strength g)
  Lift f . Knot g = Knot (strength f . g)
  Knot f . Knot g = Knot (assoc .> strength g .> slide .> strength f .> slide .> assoc')

instance (Profunctor arr, Bifunctor t) => Profunctor (Loop t arr) where
  dimap :: forall a b c d. (a -> b) -> (c -> d) -> Loop t arr b c -> Loop t arr a d
  dimap f g (Lift h) = Lift (dimap f g h)
  dimap f g (Knot @_ @_ @_ @_ @_ h) = Knot (dimap (second f) (second g) h)
  lmap :: forall a b c. (a -> b) -> Loop t arr b c -> Loop t arr a c
  lmap f (Lift h) = Lift (lmap f h)
  lmap f (Knot @_ @_ @_ @_ @_ h) = Knot (lmap (second f) h)
  rmap :: forall a b c. (b -> c) -> Loop t arr a b -> Loop t arr a c
  rmap g (Lift h) = Lift (rmap g h)
  rmap g (Knot @_ @_ @_ @_ @_ h) = Knot (rmap (second g) h)

instance (Bifunctor t) => Functor (Loop t (->) a) where
  fmap f (Lift g) = Lift (f . g)
  fmap f (Knot g) = Knot (second f . g)

-- | Lift the 'Channel' structure of the base arrow into 'Loop t arr'.
instance (Strength t arr) => Channel t (Loop t arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  slide = Lift slide

-- | Lift the 'Strength' class through 'Loop t'.
instance (Strength t arr) => Strength t (Loop t arr) where
  strength (Lift f) = Lift (strength f)
  strength (Knot f) = Knot (slide .> strength f .> slide)

-- | Lift the 'Traced' class through 'Loop t'.
--
-- 'trace' hides a wire as a 'Knot'.
instance (Traced t arr) => Traced t (Loop t arr) where
  trace (Lift f) = Knot f
  trace (Knot f) = Knot (assoc .> f .> assoc')

-- | 'Traced' plus 'Channel' — required to fold free 'Loop' over a base
-- category.
class (Traced t arr, Channel t arr) => FreeLoop t arr

instance (Traced t arr, Channel t arr) => FreeLoop t arr

-- | Free traced monoidal category.
instance Layer (Loop t) where
  type Law (Loop t) arr' = FreeLoop t arr'
  type Run (Loop t) arr = (Traced t arr, Channel t arr)
  type Bind (Loop t) arr = ()
  unit = Lift
  bind ::
    forall arr arr' a b.
    (Law (Loop t) arr') =>
    (arr :~> arr') ->
    Loop t arr a b ->
    arr' a b
  bind h (Lift f) = h f
  bind h (Knot @_ @_ @_ @_ @_ f) = trace (h f)
