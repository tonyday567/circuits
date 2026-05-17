{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free traced monoidal category.
--
-- `Circuit arr t a b` is the initial encoding of a traced monoidal category
-- over a base morphism `arr` with a supplied tensor `t` for the category. The three constructors encode:
--
--   - `Lift`: embedding of a base arrow (strict monoidal functor)
--   - `Compose`: sequential composition (category structure)
--   - `Knot`: feedback channel (trace structure)
--
-- For example, a `Circuit (->) (,)` is the initial traced monoidal cartesian category over Haskell functions.
--
-- The `reify` function interprets any `Circuit` to a plain arrow via
-- the `Trace` instance on `t`. For encoding into 'Circuit.Hyper', see
-- 'Circuit.Hyper.encode' and 'Circuit.Hyper.encodeEither'.
module Circuit.Circuit
  ( -- * Circuit
    Circuit (..),
    (↑),
    (⊙),
    (↮),

    -- * Operators
    reify,
    (↘),
    push,
    (⊲),
    ambient,
    (↣),
  )
where

import Circuit.Traced (Trace (..))
import Control.Category
import Data.Bifunctor
import Data.Profunctor
import Prelude hiding (id, (.))

-- $setup
-- >>> import Data.Profunctor (dimap)
-- >>> import Prelude hiding (id, (.))

-- | The free traced monoidal category over base morphism @arr@ and tensor @t@.
--
-- Three constructors:
--
--   * 'Lift' — embed a base arrow.
--   * 'Compose' — sequential composition.
--   * 'Knot' — feedback loop via the tensor.
data Circuit arr t a b where
  -- | Lift embeds a base arrow (strict monoidal functor).
  Lift :: arr a b -> Circuit arr t a b
  -- | Compose performs sequential composition (category structure).
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  -- | Knot ties a feedback loop. The tensor t carries the channel type.
  Knot :: arr (t a b) (t a c) -> Circuit arr t b c

-- | Synonym for 'Lift'.
infixr 9 ↑

(↑) :: arr a b -> Circuit arr t a b
(↑) = Lift

-- | Synonym for 'Knot'.
infixr 9 ↮

(↮) :: arr (t a b) (t a c) -> Circuit arr t b c
(↮) = Knot

-- | Synonym for 'Compose'.
(⊙) :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
(⊙) = Compose

-- | Synonym for 'reify'.
infixl 9 ↘

-- | Collapse a Circuit to a plain arrow.
(↘) :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
(↘) = reify

instance (Category arr) => Category (Circuit arr t) where
  id = Lift id
  (.) = Compose

instance Functor (Circuit (->) t a) where
  fmap f = Compose (Lift f)

-- | Profunctor instance for Circuit.
--
-- Maps over both ends of the arrow. For @Compose@, the map is applied
-- to the input of the left sub-circuit and the output of the right
-- sub-circuit, leaving the intermediate type aligned. For @Knot@, the
-- map is lifted through the tensor via 'bimap'.
--
-- >>> reify (dimap (+ 1) (+ 1) (Lift (* 2) :: Circuit (->) (,) Int Int)) 5
-- 13
instance (Profunctor arr, Bifunctor t) => Profunctor (Circuit arr t) where
  dimap f g (Lift h) = Lift (dimap f g h)
  dimap f g (Compose h k) = Compose (dimap id g h) (dimap f id k)
  dimap f g (Knot k) = Knot (dimap (second f) (second g) k)
  lmap f (Lift h) = Lift (lmap f h)
  lmap f (Compose h k) = Compose (lmap id h) (lmap f k)
  lmap f (Knot k) = Knot (lmap (second f) k)
  rmap g (Lift h) = Lift (rmap g h)
  rmap g (Compose h k) = Compose (rmap g h) (rmap id k)
  rmap g (Knot k) = Knot (rmap (second g) k)

-- | Push a plain function onto a Circuit.
--
-- >>> reify (push (+1) (Lift (*2) :: Circuit (->) (,) Int Int)) 5
-- 11
push :: arr b c -> Circuit arr t a b -> Circuit arr t a c
push f = Compose (Lift f)

-- | Push / prepend a plain function to a Circuit. Operator form of 'push'.
infixr 8 ⊲

(⊲) :: arr b c -> Circuit arr t a b -> Circuit arr t a c
(⊲) = push

-- | Left-to-right sequential composition. Operator form of @(>>>).
infixl 9 ↣

(↣) :: Circuit arr t a b -> Circuit arr t b c -> Circuit arr t a c
f ↣ g = g ⊙ f

-- | Thread a state wire through a Circuit.
--
-- 'ambient' threads a state component @s@ through a circuit unchanged.
-- The circuit operates on the payload while the state rides alongside
-- via the tensor @t@ — ambient, unnoticed.
--
-- The @braid@ function swaps the state wire past the feedback channel:
-- @t x (t s a) -> t s (t x a)@. For @(,)@, this is
-- @\\(x, (s, a)) -> (s, (x, a))@.
--
-- For 'Lift', the state tags along via 'untrace'.
-- For 'Compose', the state threads through both stages.
-- For 'Knot', the state slides past the feedback loop via braiding —
-- the sliding axiom made explicit.
--
-- >>> let braid (x, (s, a)) = (s, (x, a)) in reify (ambient braid (Lift (+1) :: Circuit (->) (,) Int Int)) ("st", 5)
-- ("st",6)
--
-- >>> let braid (x, (s, a)) = (s, (x, a)); step (xs, ()) = (0 : xs, take 3 xs) in reify (ambient braid (Knot step)) ("st", ())
-- ("st",[0,0,0])
ambient :: (Profunctor arr, Trace arr t)
        => (forall x y z. t x (t y z) -> t y (t x z))
        -> Circuit arr t a b
        -> Circuit arr t (t s a) (t s b)
ambient _braid (Lift f) = Lift (untrace f)
ambient braid (Compose f g) = Compose (ambient braid f) (ambient braid g)
ambient braid (Knot k) = Knot (dimap braid braid (untrace k))

-- | Interpret a Circuit to a plain arrow.
--
-- This is the unique traced functor from the initial object (Circuit)
-- to the target category. The Mendler case (when a Knot appears on the
-- left of Compose) enforces the sliding axiom of traced monoidal categories.
--
-- >>> reify (Lift (+1) :: Circuit (->) (,) Int Int) 5
-- 6
reify :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
reify (Lift f) = f
reify (Compose (Knot f) g) = trace (f . untrace (reify g))
reify (Compose f g) = reify f . reify g
reify (Knot k) = trace k
