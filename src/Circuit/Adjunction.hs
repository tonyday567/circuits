{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free-layer / free-forgetful adjunction tower.
--
-- Each layer @f@ is a free construction over a base arrow.  The single
-- 'FreeLayer' class replaces the per-layer folds:
--
-- * 'Circuit.Free.runFree'
-- * 'Circuit.Trace.run'
-- * 'Circuit.Net.weave'
--
-- with one associated constraint ('Lawful') saying what the target
-- category must be, and two combinators ('unit' and 'rightAdjunct')
-- that package the universal property.
--
-- The hom-set isomorphism is stated once, generically:
--
-- @
--   rightAdjunct h . unit = h              (β)
--   rightAdjunct unit     = id             (η)
-- @
--
-- Composition of layers is just nesting — no new operator, no bespoke
-- coherence lemmas.  The old hand-inlined joins (@run . melt@,
-- @runFree . freeze@) are recovered as @rightAdjunct id@.
module Circuit.Adjunction
  ( -- * Free-layer class
    Cat2,
    (:~>),
    FreeLayer (..),

    -- * Derived adjunction vocabulary
    leftAdjunct,
    realise,
    hoist,
    join,
  )
where

import Circuit.Dagger qualified as Dg
import Circuit.Free qualified as F
import Circuit.Monoidal (MonoidalP (..))
import Circuit.Net (Net (..))
import Circuit.Trace (Trace (Arr), foldTrace)
import Circuit.Traced (Traced (..))
import Control.Category (Category (..))
import Data.Kind (Constraint, Type)
import Prelude hiding (id, (.))

-- | A 2-cell in the category of Haskell categories: an arrow-to-arrow
-- mapping.  Homomorphisms preserve 'id', @(.)@, and the structure named
-- by the 'Lawful' constraint of the layer they are folded through.
type arr :~> arr' = forall x y. arr x y -> arr' x y

-- | The kind of Haskell categories: type-to-type hom-sets.
type Cat2 = Type -> Type -> Type

-- | A free construction over a base arrow.
--
-- * 'unit' includes the generators.
-- * 'rightAdjunct' folds the free syntax into any 'Lawful' target.
class FreeLayer (f :: Cat2 -> Cat2) where
  -- | What the target category must satisfy to receive a fold.
  type Lawful f (arr' :: Cat2) :: Constraint

  -- | Include a base arrow as a single generator.
  unit :: (Category arr) => arr :~> f arr

  -- | The universal fold out of the free construction.
  rightAdjunct :: (Lawful f arr') => (arr :~> arr') -> (f arr :~> arr')

-- | The left direction of the hom-set isomorphism.
leftAdjunct :: (FreeLayer f, Category arr) => (f arr :~> arr') -> (arr :~> arr')
leftAdjunct g = g . unit

-- | Fold a free layer into its own target level.
--
-- For 'Free' this is 'runFree'; for 'Trace' it is 'run';
-- for 'Net' it is 'weave'.
realise :: (FreeLayer f, Lawful f arr) => f arr :~> arr
realise = rightAdjunct id

-- | Functorial map of a homomorphism through a free layer.
hoist :: (FreeLayer f, Category arr', Lawful f (f arr')) => (arr :~> arr') -> (f arr :~> f arr')
hoist h = rightAdjunct (unit . h)

-- | Join nested layers.  Each layer is a monad on the category of
-- arrows; 'join' is the multiplication.
join :: (FreeLayer f, Lawful f (f arr)) => f (f arr) :~> f arr
join = rightAdjunct id

-- | Free category over a graph.
instance FreeLayer F.Free where
  type Lawful F.Free arr' = Category arr'
  unit = F.Lift
  rightAdjunct h (F.Lift f) = h f
  rightAdjunct h (F.Compose g f) = rightAdjunct h g . rightAdjunct h f

-- | Free traced monoidal category.
instance FreeLayer (Trace t) where
  type Lawful (Trace t) arr' = Traced arr' t
  unit = Arr
  rightAdjunct h c = foldTrace h c

-- | Free traced PROP with a bimonoid.
--
-- Structural rows are interpreted in the target category: parallel
-- composition uses 'par', braiding uses 'swap', and the bimonoid
-- generators are the images under @h@ of the source dictionaries carried
-- by the 'Copy', 'Discard', 'Plus', and 'Zero' constructors.
instance FreeLayer (Net t) where
  type Lawful (Net t) arr' = (Traced arr' t, MonoidalP arr')
  unit = Lift
  rightAdjunct h (Lift f) = h f
  rightAdjunct h (Compose g f) = rightAdjunct h g . rightAdjunct h f
  rightAdjunct h (Par f g) = par (rightAdjunct h f) (rightAdjunct h g)
  rightAdjunct _ Swap = swap
  rightAdjunct h Copy = h Dg.copy
  rightAdjunct h Discard = h Dg.discard
  rightAdjunct h Plus = h Dg.plus
  rightAdjunct h Zero = h Dg.zero
  rightAdjunct h (Knot f) = trace (rightAdjunct h f)
