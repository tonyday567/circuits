{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | The free-layer / free-forgetful adjunction tower.
--
-- Each layer @f@ is a free construction over a base arrow.  The single
-- 'Layer' class replaces the per-layer folds:
--
-- * @run@ @Free@       — free category
-- * @run@ @(Trace t)@  — free traced monoidal category
-- * @run@ @(Net t)@    — free traced PROP with bimonoid
--
-- with one associated constraint ('Law') saying what the target category
-- must satisfy, and two combinators ('unit' and 'bind') that package the
-- universal property.
--
-- The hom-set isomorphism is stated once, generically:
--
-- @
--   bind h . unit = h              (β)
--   bind unit      = id            (η)
-- @
--
-- Composition of layers is just nesting — no new operator, no bespoke
-- coherence lemmas.  Hand-inlined joins such as @run . melt@ are
-- recovered as @bind id@.
module Circuit.Layer
  ( -- * Free-layer class
    Cat2,
    NT,
    HNT,
    (:~>),
    (:~~>),
    Layer (..),

    -- * Derived vocabulary
    run,
    hmap,
    lower,
    join,
  )
where

import Circuit.Category (Category (..))
import Data.Kind (Constraint, Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Free

-- | The kind of Haskell categories: type-to-type hom-sets.
type Cat2 = Type -> Type -> Type

-- | A natural transformation between profunctors (arrow-to-arrow maps).
-- The underlying type of the infix synonym ':~>'.
type NT (p :: Cat2) (q :: Cat2) = forall x y. p x y -> q x y

-- | Infix synonym for 'NT': an arrow-to-arrow mapping.
-- Homomorphisms preserve 'id', @(.)@, and the structure named
-- by the 'Law' constraint of the layer they are folded through.
type arr :~> arr' = NT arr arr'

-- | A higher natural transformation between 2-functors on 'Cat2'.
-- The underlying type of the infix synonym ':~~>'.
type HNT (f :: Cat2 -> Cat2) (g :: Cat2 -> Cat2) = forall arr. f arr :~> g arr

-- | Infix synonym for 'HNT': a layer-to-layer mapping, natural in the
-- base arrow.
type f :~~> g = HNT f g

-- | A free construction over a base arrow.
--
-- * 'unit' includes the generators.
-- * 'bind' folds the free syntax into any 'Law'-abiding target.
class Layer (f :: Cat2 -> Cat2) where
  -- | What the target category must satisfy to receive a fold.
  type Law f (arr' :: Cat2) :: Constraint

  -- | Include a base arrow as a single generator.
  unit :: (Category arr) => arr :~> f arr

  -- | The universal fold out of the free construction.
  bind :: (Law f arr') => (arr :~> arr') -> (f arr :~> arr')

-- | The left direction of the hom-set isomorphism: restrict a map out of
-- the free layer to the generators.
lower :: (Layer f, Category arr) => (f arr :~> arr') -> (arr :~> arr')
lower g = g . unit

-- | Fold a free layer into its own target level.
--
-- Use with type application:
--
-- @
-- run @Free
-- run @(Trace t)
-- run @(Net t)
-- @
--
-- >>> run (Lift (+1) :: Free (->) Int Int) 5
-- 6
run :: (Layer f, Law f arr) => f arr :~> arr
run = bind id

-- | Functorial map of a homomorphism through a free layer.
--
-- Use with type application:
--
-- @
-- hmap @Free h
-- hmap @(Trace t) h
-- hmap @(Net t) h
-- @
hmap ::
  (Layer f, Category arr', Law f (f arr')) =>
  (arr :~> arr') ->
  (f arr :~> f arr')
hmap h = bind (unit . h)

-- | Join nested layers.  Each layer is a monad on the category of
-- arrows; 'join' is the multiplication.
join :: (Layer f, Law f (f arr)) => f (f arr) :~> f arr
join = bind id
