{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free-layer / free-forgetful adjunction tower.
--
-- Each layer @f@ is a free construction over a base arrow:
--
-- * @run@ @Free@       — free category
-- * @run@ @SMC@        — free symmetric monoidal category
-- * @run@ @Trace@      — free traced monoidal category (in "Circuit.Trace")
-- * @run@ @Net@        — free symmetric monoidal category with bimonoid
--
-- 'Law' says what the /target/ category must satisfy to receive a 'bind'
-- fold; 'Run' says what the /base/ category must satisfy for a same-category
-- 'run'; and 'Bind' captures any extra source constraints needed when the
-- free syntax has structural rows.
--
-- The hom-set isomorphism is stated once, generically:
--
-- @
--   bind h . unit = h              (β)
--   bind unit      = id            (η)
--   run            = bind id       (coherence, where both sides are defined)
-- @
--
-- Composition of layers is just nesting — no new operator, no bespoke
-- coherence lemmas.
module Circuit.Layer
  ( -- * Free-layer class
    Cat2,
    (:~>),
    Layer (..),

    -- * Free category
    Free (..),
    freeze,

    -- * Derived vocabulary
    lower,
  )
where

import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Data.Kind (Constraint, Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Category (Category(..))
-- >>> import Circuit.Layer (Free)

-- | The kind of Haskell categories: type-to-type hom-sets.
type Cat2 = Type -> Type -> Type

-- | An arrow-to-arrow mapping (a natural transformation between
-- profunctors).
type arr :~> arr' = forall x y. arr x y -> arr' x y

-- | A free construction over a base arrow.
--
-- * 'unit' includes the generators.
-- * 'run' folds the free syntax back into the same base category.
-- * 'bind' folds the free syntax into any 'Law'-abiding target.
class Layer (f :: Cat2 -> Cat2) where
  -- | What the target category must satisfy to receive a 'bind' fold.
  -- 'run' only needs the base category's own structure.
  type Law f (arr' :: Cat2) :: Constraint

  -- | What the base category must satisfy to receive a 'run' fold back into
  -- itself.  Defaults to no extra constraints.
  type Run f (arr :: Cat2) :: Constraint

  type Run f arr = ()

  -- | Extra constraints the /source/ category must satisfy for a 'bind'
  -- fold.  Defaults to no extra constraints.
  type Bind f (arr :: Cat2) :: Constraint

  type Bind f arr = ()

  -- | Include a base arrow as a single generator.
  unit :: (Category arr) => arr :~> f arr

  -- | Fold the free syntax into the same base category.
  --
  -- Defaults to @'bind' 'id'@, so the single eliminator vocabulary is
  -- coherent wherever it type-checks. Instances may still override this
  -- with a direct implementation if the weaker constraints of 'Run' do
  -- not already imply 'Law' and 'Bind'.
  run ::
    (Run f arr, Law f arr, Bind f arr) =>
    f arr a b ->
    arr a b
  run = bind id

  -- | The universal fold out of the free construction into any
  -- 'Law'-abiding target category.
  bind ::
    (Law f arr', Bind f arr) =>
    (arr :~> arr') ->
    f arr a b ->
    arr' a b

-- | The left direction of the hom-set isomorphism: restrict a map out of
-- the free layer to the generators.
lower :: (Layer f, Category arr) => (f arr :~> arr') -> (arr :~> arr')
lower g = g . unit

-- * Free category

-- | The free category over a base arrow.
--
-- The two constructors are 'Lift', which embeds a base arrow, and
-- 'Compose', which sequences two free morphisms.  The universal fold out
-- of 'Free' is 'run'.
--
-- >>> run (Lift (+1) :: Free (->) Int Int) 5
-- 6
-- >>> run (Compose (Lift (+1)) (Lift (*2)) :: Free (->) Int Int) 5
-- 11
data Free arr a b where
  -- | Embed a base arrow.
  Lift :: arr a b -> Free arr a b
  -- | Sequential composition.
  Compose :: Free arr b c -> Free arr a b -> Free arr a c

instance (Category arr) => Category (Free arr) where
  id = Lift id
  (.) = Compose

-- | Layer instance for the free category.
--
-- Without object constraints, folding is just recursive application of
-- the target category's composition.
instance Layer Free where
  type Law Free arr' = Category arr'
  type Run Free arr = Category arr
  type Bind Free arr = ()
  unit = Lift
  bind :: forall arr' arr a b. (Law Free arr') => (arr :~> arr') -> Free arr a b -> arr' a b
  bind h (Lift f) = h f
  bind h (Compose @_ @_ g f) = bind h g . bind h f

-- | Freeze a 'Free' category into its base arrow.
--
-- This is a synonym for 'run' @Free@.
--
-- >>> freeze (Lift (+1) :: Free (->) Int Int) 5
-- 6
freeze :: (Category arr) => Free arr a b -> arr a b
freeze (Lift f) = f
freeze (Compose g f) = freeze g . freeze f

-- | Lift the 'Channel' structure through 'Free'.
instance (Channel t arr) => Channel t (Free arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  slide = Lift slide

-- | Lift the 'Strength' class through 'Free'.
--
-- A morphism is frozen before tensoring with the feedback channel.
instance (Strength t arr) => Strength t (Free arr) where
  strength = Lift . strength . freeze

-- | Lift the 'Traced' class through 'Free'.
--
-- A loop body in @Free arr@ is frozen before calling the base 'trace'.
instance (Traced t arr) => Traced t (Free arr) where
  trace = Lift . trace . freeze
