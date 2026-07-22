{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | The free-layer / free-forgetful adjunction tower.
--
-- Each layer @f@ is a free construction over a base arrow:
--
-- * @run@ @Free@       — free category
-- * @run@ @Sym@        — free symmetric monoidal category
-- * @run@ @(Loop t)@  — free traced monoidal category
-- * @run@ @(Net t)@    — free traced PROP with bimonoid
--
-- 'Law' says what the /target/ category must satisfy to receive a 'bind'
-- fold; 'Run' says what the /base/ category must satisfy for a same-category
-- 'run'; and 'Bind' captures any extra source constraints needed when the
-- free syntax has structural rows that do not carry all 'Ob' evidence.
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

    -- * Derived vocabulary
    lower,
  )
where

import Circuit.Category (Category (..), ObDict (..))
import Data.Kind (Constraint, Type)
import Prelude hiding (id, (.))

-- $setup
-- >> import Circuit.Category (Category(..))
-- >> import Circuit.Free (Free)

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
  -- 'run' only needs the base category's own object constraints.
  type Law f (arr' :: Cat2) :: Constraint

  -- | What the base category must satisfy to receive a 'run' fold back into
  -- itself.  Defaults to no extra constraints.
  type Run f (arr :: Cat2) :: Constraint

  type Run f arr = ()

  -- | Extra constraints the /source/ category must satisfy for a 'bind'
  -- fold.  Defaults to no extra constraints; instances with structural
  -- rows that do not carry all needed 'Ob' evidence may require @Discrete@.
  --
  -- For example, 'Sym.Par' reuses the base 'Tensor.par' method, which is
  -- deliberately 'Ob'-free; because 'par = Par' has no object dictionaries
  -- to stash in the constructor, the source category must be @Discrete@ so
  -- the missing evidence can be manufactured on demand.
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
    (Run f arr, Law f arr, Bind f arr, Ob arr a, Ob arr b) =>
    f arr a b ->
    arr a b

  run = bind id id

  -- | The universal fold out of the free construction into any
  -- 'Law'-abiding target category.
  bind ::
    (Law f arr', Bind f arr, Ob arr a, Ob arr b, Ob arr' a, Ob arr' b) =>
    (forall s. ObDict arr s -> ObDict arr' s) ->
    (arr :~> arr') ->
    f arr a b ->
    arr' a b

-- | The left direction of the hom-set isomorphism: restrict a map out of
-- the free layer to the generators.
lower :: (Layer f, Category arr) => (f arr :~> arr') -> (arr :~> arr')
lower g = g . unit
