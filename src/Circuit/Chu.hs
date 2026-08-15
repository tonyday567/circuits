{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The Chu construction over a monoidal base category.
--
-- A Chu object is a polarity pair @A⁺@ and @A⁻@ together with a pairing
-- @A⁺ ⊗ A⁻ → ⊥@ into a dualising object.  A Chu morphism is an adjoint pair
-- satisfying the equation
--
-- > e_B (f⁺ a, d) = e_A (a, f⁻ d)
--
-- This is the only genuinely star-autonomous, non-compact structure in the
-- library: proper ⊗ vs ⅋, proper additives, a real negation, and an internal
-- hom that is not just @A⊥ ⊗ B@.  Promoting it to a base arrow makes the
-- linear-logic distinctions measurable for the first time.
module Circuit.Chu
  ( -- * Dualising semiring
    ChuSemiring (..),

    -- * Chu objects and morphisms
    ChuObj (..),
    ChuMorphism (..),
    Chu (..),
    ChuObjShape (..),
    negateChu,
    idChu,
    composeChu,

    -- * Adjoint law
    chuLaw,
    chuLawAt,

    -- * Delivery pairing
    deliversToSemiring,
    deliveryMatrix,
  )
where

import Circuit.Category (Category (..), Ob, ObDict (..))
import Circuit.Tensor (Action (..), Tensor (..), Unit)
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- Minimal semiring
-- ---------------------------------------------------------------------------

-- | A semiring, kept local to this module so the delivery instance does not
-- pull in an external numeric prelude.
class ChuSemiring r where
  sZero :: r
  sOne :: r
  sPlus :: r -> r -> r
  sTimes :: r -> r -> r

instance ChuSemiring Bool where
  sZero = False
  sOne = True
  sPlus = (||)
  sTimes = (&&)

instance ChuSemiring Double where
  sZero = 0
  sOne = 1
  sPlus = (+)
  sTimes = (*)

instance ChuSemiring Integer where
  sZero = 0
  sOne = 1
  sPlus = (+)
  sTimes = (*)

-- ---------------------------------------------------------------------------
-- Chu objects
-- ---------------------------------------------------------------------------

-- | An object of @Chu(C, ⊥)@.
--
-- * @a@ is the positive carrier.
-- * @b@ is the negative carrier.
-- * @chuPair@ is the pairing @a ⊗ b → r@ into the dualising object.
data ChuObj t r arr a b = ChuObj
  { -- | Positive carrier.
    chuPos :: a,
    -- | Negative carrier.
    chuNeg :: b,
    -- | Pairing into the dualising object.
    chuPair :: arr (t a b) r
  }

-- | Negation swaps the carriers via the symmetric braiding.
--
-- Involution is definitional for a symmetric braiding:
-- @swap . swap = id@.
negateChu ::
  (Action t arr, Ob arr a, Ob arr b, Ob arr r, Ob arr (t a b), Ob arr (t b a)) =>
  ChuObj t r arr a b ->
  ChuObj t r arr b a
negateChu (ChuObj a b e) = ChuObj b a (e . swap)
{-# INLINE negateChu #-}

-- ---------------------------------------------------------------------------
-- Chu morphisms
-- ---------------------------------------------------------------------------

-- | A Chu morphism @A → B@ is a pair of base arrows:
--
-- * @chuForward :: arr a c@ runs forward from @A⁺@ to @B⁺@.
-- * @chuBackward :: arr d b@ runs backward from @B⁻@ to @A⁻@.
data ChuMorphism t r arr a b c d = ChuMorphism
  { -- | Forward component.
    chuForward :: arr a c,
    -- | Backward component.
    chuBackward :: arr d b
  }

-- | Identity Chu morphism.
idChu ::
  (Category arr, Ob arr a, Ob arr b) =>
  ChuMorphism t r arr a b a b
idChu = ChuMorphism id id
{-# INLINE idChu #-}

-- | Sequential composition of Chu morphisms.
--
-- Forward components compose covariantly; backward components compose
-- contravariantly.
composeChu ::
  (Category arr, Ob arr a, Ob arr b, Ob arr c, Ob arr d, Ob arr e, Ob arr f) =>
  ChuMorphism t r arr c d e f ->
  ChuMorphism t r arr a b c d ->
  ChuMorphism t r arr a b e f
composeChu (ChuMorphism f2 g2) (ChuMorphism f1 g1) =
  ChuMorphism (f2 . f1) (g1 . g2)

-- ---------------------------------------------------------------------------
-- Chu as a base arrow
-- ---------------------------------------------------------------------------

-- | Object-shape evidence for the 'Category' instance.  Every object of
-- @Chu(C, ⊥)@ is a 'ChuObj'; this class exposes its carriers so that
-- identity and composition can be typed uniformly.
class ChuObjShape a where
  type ChuPosType a :: Type
  type ChuNegType a :: Type

instance ChuObjShape (ChuObj t r arr p n) where
  type ChuPosType (ChuObj t r arr p n) = p
  type ChuNegType (ChuObj t r arr p n) = n

-- | @Chu t r arr@ is the Chu construction as a base arrow.  Objects are
-- 'ChuObj's; morphisms are adjoint pairs wrapped by the 'Chu' constructor.
newtype Chu (t :: Type -> Type -> Type) (r :: Type) (arr :: Type -> Type -> Type) (a :: Type) (b :: Type) where
  Chu ::
    ChuMorphism t r arr (ChuPosType a) (ChuNegType a) (ChuPosType b) (ChuNegType b) ->
    Chu t r arr a b

instance (Category arr) => Category (Chu t r arr) where
  type Ob (Chu t r arr) a = (ChuObjShape a, Ob arr (ChuPosType a), Ob arr (ChuNegType a))

  id :: forall a. (Ob (Chu t r arr) a) => Chu t r arr a a
  id = Chu (idChu :: ChuMorphism t r arr (ChuPosType a) (ChuNegType a) (ChuPosType a) (ChuNegType a))

  (.) ::
    forall a b c.
    (Ob (Chu t r arr) a, Ob (Chu t r arr) b, Ob (Chu t r arr) c) =>
    Chu t r arr b c ->
    Chu t r arr a b ->
    Chu t r arr a c
  Chu g . Chu f = Chu (composeChu g f)

-- | The adjoint law for @arr = (->)@ and the cartesian tensor.
--
-- A pair @(f⁺, f⁻)@ is a Chu morphism exactly when
-- @e_B (f⁺ a, d) = e_A (a, f⁻ d)@ for all @a@ and @d@.
chuLaw ::
  (Eq r) =>
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuMorphism (,) r (->) a b c d ->
  a ->
  d ->
  Bool
chuLaw src tgt (ChuMorphism f g) a d =
  chuPair tgt (f a, d) == chuPair src (a, g d)
{-# INLINE chuLaw #-}

-- | Pointwise adjoint law for @arr = (->)@.
--
-- When the dualising object @r@ does not have an 'Eq' instance (e.g. it is
-- itself a function), supply a probe @k :: r -> s@ with 'Eq' @s@.
chuLawAt ::
  (Eq s) =>
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuMorphism (,) r (->) a b c d ->
  a ->
  d ->
  (r -> s) ->
  Bool
chuLawAt src tgt (ChuMorphism f g) a d k =
  k (chuPair tgt (f a, d)) == k (chuPair src (a, g d))
{-# INLINE chuLawAt #-}

-- ---------------------------------------------------------------------------
-- Delivery pairing
-- ---------------------------------------------------------------------------

-- | Named-recipient delivery predicate over an arbitrary semiring.
--
-- A post whose recipient list contains @who@ delivers with 'sOne';
-- an empty list delivers to no one with 'sZero'.
deliversToSemiring ::
  (ChuSemiring r, Eq a) =>
  -- | Recipients on the post.
  [a] ->
  -- | Recipient name.
  a ->
  r
deliversToSemiring recipients who
  | null recipients = sZero
  | who `elem` recipients = sOne
  | otherwise = sZero

-- | Delivery matrix for a fixed list of posts and a roster of agents.
--
-- Rows are posts (in the order given), columns are agents (in the order
-- given), and entry @(p, a)@ is the delivery weight of post @p@ to agent @a@.
deliveryMatrix ::
  (ChuSemiring r, Eq col) =>
  -- | Agents (column labels).
  [col] ->
  -- | Recipient lists for each post (row labels are implicit).
  [[col]] ->
  [[r]]
deliveryMatrix agents recipients =
  [map (deliversToSemiring recips) agents | recips <- recipients]
