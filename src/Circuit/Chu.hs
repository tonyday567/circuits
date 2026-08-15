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

    -- * Tensor and par over Set
    ChuTensorNeg (..),
    ChuParPos (..),
    tensorChuObj,
    parChuObj,
    lolliChuObj,
    withChuObj,
    oplusChuObj,
    topChuObj,
    zeroChuObj,
    evalChu,
    tensorChu,
    parChu,
    chuUnitObj,
    chuBottomObj,
    chuTensorNegs,
    chuParPoss,
    chuSeparated,
    chuExtensional,
    leftUnitorChu,
    leftUnitorChuInv,
    rightUnitorChu,
    rightUnitorChuInv,
  )
where

import Circuit.Category (Category (..), Ob, ObDict (..))
import Circuit.Tensor (Action (..), Tensor (..), Unit)
import Data.Kind (Type)
import Data.Traversable (sequenceA)
import Data.Void (Void, absurd)
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


-- ===========================================================================
-- Tensor and par structure over Set (arr = (->), t = (,))
-- ===========================================================================
--
-- The Chu construction Chu(Set, K) is *-autonomous on the full subcategory of
-- separated extensional objects.  The operations below are defined for
-- arbitrary Chu objects, but the unit laws hold only when the objects are
-- separated and extensional.  See Barr, "The separated extensional Chu
-- category" (TAC 1998).

-- | Negative part of the Chu tensor @A ⊗ B@.
--
-- A value @(f, g)@ lives here when @e_A(a, g(b)) = e_B(b, f(a))@ for all
-- @a ∈ A⁺@, @b ∈ B⁺@.
data ChuTensorNeg a b c d = ChuTensorNeg
  { -- | @A⁺ -> B⁻@
    ctnForward :: a -> d,
    -- | @B⁺ -> A⁻@
    ctnBackward :: c -> b
  }

-- | Positive part of the Chu par @A ⅋ B@.
--
-- A value @(f, g)@ lives here when @e_A(g(d), a) = e_B(f(a), d)@ for all
-- @a ∈ A⁻@, @d ∈ B⁻@.
data ChuParPos a b c d = ChuParPos
  { -- | @A⁻ -> C⁺@
    cppForward :: b -> c,
    -- | @D⁻ -> A⁺@
    cppBackward :: d -> a
  }

-- | Tensor product of Chu objects over @Set@.
tensorChuObj ::
  (Eq r) =>
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuObj (,) r (->) (a, c) (ChuTensorNeg a b c d)
tensorChuObj (ChuObj _ _ r) (ChuObj _ _ s) =
  ChuObj (error "tensorChuObj: positive carrier unused") (error "tensorChuObj: negative carrier unused") $
    \((x, y), ChuTensorNeg f g) ->
      let lhs = r (x, g y)
          rhs = s (y, f x)
       in if lhs == rhs then lhs else error "tensorChuObj: ChuTensorNeg violates bilinear law"

-- | Par product of Chu objects over @Set@.
parChuObj ::
  (Eq r) =>
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuObj (,) r (->) (ChuParPos a b c d) (b, d)
parChuObj (ChuObj _ _ r) (ChuObj _ _ s) =
  ChuObj (error "parChuObj: positive carrier unused") (error "parChuObj: negative carrier unused") $
    \(ChuParPos f g, (x, y)) ->
      let lhs = r (g y, x)
          rhs = s (f x, y)
       in if lhs == rhs then lhs else error "parChuObj: ChuParPos violates bilinear law"

-- | Linear implication @A ⊸ B = A⊥ ⅋ B@ over @Set@.
--
-- The positive carrier is the set of Chu morphisms @A → B@, packaged as
-- 'ChuParPos' after negating @A@.
lolliChuObj ::
  (Eq r) =>
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuObj (,) r (->) (ChuParPos b a c d) (a, d)
lolliChuObj a b = parChuObj (negateChu a) b

-- | Additive conjunction @A & B@ over @Set@.
--
-- Positive carrier is @A⁺ × B⁺@; negative carrier is the disjoint union
-- @A⁻ + B⁻@.
withChuObj ::
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuObj (,) r (->) (a, c) (Either b d)
withChuObj (ChuObj _ _ eA) (ChuObj _ _ eB) =
  ChuObj (error "withChuObj: positive carrier unused") (error "withChuObj: negative carrier unused") $
    \((x, y), q) -> case q of
      Left b -> eA (x, b)
      Right d -> eB (y, d)

-- | Additive disjunction @A ⊕ B@ over @Set@.
--
-- Positive carrier is the disjoint union @A⁺ + B⁺@; negative carrier is
-- @A⁻ × B⁻@.
oplusChuObj ::
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuObj (,) r (->) (Either a c) (b, d)
oplusChuObj (ChuObj _ _ eA) (ChuObj _ _ eB) =
  ChuObj (error "oplusChuObj: positive carrier unused") (error "oplusChuObj: negative carrier unused") $
    \(q, (x, y)) -> case q of
      Left a -> eA (a, x)
      Right c -> eB (c, y)

-- | Additive unit @⊤@ over @Set@.
--
-- Positive carrier is the terminal object @1@; negative carrier is the
-- initial object @0@.
topChuObj :: ChuObj (,) r (->) () Void
topChuObj = ChuObj () (error "topChuObj: negative carrier unused") (\((), v) -> absurd v)

-- | Additive unit @0@ over @Set@.
--
-- Positive carrier is the initial object @0@; negative carrier is the
-- terminal object @1@.
zeroChuObj :: ChuObj (,) r (->) Void ()
zeroChuObj = ChuObj (error "zeroChuObj: positive carrier unused") () (\(v, ()) -> absurd v)

-- | Evaluation counit @A ⊗ (A ⊸ B) → B@ over @Set@.
--
-- Forward applies the Chu morphism stored in the implication object.
-- Backward pairs the argument with its own positive point, recovering the
-- adjoint condition.
evalChu ::
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuMorphism (,) r (->) (a, ChuParPos b a c d) (ChuTensorNeg a b (ChuParPos b a c d) (a, d)) c d
evalChu _ _ =
  ChuMorphism
    (\(x, m) -> cppForward m x)
    (\d -> ChuTensorNeg (\x -> (x, d)) (\m -> cppBackward m d))

-- | Tensor of two Chu morphisms.
tensorChu ::
  ChuMorphism (,) r (->) a b c d ->
  ChuMorphism (,) r (->) e f g h ->
  ChuMorphism (,) r (->) (a, e) (ChuTensorNeg a b e f) (c, g) (ChuTensorNeg c d g h)
tensorChu (ChuMorphism fPos fNeg) (ChuMorphism gPos gNeg) =
  ChuMorphism
    (\(x, y) -> (fPos x, gPos y))
    (\(ChuTensorNeg h k) -> ChuTensorNeg (gNeg . h . fPos) (fNeg . k . gPos))

-- | Par of two Chu morphisms.
parChu ::
  ChuMorphism (,) r (->) a b c d ->
  ChuMorphism (,) r (->) e f g h ->
  ChuMorphism (,) r (->) (ChuParPos a b e f) (b, f) (ChuParPos c d g h) (d, h)
parChu (ChuMorphism fPos fNeg) (ChuMorphism gPos gNeg) =
  ChuMorphism
    (\(ChuParPos h k) -> ChuParPos (gPos . h . fNeg) (fPos . k . gNeg))
    (\(x, y) -> (fNeg x, gNeg y))

-- | Unit object @I = (1, K)@ with pairing @snd@.
chuUnitObj :: ChuObj (,) r (->) () r
chuUnitObj = ChuObj () (error "chuUnitObj: negative carrier unused") snd

-- | Bottom object @⊥ = (K, 1)@, dual of the unit.
chuBottomObj :: ChuObj (,) r (->) r ()
chuBottomObj = ChuObj (error "chuBottomObj: positive carrier unused") () (\(k, ()) -> k)

-- | Left unitor @λ_A : I ⊗ A → A@ over @Set@.
--
-- Forward drops the unit; backward maps a negative point @b@ to the unique
-- Chu tensor negative with @f() = b@ and @g a = e(a, b)@.
leftUnitorChu ::
  ChuObj (,) r (->) a b ->
  ChuMorphism (,) r (->) ((), a) (ChuTensorNeg () r a b) a b
leftUnitorChu (ChuObj _ _ e) =
  ChuMorphism snd (\b -> ChuTensorNeg (const b) (\a -> e (a, b)))

-- | Inverse of the left unitor.
leftUnitorChuInv ::
  ChuObj (,) r (->) a b ->
  ChuMorphism (,) r (->) a b ((), a) (ChuTensorNeg () r a b)
leftUnitorChuInv _ = ChuMorphism ((),) (\(ChuTensorNeg f _) -> f ())

-- | Right unitor @ρ_A : A ⊗ I → A@ over @Set@.
rightUnitorChu ::
  ChuObj (,) r (->) a b ->
  ChuMorphism (,) r (->) (a, ()) (ChuTensorNeg a b () r) a b
rightUnitorChu (ChuObj _ _ e) =
  ChuMorphism fst (\b -> ChuTensorNeg (\a -> e (a, b)) (const b))

-- | Inverse of the right unitor.
rightUnitorChuInv ::
  ChuObj (,) r (->) a b ->
  ChuMorphism (,) r (->) a b (a, ()) (ChuTensorNeg a b () r)
rightUnitorChuInv _ = ChuMorphism (\a -> (a, ())) (\(ChuTensorNeg _ g) -> g ())

-- | Enumerate all 'ChuTensorNeg' values for finite carriers.
chuTensorNegs ::
  (Eq r, Eq a, Eq c) =>
  [a] ->
  [b] ->
  [c] ->
  [d] ->
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  [ChuTensorNeg a b c d]
chuTensorNegs as bs cs ds (ChuObj _ _ r) (ChuObj _ _ s) =
  [ ChuTensorNeg f g
    | f <- functions as ds,
      g <- functions cs bs,
      all (\(a, c) -> r (a, g c) == s (c, f a)) (cartesian as cs)
  ]

-- | Enumerate all 'ChuParPos' values for finite carriers.
chuParPoss ::
  (Eq r, Eq b, Eq d) =>
  [a] ->
  [b] ->
  [c] ->
  [d] ->
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  [ChuParPos a b c d]
chuParPoss as bs cs ds (ChuObj _ _ r) (ChuObj _ _ s) =
  [ ChuParPos f g
    | f <- functions bs cs,
      g <- functions ds as,
      all (\(b, d) -> r (g d, b) == s (f b, d)) (cartesian bs ds)
  ]

-- | All functions from a finite domain to a finite codomain.
functions :: (Eq a) => [a] -> [b] -> [a -> b]
functions [] _ = [const (error "functions: empty domain")]
functions domain codomain = map (listToFunction domain) (sequenceA (replicate (length domain) codomain))

listToFunction :: (Eq a) => [a] -> [b] -> a -> b
listToFunction domain values x = fromJust (lookup x (zip domain values))
  where
    fromJust (Just y) = y
    fromJust Nothing = error "listToFunction: input not in domain"

-- | Cartesian product of two lists.
cartesian :: [a] -> [b] -> [(a, b)]
cartesian xs ys = [(x, y) | x <- xs, y <- ys]

-- | A Chu object is /separated/ when the pairing distinguishes every pair of
-- positive points.  Equivalently, the transposed pairing @A⁺ -> (A⁻ ⊸ ⊥)@ is
-- injective.
chuSeparated ::
  (Eq r, Eq a) =>
  [a] ->
  [b] ->
  ChuObj (,) r (->) a b ->
  Bool
chuSeparated as bs (ChuObj _ _ e) =
  all
    (\(a1, a2) -> a1 == a2 || any (\b -> e (a1, b) /= e (a2, b)) bs)
    (cartesian as as)

-- | A Chu object is /extensional/ when the pairing distinguishes every pair of
-- negative points.  Equivalently, the pairing @A⁻ -> (A⁺ ⊸ ⊥)@ is injective.
chuExtensional ::
  (Eq r, Eq b) =>
  [a] ->
  [b] ->
  ChuObj (,) r (->) a b ->
  Bool
chuExtensional as bs (ChuObj _ _ e) =
  all
    (\(b1, b2) -> b1 == b2 || any (\a -> e (a, b1) /= e (a, b2)) as)
    (cartesian bs bs)
