{-# LANGUAGE ScopedTypeVariables #-}

-- | The Chu construction over a monoidal base category.
--
-- A Chu object is a polarity pair @A⁺@ and @A⁻@ together with a pairing
-- @e : A⁺ ⊗ A⁻ → ⊥@.  Negation swaps the carriers via the braiding, and a
-- Chu morphism is an adjoint pair satisfying the equation
-- @e_B (f⁺ a, d) = e_A (a, f⁻ d)@.
--
-- == Excluded middle, split
--
-- Classical LEM says @A ∨ ¬A@ with a single disjunction.  Linear logic splits
-- that disjunction into two connectives:
--
--   * Additive @A ⊕ A⊥@ — a tagged verdict now.  This is /not/ supported:
--     there is no @decide :: Either (Proof a) (Refutation a)@ combinator.
--     The absence is load-bearing.
--   * Multiplicative @A ⅋ A⊥@ — the copycat strategy, provable as the linear
--     identity @⊢ A⊥, A@.  A symmetric end @Ends arr a a@ with
--     @close (conjoint e) (companion e) = id@ is exactly this witness; see
--     'endsAsChu' and 'Circuit.Ends.copycat'.
--
-- In this reading 'negateChu' is polarity swap, 'endsAsChu' embeds the
-- multiplicative witness, and 'chuLaw' is the adjoint equation that annihilates
-- a decided pairing into quiet.
--
-- This module also provides a small semiring class and the named-recipient
-- delivery pairing that motivated the construction in @circuits-agent@.
module Circuit.Chu
  ( -- * Semiring (minimal, local)
    ChuSemiring (..),

    -- * Chu objects and negation
    ChuObj (..),
    negateChu,

    -- * Chu morphisms
    ChuMorphism (..),
    idChu,
    composeChu,
    chuLaw,
    chuLawAt,

    -- * Ends embedding
    endsAsChu,

    -- * Delivery pairing
    deliversToSemiring,
    deliveryMatrix,
  )
where

import Circuit.Category (Category (..), (.>))
import Circuit.Ends (Ends (..), In (..), Out (..), close)
import Circuit.Tensor (Action (..), Tensor (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Chu
-- >>> import Circuit.Tensor (swap)
-- >>> import Prelude hiding (id, (.))

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
-- Ends embedding
-- ---------------------------------------------------------------------------

-- | Embed a symmetric end into a Chu object.
--
-- A self-dual channel @Ends arr a a@ has write end @In arr a@ and read end
-- @Out arr a@.  'close' is already the pairing @In ⊗ Out → arr a a@, so the
-- embedding is direct.
endsAsChu ::
  Ends arr a a ->
  ChuObj (,) (arr a a) (->) (In arr a) (Out arr a)
endsAsChu e = ChuObj (conjoint e) (companion e) (uncurry close)
{-# INLINE endsAsChu #-}

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
