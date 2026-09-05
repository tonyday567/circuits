{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Linear-logic connectives over a base category.
--
-- This module surfaces the multiplicative–exponential fragment as
-- type-class structure: the multiplicative disjunction (@⅋@) with its
-- unit @⊥@ and one-way distributors, linear implication (@⊸@) as the
-- internal hom, and the exponential modalities @!@ / @?@.
module Circuit.Linear
  ( -- * Multiplicative disjunction
    Bot,
    Par (..),

    -- * Linear distributors and mix
    distL,
    distR,
    mix,

    -- * Linear implication (internal hom)
    Lolli (..),

    -- * Exponentials
    Exponential (..),
    BangCopy (..),
    BangWeaken (..),
    WhyNotIntro (..),
    WhyNotMonoid (..),
    LinearBang,
    AffineBang,
    RelevantBang,
  )
where

import Circuit.Category (Category (..), K (..))
import Circuit.Tensor (Tensor (..), Unit)
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- * Multiplicative disjunction

-- | Unit of the multiplicative disjunction (@⊥@).
type family Bot (p :: k -> k -> k) :: k

-- | Multiplicative disjunction action on a category.
--
-- 'parP' is the tensor product of morphisms.  The unitors witness that
-- @⊥ ⅋ a ≅ a@ and @a ⅋ ⊥ ≅ a@.
class (Category arr) => Par p arr where
  -- | Parallel composition under tensor.
  parP :: arr a b -> arr c d -> arr (p a c) (p b d)

  -- | Left unitor: @⊥ ⅋ a -> a@.
  unitlP :: arr (p (Bot p) a) a

  -- | Inverse left unitor: @a -> ⊥ ⅋ a@.
  unitlP' :: arr a (p (Bot p) a)

  -- | Right unitor: @a ⅋ ⊥ -> a@.
  unitrP :: arr (p a (Bot p)) a

  -- | Inverse right unitor: @a -> a ⅋ ⊥@.
  unitrP' :: arr a (p a (Bot p))

-- | The coproduct is the canonical tensor product on functions.
type instance Bot Either = Void

-- | Coproduct as multiplicative disjunction on functions.
--
-- The unit is the initial object @Void@; the unitors are the coproduct
-- injections absorbed by the universal property.
instance Par Either (->) where
  parP = bimap
  {-# INLINE parP #-}
  unitlP = either absurd id
  {-# INLINE unitlP #-}
  unitlP' = Right
  {-# INLINE unitlP' #-}
  unitrP = either id absurd
  {-# INLINE unitrP #-}
  unitrP' = Left
  {-# INLINE unitrP' #-}

-- | Coproduct as multiplicative disjunction on @K@ arrows.
instance (Monad m) => Par Either (K m) where
  parP (K f) (K g) =
    K $ \case
      Left a -> Left <$> f a
      Right c -> Right <$> g c
  {-# INLINE parP #-}
  unitlP = K $ either absurd pure
  {-# INLINE unitlP #-}
  unitlP' = K $ pure . Right
  {-# INLINE unitlP' #-}
  unitrP = K $ either pure absurd
  {-# INLINE unitrP #-}
  unitrP' = K $ pure . Left
  {-# INLINE unitrP' #-}

-- * Linear distributors and mix

-- | Left linear distributor: @A ⊗ (B ⅋ C) -> (A ⊗ B) ⅋ C@.
--
-- For @(,)@ and @Either@ this is the one-way product-over-coproduct map.
-- Note that @(_, Right c) = Right c@ discards the @a@; this is legal
-- affinely but not in strict MLL. The distributors already live in the
-- affine fragment.
distL :: (a, Either b c) -> Either (a, b) c
distL (a, Left b) = Left (a, b)
distL (_, Right c) = Right c
{-# INLINE distL #-}

-- | Right linear distributor: @(B ⅋ C) ⊗ A -> B ⅋ (C ⊗ A)@.
--
-- Mirror of 'distL': the same affine discard is present when the left
-- summand is taken.
distR :: (Either b c, a) -> Either b (c, a)
distR (Left b, _) = Left b
distR (Right c, a) = Right (c, a)
{-# INLINE distR #-}

-- | Mix: the canonical map @⊥ -> 1@ from tensor unit to tensor unit.
--
-- Every @⊥@-value is vacuous, so it maps to the unique tensor unit.
mix :: Void -> ()
mix = absurd
{-# INLINE mix #-}

-- * Linear implication (internal hom)

-- | Closed monoidal structure: @A ⊸ B@ is the right adjoint of tensor.
--
-- Maps @A ⊗ B -> C@ correspond to maps @A -> B ⊸ C@ via 'curryL'/'uncurryL'.
-- 'evalLinear' is the counit @A ⊗ (A ⊸ B) -> B@ (hom on the right of the tensor).
-- That is the existing Chu convention; it differs from @uncurryL id@ by a
-- 'Circuit.Tensor.braid'.  'lolli' is identity on the implication object, used to mention
-- it.
--
-- Kind is fixed to 'Type' so type applications stay concrete (GHC 9.14
-- panics on kind-polymorphic @TypeApplications@ here).
class (Category arr) => Lolli (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) where
  -- | The implication object @A ⊸ B@.
  --
  -- Indexed by the base arrow as well as the tensor, so @(->)@ and
  -- @Mat@ can both close @(,)@ without colliding.
  type LolliT t arr a b :: Type

  -- | Identity at the implication object.  The argument is a type proxy.
  lolli ::
    arr a b ->
    arr (LolliT t arr a b) (LolliT t arr a b)

  -- | Evaluation counit @A ⊗ (A ⊸ B) -> B@.
  evalLinear ::
    arr (t a (LolliT t arr a b)) b

  -- | Curry the left factor: @(A ⊗ B -> C) -> (A -> B ⊸ C)@.
  curryL ::
    arr (t a b) c ->
    arr a (LolliT t arr b c)

  -- | Uncurry the left factor: @(A -> B ⊸ C) -> (A ⊗ B -> C)@.
  uncurryL ::
    arr a (LolliT t arr b c) ->
    arr (t a b) c

-- | Cartesian closed structure on functions: implication collapses to
-- function space.
instance Lolli (,) (->) where
  type LolliT (,) (->) a b = a -> b
  lolli _ = id
  {-# INLINE lolli #-}
  evalLinear (a, f) = f a
  {-# INLINE evalLinear #-}
  curryL f a b = f (a, b)
  {-# INLINE curryL #-}
  uncurryL g (a, b) = g a b
  {-# INLINE uncurryL #-}

-- * Exponentials (! and ?)

-- | Exponential modality: object-level types for @!A@ and @?A@.
--
-- The structural rules are split into independent subclasses so that
-- affine and linear uses of the modality differ only in their constraint
-- sets, mirroring the 'Circuit.Bimonoid.Copy'/'Circuit.Bimonoid.Discard' split at the base-arrow level.
--
-- * @!A@ has a contraction half ('BangCopy') and a weakening half
--   ('BangWeaken').  Linear logic requires both; affine logic requires
--   only weakening.
-- * @?A@ has its unit rule ('WhyNotIntro') and its ⅋-monoid structure
--   ('WhyNotMonoid': 'mergeE' and 'zeroE').  In the vocabulary of
--   'Circuit.Bimonoid', these are the 'Circuit.Bimonoid.CoAffine' half
--   (the unit) and the 'Circuit.Bimonoid.CoRelevant' half (the merge).
class (Tensor t arr) => Exponential t arr where
  type Bang t arr a :: Type
  type WhyNot t arr a = result | result -> a

-- | Contraction half of @!A@: copy @!A → !A ⊗ !A@.
class (Exponential t arr) => BangCopy t arr where
  copyE ::
    arr (Bang t arr a) (t (Bang t arr a) (Bang t arr a))

-- | Weakening half of @!A@: dereliction @!A → A@ and discard @!A → I@.
class (Exponential t arr) => BangWeaken t arr where
  discardE ::
    arr (Bang t arr a) (Unit t)

  derelict ::
    arr (Bang t arr a) a

-- | Unit rule for @?A@: introduction @A → ?A@.
class (Exponential t arr) => WhyNotIntro t arr where
  introduce ::
    arr a (WhyNot t arr a)

-- | The ⅋-monoid structure on @?A@.
--
-- Dual to the @!@-comonoid ('BangCopy' / 'BangWeaken'), but living on the
-- par product (@⅋@) rather than the tensor product (@⊗@). 'mergeE' is the
-- multiplication @?A ⅋ ?A → ?A@ and 'zeroE' is the unit @⊥ → ?A@.
class (Exponential t arr, Par p arr) => WhyNotMonoid t p arr where
  mergeE ::
    arr (p (WhyNot t arr a) (WhyNot t arr a)) (WhyNot t arr a)

  zeroE ::
    arr (Bot p) (WhyNot t arr a)

-- | Linear @!A@: both contraction and weakening.
type LinearBang t arr = (Exponential t arr, BangCopy t arr, BangWeaken t arr)

-- | Affine @!A@: weakening only.
type AffineBang t arr = (Exponential t arr, BangWeaken t arr)

-- | Relevant @!A@: contraction only.
type RelevantBang t arr = (Exponential t arr, BangCopy t arr)

-- | Cartesian collapse: @!A ≅ A@, and @?A@ is the free monoid of lists.
instance Exponential (,) (->) where
  type Bang (,) (->) a = a
  type WhyNot (,) (->) a = [a]

instance BangCopy (,) (->) where
  copyE x = (x, x)
  {-# INLINE copyE #-}

instance BangWeaken (,) (->) where
  discardE _ = ()
  {-# INLINE discardE #-}
  derelict = id
  {-# INLINE derelict #-}

instance WhyNotIntro (,) (->) where
  introduce x = [x]
  {-# INLINE introduce #-}

instance WhyNotMonoid (,) Either (->) where
  mergeE = either id id
  {-# INLINE mergeE #-}
  zeroE = absurd
  {-# INLINE zeroE #-}
