{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Linear-logic connectives over a base category.
--
-- This module surfaces linear implication (@⊸@) and the exponential
-- modalities @!@ / @?@ as type-class structure.  The par product @⅋@ and
-- its unit @⊥@ live in "Circuit.Par".
module Circuit.Linear
  ( -- * Linear implication (internal hom)
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

import Circuit.Category (Category (..))
import Circuit.Par (Bot, Par (..))
import Circuit.Tensor (Tensor (..), Unit)
import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude hiding (curry, id, uncurry, (.))

-- ===========================================================================
-- Linear implication (internal hom)
-- ===========================================================================

-- | Closed monoidal structure: @A ⊸ B@ is the right adjoint of tensor.
--
-- Maps @A ⊗ B -> C@ correspond to maps @A -> B ⊸ C@ via 'curry'/'uncurry'.
-- 'eval' is the counit @A ⊗ (A ⊸ B) -> B@ (hom on the right of the tensor).
-- That is the existing Chu convention; it differs from @uncurry id@ by a
-- 'swap'.  'lolli' is identity on the implication object, used to mention
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
  eval ::
    arr (t a (LolliT t arr a b)) b

  -- | Curry the left factor: @(A ⊗ B -> C) -> (A -> B ⊸ C)@.
  curry ::
    arr (t a b) c ->
    arr a (LolliT t arr b c)

  -- | Uncurry the left factor: @(A -> B ⊸ C) -> (A ⊗ B -> C)@.
  uncurry ::
    arr a (LolliT t arr b c) ->
    arr (t a b) c

-- | Cartesian closed structure on functions: implication collapses to
-- function space.
instance Lolli (,) (->) where
  type LolliT (,) (->) a b = a -> b
  lolli _ = id
  {-# INLINE lolli #-}
  eval (a, f) = f a
  {-# INLINE eval #-}
  curry f a b = f (a, b)
  {-# INLINE curry #-}
  uncurry g (a, b) = g a b
  {-# INLINE uncurry #-}

-- ===========================================================================
-- Exponentials (! and ?)
-- ===========================================================================

-- | Exponential modality: object-level types for @!A@ and @?A@.
--
-- The structural rules are split into independent subclasses so that
-- affine and linear uses of the modality differ only in their constraint
-- sets, mirroring the 'Copy'/'Discard' split at the base-arrow level.
--
-- * @!A@ has a contraction half ('BangCopy') and a weakening half
--   ('BangWeaken').  Linear logic requires both; affine logic requires
--   only weakening.
-- * @?A@ currently exposes only its unit rule ('WhyNotIntro'); the ⅋-monoid
--   multiplication on @?A@ ('WhyNotMerge') is missing. In the vocabulary of
--   'Circuit.Dagger', @?A@ is currently 'CoAffine'-only (the unit @Zero@)
--   and the missing half is 'CoRelevant' (the merge @Merge@). That hole is
--   the first observable thing the Exponential split made visible; wiring it
--   is part of the chu-depth class dig.
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
-- par product rather than the tensor product. 'mergeE' is the
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
