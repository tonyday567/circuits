{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}

-- | Multiplicative disjunction (@⅋@) and its linear distributors.
--
-- This module surfaces the tensor product, its unit @⊥@, and the one-way
-- distributors between tensor and tensor.  These are "mixed metaphor"
-- structure: they relate a tensor @t@ (typically @(,)@) with a tensor
-- product @p@ (typically 'Either').
module Circuit.Par
  ( -- * Multiplicative disjunction
    Bot,
    Par (..),

    -- * Linear distributors and mix
    distL,
    distR,
    mix,
  )
where

import Circuit.Category (Category (..), K (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- | Unit of the tensor tensor (@⊥@).
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
