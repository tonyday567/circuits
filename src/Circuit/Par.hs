{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Multiplicative disjunction (par, ⅋) and linear distributivity.
--
-- A @Par p arr@ is a second monoidal structure on @arr@ with its own unit
-- @⊥ = Bot p@.  Together with a tensor @Tensor t arr@ it forms a linearly
-- distributive category: the distributors are one-way doors from a tensor
-- into a par, not isomorphisms.
--
-- The canonical instance here takes the coproduct @Either@ as the par
-- bifunctor over @(->)@, with unit @Void@.  This is the partner of the
-- cartesian product @(,)@ with unit @()@: products distribute over coproducts
-- in exactly one direction, and that direction is the linear distributor.
module Circuit.Par
  ( -- * Par unit
    Bot,

    -- * Par action
    Par (..),

    -- * Linear distributors
    distL,
    distR,

    -- * Mix: the canonical map from bottom to the tensor unit
    mix,
  )
where

import Circuit.Category (Category (..))
import Circuit.Tensor (Tensor (..), Unit)
import Control.Arrow (Kleisli (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- | Unit of the par tensor (⊥).
type family Bot (p :: k -> k -> k) :: k

-- | Multiplicative disjunction action on a category.
--
-- 'parP' is the par product of morphisms.  The unitors witness that
-- @⊥ ⅋ a ≅ a@ and @a ⅋ ⊥ ≅ a@.
class (Category arr) => Par p arr where
  -- | Parallel composition under par.
  parP :: arr a b -> arr c d -> arr (p a c) (p b d)

  -- | Left unitor: @⊥ ⅋ a -> a@.
  unitlP :: (Ob arr a) => arr (p (Bot p) a) a

  -- | Inverse left unitor: @a -> ⊥ ⅋ a@.
  unitlP' :: (Ob arr a) => arr a (p (Bot p) a)

  -- | Right unitor: @a ⅋ ⊥ -> a@.
  unitrP :: (Ob arr a) => arr (p a (Bot p)) a

  -- | Inverse right unitor: @a -> a ⅋ ⊥@.
  unitrP' :: (Ob arr a) => arr a (p a (Bot p))

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

-- | Coproduct as multiplicative disjunction on @Kleisli@ arrows.
instance (Monad m) => Par Either (Kleisli m) where
  parP (Kleisli f) (Kleisli g) =
    Kleisli $ \case
      Left a -> Left <$> f a
      Right c -> Right <$> g c
  {-# INLINE parP #-}
  unitlP = Kleisli $ either absurd pure
  {-# INLINE unitlP #-}
  unitlP' = Kleisli $ pure . Right
  {-# INLINE unitlP' #-}
  unitrP = Kleisli $ either pure absurd
  {-# INLINE unitrP #-}
  unitrP' = Kleisli $ pure . Left
  {-# INLINE unitrP' #-}

-- ---------------------------------------------------------------------------
-- Linear distributors and mix
-- ---------------------------------------------------------------------------

-- | Left linear distributor: @A ⊗ (B ⅋ C) -> (A ⊗ B) ⅋ C@.
--
-- For @(,)@ and @Either@ this is the one-way product-over-coproduct map.
distL :: (a, Either b c) -> Either (a, b) c
distL (a, Left b) = Left (a, b)
distL (_, Right c) = Right c
{-# INLINE distL #-}

-- | Right linear distributor: @(B ⅋ C) ⊗ A -> B ⅋ (C ⊗ A)@.
--
-- This is the mirror of 'distL'.
distR :: (Either b c, a) -> Either b (c, a)
distR (Left b, _) = Left b
distR (Right c, a) = Right (c, a)
{-# INLINE distR #-}

-- | Mix: the canonical map @⊥ -> 1@ from par unit to tensor unit.
--
-- Every @⊥@-value is vacuous, so it maps to the unique tensor unit.
mix :: Void -> ()
mix = absurd
{-# INLINE mix #-}
