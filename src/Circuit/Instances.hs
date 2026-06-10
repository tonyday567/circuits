{-# LANGUAGE CPP #-}

-- | Concrete instances for the standard base arrows.
--
--   * 'Dup' @(->)@ — every type copies for free (Fox's theorem).
--   * 'Additive' @(->)@ — addition via 'Num'.
--   * 'MonoidalP' — parallel composition and swapping for product categories.
module Circuit.Instances
  ( -- * Monoidal product
    MonoidalP (..),
  )
where

#ifdef __GLASGOW_HASKELL__
import Control.Category
#else
import Circuit.Classes
#endif

import Circuit.Additive (Additive (..))
import Circuit.Dup (Dup (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> 1 + 1 :: Int
-- 2
-- >>> import Circuit.Instances
-- >>> import Circuit.Dup (Dup(..))
-- >>> import Circuit.Additive (Additive(..))
-- >>> import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- Dup (->)
-- ---------------------------------------------------------------------------

-- | Every type copies for free in a cartesian category (Fox's theorem).
--
-- >>> dup (42 :: Int)
-- (42,42)
-- >>> discard (42 :: Int)
-- ()
instance Dup (->) a where
  dup a = (a, a)
  {-# INLINE dup #-}
  discard _ = ()
  {-# INLINE discard #-}

-- ---------------------------------------------------------------------------
-- Additive (->)
-- ---------------------------------------------------------------------------

-- | Addition via 'Num'.  For types without 'Num', use a 'Semigroup'/'Monoid'
-- instance.
--
-- >>> plus ((3 :: Int), (4 :: Int))
-- 7
-- >>> zero () :: Int
-- 0
instance Num a => Additive (->) a where
  plus = uncurry (+)
  {-# INLINE plus #-}
  zero _ = 0
  {-# INLINE zero #-}

-- ---------------------------------------------------------------------------
-- MonoidalP — parallel composition for product categories
-- ---------------------------------------------------------------------------

-- | A monoidal product on base arrows.
--
-- 'parA' composes two arrows in parallel (disjoint wires — no interaction,
-- so no 'Additive' constraint).  'swapA' is the symmetric braiding.
--
-- Laws: 'parA' is a bifunctor, 'swapA' is involutive, and they satisfy
-- the symmetric monoidal coherence conditions.
class Category arr => MonoidalP arr where
  -- | Parallel composition: run two arrows on disjoint wires.
  --
  -- >>> parA ((+1) :: Int -> Int) ((*2) :: Int -> Int) (3, 4)
  -- (4,8)
  parA :: arr a b -> arr c d -> arr (a, c) (b, d)

  -- | Symmetric braiding.
  --
  -- >>> swapA (3, 4) :: (Int, Int)
  -- (4,3)
  swapA :: arr (a, b) (b, a)

instance MonoidalP (->) where
  parA f g (a, c) = (f a, g c)
  {-# INLINE parA #-}
  swapA (a, b) = (b, a)
  {-# INLINE swapA #-}
