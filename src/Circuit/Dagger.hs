{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free dagger category over a base arrow.
--
-- A 'Dagger' value pairs a forward arrow with a backward arrow.
-- Composition is covariant forward and contravariant backward;
-- 'transpose' swaps the two directions.
--
-- The structural rules ('Copy' / 'Discard' / 'Merge' / 'Zero' and their
-- tensor-generic forms) live in "Circuit.Bimonoid".  This module only
-- provides the free dagger construction and the way it dualises a bimonoid:
-- forward copy corresponds to backward merge, forward discard to backward
-- zero, and vice versa.
module Circuit.Dagger
  ( -- * Free dagger category
    Dagger (..),
    transpose,
  )
where

import Circuit.Bimonoid
  ( Copy (..),
    CopyT (..),
    Discard (..),
    DiscardT (..),
    Merge (..),
    MergeT (..),
    Zero (..),
    ZeroT (..),
  )
import Circuit.Category (Category (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Circuit.Tensor (Action (..), Tensor (..), Unital (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Dagger
-- >>> import Circuit.Bimonoid
-- >>> import Circuit.Tensor (Action (..), Tensor (..), Unital (..))
-- >>> import Circuit.Traced (Yank (..))
-- >>> import Circuit.Category (Category (..), (.>))
-- >>> import Prelude hiding (id, (.))

-- | The free dagger category over a base arrow.
--
-- @Dagger arr a b@ is a pair of arrows @arr a b@ (forward) and
-- @arr b a@ (backward).  Composition is covariant forward, contravariant
-- backward: @Dagger f g . Dagger f' g' = Dagger (f . f') (g' . g)@.
--
-- >>> let d = Dagger (+1) (subtract 1) :: Dagger (->) Int Int
-- >>> front d 5
-- 6
-- >>> back d 6
-- 5
data Dagger arr a b = Dagger
  { -- | The forward direction.
    front :: arr a b,
    -- | The backward direction.
    back :: arr b a
  }

-- | The dagger operation: braid forward and backward.
--
-- Involutive: @transpose . transpose = id@.
transpose :: Dagger arr a b -> Dagger arr b a
transpose (Dagger f g) = Dagger g f

instance (Category arr) => Category (Dagger arr) where
  id = Dagger id id
  {-# INLINE id #-}

  Dagger f g . Dagger f' g' = Dagger (f . f') (g' . g)
  {-# INLINE (.) #-}

instance (Strength t arr) => Strength t (Dagger arr) where
  strength (Dagger f g) = Dagger (strength f) (strength g)
  {-# INLINE strength #-}

instance (Yank t arr) => Yank t (Dagger arr) where
  yank (Dagger f g) = Dagger (yank f) (yank g)
  {-# INLINE yank #-}

-- | Forward copy, backward add — the bimonoid self-duality.
--
-- The interlock is the point to notice: 'Copy' on the dagger requires
-- 'Merge' on the base.  The comonoid and monoid cannot be granted
-- separately in this construction; @Dagger (FinRel k)@ is where that
-- collapse becomes observable (see the @circuits-axioma@ oracle).
instance (Copy arr a, Merge arr a) => Copy (Dagger arr) a where
  copy = Dagger copy plus
  {-# INLINE copy #-}

instance (Discard arr a, Zero arr a) => Discard (Dagger arr) a where
  discard = Dagger discard zero
  {-# INLINE discard #-}

-- | Forward add, backward copy.
instance (Merge arr a, Copy arr a) => Merge (Dagger arr) a where
  plus = Dagger plus copy
  {-# INLINE plus #-}

instance (Zero arr a, Discard arr a) => Zero (Dagger arr) a where
  zero = Dagger zero discard
  {-# INLINE zero #-}

-- | Tensor-generic bimonoid interlock through @Dagger@.
--
-- These instances mirror the cartesian ones above, but work for any wiring
-- tensor @t@.  They are the missing lemma that makes 'Circuit.Net.mirror'
-- total: a 'Circuit.Net.Net' over 'Dagger arr' can transpose its bimonoid rows because
-- the dagger swaps the tensor-comonoid and tensor-monoid dictionaries.
--
-- >>> let d = copyT @(,) @(Dagger (->)) @Int :: Dagger (->) Int (Int, Int)
-- >>> front d 5
-- (5,5)
-- >>> back d (2, 3)
-- 5
instance {-# INCOHERENT #-} (CopyT t arr a, MergeT t arr a) => CopyT t (Dagger arr) a where
  copyT = Dagger (copyT @t) (plusT @t)
  {-# INLINE copyT #-}

instance {-# INCOHERENT #-} (DiscardT t arr a, ZeroT t arr a) => DiscardT t (Dagger arr) a where
  discardT = Dagger (discardT @t) (zeroT @t)
  {-# INLINE discardT #-}

instance {-# INCOHERENT #-} (MergeT t arr a, CopyT t arr a) => MergeT t (Dagger arr) a where
  plusT = Dagger (plusT @t) (copyT @t)
  {-# INLINE plusT #-}

instance {-# INCOHERENT #-} (ZeroT t arr a, DiscardT t arr a) => ZeroT t (Dagger arr) a where
  zeroT = Dagger (zeroT @t) (discardT @t)
  {-# INLINE zeroT #-}

instance (Unital t arr) => Unital t (Dagger arr) where
  unitl = Dagger unitl unitl'
  {-# INLINE unitl #-}
  unitl' = Dagger unitl' unitl
  {-# INLINE unitl' #-}
  unitr = Dagger unitr unitr'
  {-# INLINE unitr #-}
  unitr' = Dagger unitr' unitr
  {-# INLINE unitr' #-}

instance (Tensor t arr) => Tensor t (Dagger arr) where
  tensor (Dagger f g) (Dagger f' g') = Dagger (tensor f f') (tensor g g')
  {-# INLINE tensor #-}

instance (Action t arr) => Action t (Dagger arr) where
  braid = Dagger braid braid
  {-# INLINE braid #-}

instance (Assoc t arr) => Assoc t (Dagger arr) where
  assoc = Dagger assoc assoc'
  assoc' = Dagger assoc' assoc

instance (Slide t arr) => Slide t (Dagger arr) where
  slide = Dagger slide slide
