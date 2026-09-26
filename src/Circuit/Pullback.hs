{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

module Circuit.Pullback
  ( Pullback (..),
    evalPullback,
  )
where

import Circuit.Bimonoid (Copy (..), Discard (..), Merge (..), Zero (..))
import Circuit.Category (Category (..))
import Circuit.Net (Net)
import Circuit.Syntax (run)
import Circuit.Tensor (Action (..), SemiTensor (..), Tensor, Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Bifunctor
import Prelude hiding (id, (.))

newtype Pullback b a = Pullback
  { runPullback :: b -> a
  }

instance Category Pullback where
  id = Pullback id
  Pullback g . Pullback f = Pullback (\x -> g (f x))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance Unital (,) Pullback where
  unitl = Pullback snd
  {-# INLINE unitl #-}
  unitl' = Pullback ((),)
  {-# INLINE unitl' #-}
  unitr = Pullback fst
  {-# INLINE unitr #-}
  unitr' = Pullback (,())
  {-# INLINE unitr' #-}

instance SemiTensor (,) Pullback where
  tensor (Pullback f) (Pullback g) = Pullback (Data.Bifunctor.bimap f g)
  {-# INLINE tensor #-}

instance Tensor (,) Pullback

instance Action (,) Pullback where
  braid = Pullback (\(b, a) -> (a, b))
  {-# INLINE braid #-}

instance Strength (,) Pullback where
  strength (Pullback f) = Pullback (\(a, b) -> (a, f b))
  {-# INLINE strength #-}

instance Yank (,) Pullback where
  yank (Pullback f) = Pullback $ \dc ->
    let ~(dx, db) = f (dx, dc)
     in db
  {-# INLINE yank #-}

instance Copy Pullback a where
  copy = Pullback (\b -> (b, b))
  {-# INLINE copy #-}

instance Discard Pullback a where
  discard = Pullback (const ())
  {-# INLINE discard #-}

instance (Merge (->) a) => Merge Pullback a where
  plus = Pullback (\(b1, b2) -> plus (b1, b2))
  {-# INLINE plus #-}

instance (Zero (->) a) => Zero Pullback a where
  zero = Pullback (\() -> zero ())
  {-# INLINE zero #-}

evalPullback :: Net (,) Pullback b a -> b -> a
evalPullback n = runPullback (run n)
{-# INLINE evalPullback #-}

instance Assoc (,) Pullback where
  assoc = Pullback (\((s, s'), x) -> (s, (s', x)))
  assoc' = Pullback (\(s, (s', x)) -> ((s, s'), x))

instance Slide (,) Pullback where
  slide = Pullback (\(s, (s', x)) -> (s', (s, x)))
