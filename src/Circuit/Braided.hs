{-# LANGUAGE CPP #-}

-- | Canonical braidings for traced monoidal categories.
--
-- The standard tensors @(,)@ and @Either@ are symmetric monoidal,
-- each carrying a canonical braid.  This module exposes them as a
-- type class and provides the default 'ambientB' combinator.
module Circuit.Braided
  ( -- * Braided tensors
    Braided (..),

    -- * Ambient threading with canonical braid
    ambient,
  )
where

#ifdef __GLASGOW_HASKELL__
import Data.Profunctor (Profunctor)
#else
import Circuit.Classes (Profunctor)
#endif

import Circuit.Circuit (Circuit, ambientBy)
import Circuit.Traced (Trace)

#ifdef __GLASGOW_HASKELL__
import Data.Bifunctor (Bifunctor (..))
#else
import Circuit.Classes (Bifunctor (..))
#endif

-- | A symmetric braiding for a bifunctor tensor.
--
-- The braid swaps a wire past a nested pair:
--
-- @
--   t x (t y z)  ->  t y (t x z)
-- @
--
-- For @(,)@ this is the cartesian slide.  For @Either@ it is the
-- coproduct slide.  Both are derived from the associator and swap.
class (Bifunctor t) => Braided t where
  braid :: t x (t y z) -> t y (t x z)

-- | Cartesian slide: @(x, (y, z)) -> (y, (x, z))@.
instance Braided (,) where
  braid (x, (y, z)) = (y, (x, z))

-- | Coproduct slide.
instance Braided Either where
  braid (Left x) = Right (Left x)
  braid (Right (Left y)) = Left y
  braid (Right (Right z)) = Right (Right z)

-- | Thread a state wire through a circuit using the canonical braid.
--
-- This is 'ambientBy' with the braid supplied by the 'Braided' instance.
ambient ::
  (Profunctor arr, Trace arr t, Braided t) =>
  Circuit arr t a b -> Circuit arr t (t s a) (t s b)
ambient = ambientBy braid
