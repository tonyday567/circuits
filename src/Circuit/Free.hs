{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The free category over a base arrow — just 'Lift' and 'Compose'.
--
-- Free is Trace without the knot constructor.  Where Trace is the free /traced/
-- category, Free is the free category.  The universal fold out of Free
-- is 'run'; it is also 'bind' of the 'Layer' instance.
module Circuit.Free
  ( Free (..),
    freeze,
  )
where

import Circuit.Layer (Layer (..), run)
import Circuit.Monoidal.Category (Monoidal (..))
import Circuit.Trace (Traced (..))
import Prelude hiding (id, (.))

#ifdef __GLASGOW_HASKELL__
import Control.Category
#else
import Circuit.Classes
#endif

-- $setup
-- >>> import Circuit.Free
-- >>> import Circuit.Layer (hmap, run)
-- >>> import Prelude hiding (id, (.))

-- | The free category over a base arrow @arr@.
--
-- Two constructors:
--
--   * 'Lift' — embed a base arrow.
--   * 'Compose' — sequential composition.
--
-- >>> run (Lift (+1) :: Free (->) Int Int) 5
-- 6
data Free arr a b where
  -- | Embed a base arrow.
  Lift :: arr a b -> Free arr a b
  -- | Sequential composition.
  Compose :: Free arr b c -> Free arr a b -> Free arr a c

instance (Category arr) => Category (Free arr) where
  id = Lift id
  (.) = Compose

-- | Free category over a graph.
instance Layer Free where
  type Law Free arr' = Category arr'
  unit = Lift
  bind h (Lift f) = h f
  bind h (Compose g f) = bind h g . bind h f

-- | Freeze a 'Free' category into its base arrow.
--
-- This is the concrete specialization of 'run' @Free@.
--
-- >>> freeze (Lift (+1) :: Free (->) Int Int) 5
-- 6
freeze :: (Category arr) => Free arr a b -> arr a b
freeze (Lift f) = f
freeze (Compose g f) = freeze g . freeze f

-- | Lift the 'Monoidal' structure through 'Free'.
instance (Monoidal t arr) => Monoidal t (Free arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  braid = Lift braid

-- | Lift the 'Traced' class through 'Free'.
--
-- A loop body in @Free arr@ is frozen before calling the base 'trace'.
instance (Category arr, Traced t arr) => Traced t (Free arr) where
  trace = Lift . trace . freeze
  untrace = Lift . untrace . freeze
