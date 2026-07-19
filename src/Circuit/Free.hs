{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The free category over a base arrow.
--
-- The two constructors are 'Lift', which embeds a base arrow, and
-- 'Compose', which sequences two free morphisms.  The universal fold out
-- of 'Free' is 'run'.
module Circuit.Free
  ( Free (..),
    freeze,
  )
where

import Circuit.Category (Category (..), Discrete (..))
import Circuit.Layer (Layer (..), run)
import Circuit.Monoidal (Monoidal (..))
import Circuit.Trace (Traced (..), compD)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Free
-- >>> import Circuit.Layer (run)
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
-- >>> run (Compose (Lift (+1)) (Lift (*2)) :: Free (->) Int Int) 5
-- 11
data Free arr a b where
  -- | Embed a base arrow.
  Lift :: arr a b -> Free arr a b
  -- | Sequential composition.
  Compose :: Free arr b c -> Free arr a b -> Free arr a c

instance (Category arr) => Category (Free arr) where
  type Ob (Free arr) a = Ob arr a
  id = Lift id
  (.) = Compose

-- | Layer instance for the free category.
--
-- 'Law' requires 'Discrete' so intermediate objects in 'Compose' can
-- discharge 'Ob' when folding.
instance Layer Free where
  type Law Free arr' = Discrete arr'
  unit = Lift
  bind h (Lift f) = h f
  bind h (Compose g f) = bind h g `compD` bind h f

-- | Freeze a 'Free' category into its base arrow.
--
-- This is the concrete specialization of 'run' @Free@.
--
-- >>> freeze (Lift (+1) :: Free (->) Int Int) 5
-- 6
freeze :: (Discrete arr) => Free arr a b -> arr a b
freeze (Lift f) = f
freeze (Compose g f) = freeze g `compD` freeze f

-- | Lift the 'Monoidal' structure through 'Free'.
instance (Monoidal t arr) => Monoidal t (Free arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  braid = Lift braid

-- | Lift the 'Traced' class through 'Free'.
--
-- A loop body in @Free arr@ is frozen before calling the base 'trace'.
instance (Discrete arr, Traced t arr) => Traced t (Free arr) where
  trace = Lift . trace . freeze
  untrace = Lift . untrace . freeze
