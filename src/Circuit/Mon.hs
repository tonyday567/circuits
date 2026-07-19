{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free symmetric monoidal category over a base arrow.
--
-- 'Mon' extends the free category ('Circuit.Free.Free') with explicit
-- monoidal product ('Par') and symmetry ('Swap') syntax.  It is the
-- intermediate layer between 'Circuit.Free.Free' and 'Circuit.Net.Net':
--
-- @
-- Free = Lift + Compose
-- Mon  = Free + Par + Swap
-- Net  = Mon + Knot + Copy + Discard + Plus + Zero
-- @
--
-- The tensor is fixed to @(,)@, matching 'Circuit.Monoidal.Action'.
module Circuit.Mon
  ( Mon (..),
    freeToMon,
    monTranspose,
  )
where

import Circuit.Classes (Category (..), Discrete (..), (>>>))
import Circuit.Dagger qualified as Dg
import Circuit.Free (Free)
import Circuit.Free qualified as Fr
import Circuit.Layer (Layer (..), run)
import Circuit.Monoidal (Monoidal (..))
import Circuit.Tensor (Action (..), Tensor (..))
import Circuit.Trace (Traced (..), compD)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Dagger qualified as Dg
-- >>> import Circuit.Free qualified as Fr
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Tensor (Action (..), Tensor (..))
-- >>> import Prelude hiding (id, (.))

-- | The free symmetric monoidal category over a base arrow @arr@.
--
-- Four constructors:
--
--   * 'Arr' — embed a base arrow.
--   * 'Compose' — sequential composition.
--   * 'Par' — tensor product of morphisms (parallel composition).
--   * 'Swap' — symmetry / braiding.
data Mon arr a b where
  -- | Embed a base arrow.
  Arr :: arr a b -> Mon arr a b
  -- | Sequential composition.
  Compose :: Mon arr b c -> Mon arr a b -> Mon arr a c
  -- | Tensor product of morphisms (parallel composition on disjoint wires).
  Par :: Mon arr a b -> Mon arr c d -> Mon arr (a, c) (b, d)
  -- | Symmetric braiding.
  Swap :: Mon arr (a, b) (b, a)

-- | 'Mon' is a category.
instance (Category arr) => Category (Mon arr) where
  type Ob (Mon arr) a = Ob arr a
  id = Arr id
  (.) = Compose

-- | Free monoidal syntax over functions is discrete (Ob reduces to @()@).
instance Discrete (Mon (->)) where
  withOb x = x

-- | 'Mon' has a tensor structure whose tensor is @(,)@.
--
-- This is the syntactic instance: 'Par' is its own interpretation.
-- The unitors require the base arrow to have its own cartesian unitors.
instance (Tensor (,) arr) => Tensor (,) (Mon arr) where
  par = Par
  unitl = Arr unitl
  unitl' = Arr unitl'
  unitr = Arr unitr
  unitr' = Arr unitr'

-- | 'Mon' has a symmetric braiding.
--
-- This is the syntactic instance: 'Swap' is its own interpretation.
instance (Tensor (,) arr) => Action (,) (Mon arr) where
  swap = Swap

-- | Lift the 'Monoidal' structure through 'Mon'.
instance (Category arr, Monoidal t arr) => Monoidal t (Mon arr) where
  assoc = Arr assoc
  assoc' = Arr assoc'
  braid = Arr braid

-- | Free symmetric monoidal category.
--
-- The target only needs 'Action'; the sequential structure is folded
-- with the target's category composition.
-- | 'Action' plus 'Discrete' so free 'Mon' can fold intermediate objects.
class (Action (,) arr, Discrete arr) => FreeMon arr

instance (Action (,) arr, Discrete arr) => FreeMon arr

instance Layer Mon where
  type Law Mon arr' = FreeMon arr'
  unit = Arr
  bind h (Arr f) = h f
  bind h (Compose g f) = bind h g `compD` bind h f
  bind h (Par f g) = par (bind h f) (bind h g)
  bind _ Swap = swap

-- | Include a 'Free' category into 'Mon'.
--
-- 'Free' is the sequential fragment of 'Mon'; this is the constructor-to-
-- constructor injection @Free ↪ Mon@.
--
-- >>> let f = Fr.Compose (Fr.Lift (+1)) (Fr.Lift (*2)) :: Fr.Free (->) Int Int
-- >>> run (freeToMon f) 5
-- 11
freeToMon :: Free arr a b -> Mon arr a b
freeToMon (Fr.Lift f) = Arr f
freeToMon (Fr.Compose g f) = Compose (freeToMon g) (freeToMon f)

-- | 'Mon' over a 'Dg.Dagger' base is self-dual: reverse 'Compose',
-- transpose 'Par' componentwise, and leave 'Swap' fixed.
--
-- Law: @monTranspose . monTranspose = id@.
--
-- >>> let m = Arr (Dg.Dagger (*2) (\x -> x `div` 2)) `Compose` Arr (Dg.Dagger (+1) (subtract 1)) :: Mon (Dg.Dagger (->)) Int Int
-- >>> Dg.front (run (monTranspose m)) 10
-- 4
monTranspose ::
  Mon (Dg.Dagger arr) a b ->
  Mon (Dg.Dagger arr) b a
monTranspose (Arr (Dg.Dagger f g)) = Arr (Dg.Dagger g f)
monTranspose (Compose g f) = Compose (monTranspose f) (monTranspose g)
monTranspose (Par f g) = Par (monTranspose f) (monTranspose g)
monTranspose Swap = Swap

-- | Lift the 'Traced' structure through 'Mon'.
--
-- Loop bodies are 'run' into the base arrow before tracing, just as for
-- 'Free'.  This instance makes 'Mon' a valid target for 'Net.bind',
-- yielding the forgetful map @Net t arr -> Mon arr@ via @bind unit@.
instance (Traced t arr, Action (,) arr, Discrete arr) => Traced t (Mon arr) where
  trace = Arr . trace . run
  untrace = Arr . untrace . run
