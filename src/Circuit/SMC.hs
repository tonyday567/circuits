{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free symmetric monoidal category over a base arrow.
--
-- 'SMC' extends the free category ('Free') with explicit
-- monoidal product ('SMCPar') and symmetry ('SMCSwap') syntax.  It is the
-- intermediate layer between 'Free' and 'Net':
--
-- @
-- Free = Lift + Compose
-- SMC  = Free + Par + Swap
-- Net  = SMC + Copy + Discard + Plus + Zero
-- @
--
-- The tensor is the wiring tensor @w@, matching 'Circuit.Tensor.Action'.
module Circuit.SMC
  ( -- * SMC
    SMC (..),
    FreeSMC,
  )
where

import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Layer (Layer (..), run, (:~>))
import Circuit.Tensor (Action (..), Tensor (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- | The free symmetric monoidal category over a base arrow.
--
-- Four constructors:
--
--   * 'SMCLift' — embed a base arrow.
--   * 'SMCCompose' — sequential composition.
--   * 'SMCPar' — tensor product of morphisms (parallel composition).
--   * 'SMCSwap' — symmetry / braiding.
data SMC (w :: Type -> Type -> Type) arr a b where
  -- | Embed a base arrow.
  SMCLift :: arr a b -> SMC w arr a b
  -- | Sequential composition.
  SMCCompose :: SMC w arr b c -> SMC w arr a b -> SMC w arr a c
  -- | Tensor product of morphisms (parallel composition on disjoint wires).
  SMCPar ::
    SMC w arr a b ->
    SMC w arr c d ->
    SMC w arr (w a c) (w b d)
  -- | Symmetric braiding.
  SMCSwap :: SMC w arr (w a b) (w b a)

-- | 'SMC' is a category.
instance (Category arr) => Category (SMC w arr) where
  id = SMCLift id
  (.) = SMCCompose

-- | 'SMC' has a tensor structure over @w@.
--
-- This is the syntactic instance: 'SMCPar' is its own interpretation.
-- The unitors require the base arrow to have its own @w@-tensor unitors.
instance (Tensor w arr) => Tensor w (SMC w arr) where
  par = SMCPar
  unitl = SMCLift unitl
  unitl' = SMCLift unitl'
  unitr = SMCLift unitr
  unitr' = SMCLift unitr'

-- | 'SMC' has a symmetric braiding over @w@.
--
-- This is the syntactic instance: 'SMCSwap' is its own interpretation.
instance (Action w arr) => Action w (SMC w arr) where
  swap = SMCSwap

-- | Lift the 'Channel' structure through 'SMC'.
instance (Category arr, Channel t arr) => Channel t (SMC w arr) where
  assoc = SMCLift assoc
  assoc' = SMCLift assoc'
  slide = SMCLift slide

-- | 'Action' — free 'SMC' fold carries its own structure.
--
-- Sequential structure is folded with the target's category composition.
class (Action w arr) => FreeSMC w arr

instance (Action w arr) => FreeSMC w arr

instance Layer (SMC w) where
  type Law (SMC w) arr' = FreeSMC w arr'
  type Run (SMC w) arr = Action w arr
  type Bind (SMC w) arr = ()
  unit = SMCLift
  bind ::
    forall arr' arr a b.
    (Law (SMC w) arr') =>
    (arr :~> arr') ->
    SMC w arr a b ->
    arr' a b
  bind h (SMCLift f) = h f
  bind h (SMCCompose (g :: SMC w arr b1 c) (f :: SMC w arr a b1)) =
    bind h g . bind h f
  bind h (SMCPar (f :: SMC w arr a1 b1) (g :: SMC w arr c d)) =
    par (bind h f) (bind h g)
  bind _h SMCSwap = swap

-- | Lift the 'Strength' structure through 'SMC'.
instance (Strength t arr, Action w arr) => Strength t (SMC w arr) where
  strength = SMCLift . strength . run

-- | Lift the 'Traced' structure through 'SMC'.
--
-- Loop bodies are 'run' into the base arrow before tracing, just as for
-- 'Free'.
instance (Traced t arr, Action w arr) => Traced t (SMC w arr) where
  trace = SMCLift . trace . run
