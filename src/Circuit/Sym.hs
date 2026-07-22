{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free symmetric monoidal category over a base arrow.
--
-- 'Sym' extends the free category (@Circuit.Free.Free@) with explicit
-- monoidal product ('Par') and symmetry ('Swap') syntax.  It is the
-- intermediate layer between @Circuit.Free.Free@ and @Circuit.Net.Net@:
--
-- @
-- Free = Lift + Compose
-- Sym  = Free + Par + Swap
-- Net  = Sym + Knot + Copy + Discard + Plus + Zero
-- @
--
-- The tensor is fixed to @(,)@, matching 'Circuit.Tensor.Action'.
module Circuit.Sym
  ( Sym (..),

    -- * Free monoidal constraint
    FreeSym,
  )
where

import Circuit.Category (Category (..), Discrete (..), ObDict (..), withObDict, (.>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Layer (Layer (..), run, (:~>))
import Circuit.Tensor (Action (..), Tensor (..))
import Prelude hiding (id, (.))

-- $setup
-- >> import Circuit.Layer (run)
-- >> import Circuit.Tensor (Action (..), Tensor (..))
-- >> import Prelude hiding (id, (.))

-- | The free symmetric monoidal category over a base arrow @arr@.
--
-- Four constructors:
--
--   * 'Lift' — embed a base arrow.
--   * 'Compose' — sequential composition.
--   * 'Par' — tensor product of morphisms (parallel composition).
--   * 'Swap' — symmetry / braiding.
data Sym arr a b where
  -- | Embed a base arrow.
  Lift :: arr a b -> Sym arr a b
  -- | Sequential composition.
  --
  -- The 'Ob' constraint on the intermediate object @b@ is carried in the
  -- constructor so folding does not need a 'Discrete' base.
  Compose :: (Ob arr b) => Sym arr b c -> Sym arr a b -> Sym arr a c
  -- | Tensor product of morphisms (parallel composition on disjoint wires).
  Par :: Sym arr a b -> Sym arr c d -> Sym arr (a, c) (b, d)
  -- | Symmetric braiding.
  Swap :: Sym arr (a, b) (b, a)

-- | 'Sym' is a category.
instance (Category arr) => Category (Sym arr) where
  type Ob (Sym arr) a = Ob arr a
  id = Lift id
  (.) = Compose

-- | A discrete base yields a discrete free monoidal category.
instance (Category arr, Discrete arr) => Discrete (Sym arr) where
  withOb @a x = withOb @arr @a x

-- | 'Sym' has a tensor structure whose tensor is @(,)@.
--
-- This is the syntactic instance: 'Par' is its own interpretation.
-- The unitors require the base arrow to have its own cartesian unitors.
instance (Tensor (,) arr) => Tensor (,) (Sym arr) where
  par = Par
  unitl = Lift unitl
  unitl' = Lift unitl'
  unitr = Lift unitr
  unitr' = Lift unitr'

-- | 'Sym' has a symmetric braiding.
--
-- This is the syntactic instance: 'Swap' is its own interpretation.
instance (Tensor (,) arr) => Action (,) (Sym arr) where
  swap = Swap

-- | Lift the 'Channel' structure through 'Sym'.
instance (Category arr, Channel t arr) => Channel t (Sym arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  slide = Lift slide
  withTensorOb ::
    forall a b r.
    ObDict (Sym arr) a ->
    ObDict (Sym arr) b ->
    ((Ob (Sym arr) (t a b)) => r) ->
    r
  withTensorOb (dA :: ObDict (Sym arr) a) (dB :: ObDict (Sym arr) b) k =
    withObDict dA $
      withObDict dB $
        withTensorOb @t @arr (ObDict :: ObDict arr a) (ObDict :: ObDict arr b) k

-- | 'Action' plus 'Discrete' so free 'Sym' can fold intermediate objects.
--
-- Sequential structure is folded with the target's category composition.
class (Action (,) arr, Discrete arr) => FreeSym arr

instance (Action (,) arr, Discrete arr) => FreeSym arr

instance Layer Sym where
  type Law Sym arr' = FreeSym arr'
  type Run Sym arr = (Action (,) arr, Discrete arr)
  type Bind Sym arr = Discrete arr
  unit = Lift
  bind ::
    forall arr' arr a b.
    (Law Sym arr', Bind Sym arr, Ob arr a, Ob arr b, Ob arr' a, Ob arr' b) =>
    (forall s. ObDict arr s -> ObDict arr' s) ->
    (arr :~> arr') ->
    Sym arr a b ->
    arr' a b
  bind _phi h (Lift f) = h f
  bind phi h (Compose @_ @b1 g f) = withObDict (phi (ObDict :: ObDict arr b1)) (bind phi h g . bind phi h f)
  bind phi h (Par (f :: Sym arr a1 b1) (g :: Sym arr c d)) =
    let dA1 = obDict :: ObDict arr a1
        dB1 = obDict :: ObDict arr b1
        dC = obDict :: ObDict arr c
        dD = obDict :: ObDict arr d
     in withObDict dA1 $
          withObDict dB1 $
            withObDict dC $
              withObDict dD $
                withObDict (phi dA1) $
                  withObDict (phi dB1) $
                    withObDict (phi dC) $
                      withObDict (phi dD) $
                        withOb @arr' @(a1, c) $
                          withOb @arr' @(b1, d) $
                            par (bind phi h f) (bind phi h g)
  bind _phi _ Swap = swap

-- | Lift the 'Strength' structure through 'Sym'.
instance (Strength t arr, Action (,) arr, Discrete arr) => Strength t (Sym arr) where
  strength = Lift . strength . run
  withStrengthOb ::
    forall a b c r.
    ObDict (Sym arr) a ->
    ObDict (Sym arr) b ->
    ObDict (Sym arr) c ->
    ((Ob (Sym arr) (t a b), Ob (Sym arr) (t a c)) => r) ->
    r
  withStrengthOb (dA :: ObDict (Sym arr) a) (dB :: ObDict (Sym arr) b) (dC :: ObDict (Sym arr) c) k =
    withObDict dA $
      withObDict dB $
        withObDict dC $
          withStrengthOb @t @arr (ObDict :: ObDict arr a) (ObDict :: ObDict arr b) (ObDict :: ObDict arr c) k

-- | Lift the 'Traced' structure through 'Sym'.
--
-- Loop bodies are 'run' into the base arrow before tracing, just as for
-- @Free@.
instance (Traced t arr, Action (,) arr, Discrete arr) => Traced t (Sym arr) where
  trace = Lift . trace . run
