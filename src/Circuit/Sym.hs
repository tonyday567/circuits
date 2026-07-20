{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free symmetric monoidal category over a base arrow.
--
-- 'Sym' extends the free category ('Circuit.Free.Free') with explicit
-- monoidal product ('Par') and symmetry ('Swap') syntax.  It is the
-- intermediate layer between 'Circuit.Free.Free' and 'Circuit.Net.Net':
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
    freeToMon,
    monTranspose,

    -- * Free monoidal constraint
    FreeSym,
  )
where

import Circuit.Category (Category (..), Discrete (..), (>>>))
import Circuit.Dagger qualified as Dg
import Circuit.Free (Free)
import Circuit.Free qualified as Fr
import Circuit.Layer (Layer (..), run, (:~>))
import Circuit.Channel (Channel (..))
import Circuit.Tensor (Action (..), Tensor (..))
import Circuit.Loop (Strength (..), Traced (..))
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
  Compose :: Ob arr b => Sym arr b c -> Sym arr a b -> Sym arr a c
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
  run :: forall arr a b. (Run Sym arr, Ob arr a, Ob arr b) => Sym arr a b -> arr a b
  run (Lift f) = f
  run (Compose g f) = run g . run f
  run (Par (f :: Sym arr a1 b1) (g :: Sym arr c d)) =
    withOb @arr @a1 $
      withOb @arr @b1 $
        withOb @arr @c $
          withOb @arr @d $
            par (run f) (run g)
  run Swap = swap
  bind :: forall arr' arr a b. (Law Sym arr', Bind Sym arr, Ob arr a, Ob arr b, Ob arr' a, Ob arr' b) => (arr :~> arr') -> Sym arr a b -> arr' a b
  bind h (Lift f) = h f
  bind h (Compose @_ @b1 g f) = withOb @arr' @b1 (bind h g . bind h f)
  bind h (Par (f :: Sym arr a1 b1) (g :: Sym arr c d)) =
    withOb @arr @a1 $
      withOb @arr @b1 $
        withOb @arr @c $
          withOb @arr @d $
            withOb @arr' @a1 $
              withOb @arr' @b1 $
                withOb @arr' @c $
                  withOb @arr' @d $
                    par (bind h f) (bind h g)
  bind _ Swap = swap

-- | Include a 'Free' category into 'Sym'.
--
-- 'Free' is the sequential fragment of 'Sym'; this is the constructor-to-
-- constructor injection @Free ↪ Sym@.
--
-- >>> let f = Fr.Compose (Fr.Lift (+1)) (Fr.Lift (*2)) :: Fr.Free (->) Int Int
-- >>> run (freeToMon f) 5
-- 11
freeToMon :: Free arr a b -> Sym arr a b
freeToMon (Fr.Lift f) = Lift f
freeToMon (Fr.Compose g f) = Compose (freeToMon g) (freeToMon f)

-- | 'Sym' over a 'Dg.Dagger' base is self-dual: reverse 'Compose',
-- transpose 'Par' componentwise, and leave 'Swap' fixed.
--
-- Law: @monTranspose . monTranspose = id@.
--
-- >>> let m = Lift (Dg.Dagger (*2) (\x -> x `div` 2)) `Compose` Lift (Dg.Dagger (+1) (subtract 1)) :: Sym (Dg.Dagger (->)) Int Int
-- >>> Dg.front (run (monTranspose m)) 10
-- 4
monTranspose ::
  Sym (Dg.Dagger arr) a b ->
  Sym (Dg.Dagger arr) b a
monTranspose (Lift (Dg.Dagger f g)) = Lift (Dg.Dagger g f)
monTranspose (Compose g f) = Compose (monTranspose f) (monTranspose g)
monTranspose (Par f g) = Par (monTranspose f) (monTranspose g)
monTranspose Swap = Swap

-- | Lift the 'Strength' structure through 'Sym'.
instance (Strength t arr, Action (,) arr, Discrete arr) => Strength t (Sym arr) where
  strength = Lift . strength . run

-- | Lift the 'Traced' structure through 'Sym'.
--
-- Loop bodies are 'run' into the base arrow before tracing, just as for
-- 'Free'.
instance (Traced t arr, Action (,) arr, Discrete arr) => Traced t (Sym arr) where
  trace = Lift . trace . run
