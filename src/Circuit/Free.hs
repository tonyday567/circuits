{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
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

import Circuit.Category (Category (..), Discrete (..), ObDict (..), withObDict)
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Layer (Layer (..), (:~>))
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
  --
  -- The 'Ob' constraint on the intermediate object @b@ is carried in the
  -- constructor so folding does not need a 'Discrete' base.
  Compose :: (Ob arr b) => Free arr b c -> Free arr a b -> Free arr a c

instance (Category arr) => Category (Free arr) where
  type Ob (Free arr) a = Ob arr a
  id = Lift id
  (.) = Compose

-- | A discrete base yields a discrete free category.
instance (Discrete arr) => Discrete (Free arr) where
  withOb @a x = withOb @arr @a x

-- | Layer instance for the free category.
--
-- 'Compose' carries the intermediate 'Ob' evidence of the /source/
-- category, but folding into a target category @arr'@ still needs to
-- manufacture the corresponding 'Ob arr' b' evidence.  That is exactly
-- what 'Discrete arr'' provides, so 'Law' is 'Discrete'.
instance Layer Free where
  type Law Free arr' = Discrete arr'
  type Run Free arr = (Category arr, Discrete arr)
  type Bind Free arr = ()
  unit = Lift
  bind :: forall arr' arr a b. (Law Free arr', Ob arr a, Ob arr b, Ob arr' a, Ob arr' b) => (forall s. ObDict arr s -> ObDict arr' s) -> (arr :~> arr') -> Free arr a b -> arr' a b
  bind _phi h (Lift f) = h f
  bind phi h (Compose @_ @b1 g f) = withObDict (phi (ObDict :: ObDict arr b1)) (bind phi h g . bind phi h f)

-- | Freeze a 'Free' category into its base arrow.
--
-- This is a synonym for 'run' @Free@.
--
-- >>> freeze (Lift (+1) :: Free (->) Int Int) 5
-- 6
freeze :: (Category arr, Ob arr a, Ob arr b) => Free arr a b -> arr a b
freeze (Lift f) = f
freeze (Compose g f) = freeze g . freeze f

-- | Lift the 'Channel' structure through 'Free'.
instance (Channel t arr) => Channel t (Free arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  slide = Lift slide
  withTensorOb ::
    forall a b r.
    ObDict (Free arr) a ->
    ObDict (Free arr) b ->
    ((Ob (Free arr) (t a b)) => r) ->
    r
  withTensorOb (dA :: ObDict (Free arr) a) (dB :: ObDict (Free arr) b) k =
    withObDict dA $
      withObDict dB $
        withTensorOb @t @arr (ObDict :: ObDict arr a) (ObDict :: ObDict arr b) k

-- | Lift the 'Strength' class through 'Free'.
--
-- A morphism is frozen before tensoring with the feedback channel.
instance (Strength t arr) => Strength t (Free arr) where
  strength = Lift . strength . freeze
  withStrengthOb ::
    forall a b c r.
    ObDict (Free arr) a ->
    ObDict (Free arr) b ->
    ObDict (Free arr) c ->
    ((Ob (Free arr) (t a b), Ob (Free arr) (t a c)) => r) ->
    r
  withStrengthOb (dA :: ObDict (Free arr) a) (dB :: ObDict (Free arr) b) (dC :: ObDict (Free arr) c) k =
    withObDict dA $
      withObDict dB $
        withObDict dC $
          withStrengthOb @t @arr (ObDict :: ObDict arr a) (ObDict :: ObDict arr b) (ObDict :: ObDict arr c) k

-- | Lift the 'Traced' class through 'Free'.
--
-- A loop body in @Free arr@ is frozen before calling the base 'trace'.
instance (Traced t arr) => Traced t (Free arr) where
  trace = Lift . trace . freeze
