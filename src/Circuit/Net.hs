{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-partial-fields #-}

-- | The free symmetric monoidal category with a bimonoid over a primitive set.
--
-- 'Net' extends 'SMC' with structural rows for the bimonoid
-- operations: copy, discard, addition, and zero.  Where 'C.Loop' keeps
-- only 'C.Lift' and 'C.Knot' in normal form, 'Net' keeps the wiring
-- inspectable — the difference between wiring you can read backwards and
-- wiring that has been melted into a single loop.
--
-- @
-- Free = Lift + Compose
-- SMC  = Free + Par + Swap
-- Net  = SMC + Copy + Discard + Plus + Zero
-- @
--
-- 'run' @Net@ interprets a 'Net' to a plain arrow.  'melt' interprets the
-- structural rows into the normal form of 'C.Loop'.
module Circuit.Net
  ( -- * Net
    Net (..),

    -- * Conversion
    widen,
    sift,

    -- * Interpretation
    melt,
  )
where

import Circuit.Category (Category (..), (.>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Dagger qualified as Dg
import Circuit.Layer (Layer (..), run, (:~>))
import Circuit.Layer qualified as Layer
import Circuit.Loop qualified as C
import Circuit.SMC (FreeSMC, SMC (..))
import Circuit.SMC qualified as SMC
import Circuit.Tensor (Action (..), Tensor (..), Unit)
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Dagger qualified as Dg
-- >>> import Circuit.Layer (bind, run, unit)
-- >>> import Circuit.Loop qualified as C
-- >>> import Circuit.Net
-- >>> import Circuit.SMC
-- >>> import Prelude hiding (id, (.))

-- | The free symmetric monoidal category with a bimonoid.
--
-- Four families of constructor:
--
--   * __Sequential__ — @Lift@, @Compose@.
--   * __Monoidal__ — 'Par', 'Swap' (parallel composition, braiding).
--   * __Copy/Discard__ — the comonoid on channel objects.
--   * __Plus/Zero__ — the monoid on channel objects.
--
-- 'Dg.CopyT' / 'Dg.DiscardT' and 'Dg.MergeT' / 'Dg.ZeroT' constraints ride
-- as dictionary arguments on the constructors that need them — laws in the
-- typeclass holes, evidence on the GADT rows.
--
-- The wiring monoidal structure ('Par' / 'Swap') is over a generic tensor
-- @w@.  Feedback is not represented inside 'Net'; it lives in 'C.Loop' and
-- is introduced only at the boundary by 'melt' or by interpreting into a
-- traced target category.
--
-- 'Net' extends 'C.Loop' inspectably for the wiring rows.  'melt'
-- collapses the structure to the normal form of 'C.Loop'.
data Net (w :: Type -> Type -> Type) arr a b where
  -- | Embed a base arrow.
  Lift :: arr a b -> Net w arr a b
  -- | Sequential composition.
  Compose :: Net w arr b c -> Net w arr a b -> Net w arr a c
  -- | Parallel composition (monoidal product over @w@).
  Par ::
    Net w arr a b ->
    Net w arr c d ->
    Net w arr (w a c) (w b d)
  -- | Symmetric braiding over @w@.
  Swap :: Net w arr (w a b) (w b a)
  -- | Copy: fan-out.  Requires 'Dg.CopyT' on the wiring tensor @w@.
  Copy ::
    (Dg.CopyT w arr a) =>
    Net w arr a (w a a)
  -- | Discard: erase.  Requires 'Dg.DiscardT' on the wiring tensor @w@.
  Discard ::
    (Dg.DiscardT w arr a) =>
    Net w arr a (Unit w)
  -- | Plus: fan-in.  Requires 'Dg.MergeT' on the wiring tensor @w@.
  Plus ::
    (Dg.MergeT w arr a) =>
    Net w arr (w a a) a
  -- | Zero: the neutral element.  Requires 'Dg.ZeroT' on the wiring tensor @w@.
  Zero ::
    (Dg.ZeroT w arr a) =>
    Net w arr (Unit w) a

-- | The 'Category' instance preserves inspectable wiring.
--
-- Composition uses the explicit @Compose@ constructor, so 'Copy',
-- 'Plus', and 'Par' stay visible.  'melt' collapses the structure when
-- the normal form is needed.
instance (Category arr) => Category (Net w arr) where
  id = Lift id
  g . f = Compose g f

-- | Include an 'SMC' circuit into 'Net' — constructor-to-constructor.
--
-- 'Net' duplicates the four rows of 'SMC' ('SMCLift', 'SMCCompose', 'SMCPar',
-- 'SMCSwap') so that structural wiring stays inspectable.  This is the
-- injection of the 'SMC' layer into the 'Net' layer.
--
-- >>> let m = SMCLift (+1) `SMCCompose` SMCLift (*2) :: SMC (,) (->) Int Int
-- >>> run (widen m :: Net (,) (->) Int Int) 5
-- 11
--
-- Coherence: 'sift' projects 'widen' back to the original 'SMC'.
--
-- >>> run (sift (widen m :: Net (,) (->) Int Int)) 5
-- 11
-- >>> run m 5
-- 11
--
-- Coherence: 'melt' agrees with the function fold on 'SMC' circuits.
--
-- >>> run (melt (widen m :: Net (,) (->) Int Int) :: C.Loop (,) (->) Int Int) 5
-- 11
-- >>> let h f = f
-- >>> (bind h m :: Int -> Int) 5
-- 11
--
-- Coherence: 'Net' folds through 'widen' match 'SMC' folds.
--
-- >>> let h f = f
-- >>> (bind h (widen m :: Net (,) (->) Int Int) :: Int -> Int) 5
-- 11
-- >>> (bind h m :: Int -> Int) 5
-- 11
--
-- Coherence: transposition commutes with 'widen'.
--
-- >>> let dm = SMCLift (Dg.Dagger (+1) (subtract 1)) `SMCCompose` SMCLift (Dg.Dagger (*2) (\x -> x `div` 2)) :: SMC (,) (Dg.Dagger (->)) Int Int
-- >>> Dg.front (Dg.transpose (run dm)) 10
-- 4
-- >>> Dg.front (Dg.transpose (run (widen dm :: Net (,) (Dg.Dagger (->)) Int Int))) 10
-- 4
widen :: SMC w arr a b -> Net w arr a b
widen (SMCLift f) = Lift f
widen (SMCCompose g f) = Compose (widen g) (widen f)
widen (SMCPar f g) = Par (widen f) (widen g)
widen SMCSwap = Swap

-- | Forget the bimonoid rows of a 'Net', keeping only the 'SMC' wiring.
--
-- 'sift' collapses the bimonoid rows into 'SMCLift' while leaving
-- @Compose@, 'Par', and 'Swap' inspectable. Together with 'widen'
-- it gives the adjunction between 'SMC' and 'Net'.
-- Note the converse does not hold: @widen . sift ≠ id@ because 'sift'
-- forgets bimonoid structure.
sift ::
  forall w arr a b.
  (Action w arr) =>
  Net w arr a b ->
  SMC w arr a b
sift (Lift f) = SMCLift f
sift (Compose g f) = SMCCompose (sift g) (sift f)
sift (Par f g) = SMCPar (sift f) (sift g)
sift Swap = SMCSwap
sift Copy = SMCLift (Dg.copyT @w)
sift Discard = SMCLift (Dg.discardT @w)
sift Plus = SMCLift (Dg.plusT @w)
sift Zero = SMCLift (Dg.zeroT @w)

-- | Melt the structural rows of a 'Net' into the normal form of 'C.Loop'.
--
-- The interpretation from the free symmetric monoidal category with
-- bimonoid to the free traced monoidal category.  Structural rows ('Par',
-- 'Copy', 'Plus', etc.) become opaque base-arrow operations wrapped in
-- 'C.Lift'; @Compose@ uses the 'Category' instance of 'C.Loop'.
--
-- @'run' @Net = 'run' . 'melt'@.
--
-- >>> run (melt (Lift (+1) :: Net (,) (->) Int Int) :: C.Loop (,) (->) Int Int) 5
-- 6
melt ::
  forall w t arr a b.
  (Traced t arr, Action w arr) =>
  Net w arr a b ->
  C.Loop t arr a b
melt (Lift f) = C.Lift f
melt (Compose g f) = melt g . melt f
melt (Par f g) = par (melt f) (melt g)
melt Swap = C.Lift swap
melt Copy = C.Lift (Dg.copyT @w)
melt Discard = C.Lift (Dg.discardT @w)
melt Plus = C.Lift (Dg.plusT @w)
melt Zero = C.Lift (Dg.zeroT @w)

-- | Free symmetric monoidal category with a bimonoid.
--
-- Structural rows are interpreted in the target category: parallel
-- composition uses 'par', braiding uses 'swap', and the bimonoid
-- generators are the images under @h@ of the source dictionaries carried
-- by the 'Copy', 'Discard', 'Plus', and 'Zero' constructors.
--
-- [Conditional] 'bind' @h@ interprets bimonoid generators as images under
-- @h@ of the source arrow's dictionaries.  This is the free-PROP fold
-- only when @h@ is a bimonoid homomorphism (automatic for the generator
-- embedding, but must be verified for custom @h@).
instance Layer (Net w) where
  type Law (Net w) arr' = FreeSMC w arr'
  type Run (Net w) arr = Action w arr
  type Bind (Net w) arr = ()
  unit = Lift
  bind ::
    forall arr' arr a b.
    (Law (Net w) arr') =>
    (arr :~> arr') ->
    Net w arr a b ->
    arr' a b
  bind h (Lift f) = h f
  bind h (Compose (g :: Net w arr b1 c) (f :: Net w arr a b1)) =
    bind h g . bind h f
  bind h (Par (f :: Net w arr a1 b1) (g :: Net w arr c d)) =
    par (bind h f) (bind h g)
  bind _h Swap = swap
  bind h Copy = h (Dg.copyT @w)
  bind h Discard = h (Dg.discardT @w)
  bind h Plus = h (Dg.plusT @w)
  bind h Zero = h (Dg.zeroT @w)
