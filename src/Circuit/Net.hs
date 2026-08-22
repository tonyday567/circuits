{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-partial-fields #-}

-- | The free symmetric monoidal category with a bimonoid over a primitive set.
--
-- 'Net' extends 'SMC' with structural rows for the bimonoid
-- operations: copy, discard, addition, and zero.  Where 'Trace' keeps
-- only 'base' and 'yank' in normal form, 'Net' keeps the wiring
-- inspectable — the difference between wiring you can read backwards and
-- wiring that has been melted into a single loop.
--
-- The bimonoid rows are the dagger's fixed structure: they are owned by
-- "Circuit.Dagger", and 'Dg.BimonoidT' is exactly the precondition that
-- lets 'Net' mirror over 'Dg.Dagger' (see 'mirror').
--
-- @
-- Free = Lift + Compose
-- SMC  = Free + Par + Swap
-- Net  = SMC + Copy + Discard + Plus + Zero
-- @
--
-- 'run' @Net@ interprets a 'Net' to a plain arrow.  'melt' interprets the
-- structural rows into the free 'Trace' syntax.
module Circuit.Net
  ( -- * Net
    Net (..),

    -- * Smart constructors
    lift,
    swap,

    -- * Conversion
    widen,
    sift,

    -- * Interpretation
    melt,

    -- * Dagger
    mirror,
  )
where

import Circuit.Category (Category (..), (.>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Dagger qualified as Dg
import Circuit.Layer (Layer (..), run, (:~>))
import Circuit.Layer qualified as Layer
import Circuit.SMC (FreeSMC, SMC (..))
import Circuit.Trace (Trace, base, yank)
import Circuit.SMC qualified as SMC
import Circuit.Tensor (Action, Tensor (..), Unit)
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Dagger qualified as Dg
-- >>> import Circuit.Layer (bind, run, unit)
-- >>> import Circuit.Net
-- >>> import Circuit.Trace (Trace, base, yank)
-- >>> import Circuit.Syntax (eval)
-- >>> import Circuit.SMC
-- >>> import Prelude hiding (id, (.))

-- | The free symmetric monoidal category with a bimonoid.
--
-- Three families of constructor:
--
--   * __SMC__ — 'FromSMC' embeds the whole 'SMC' layer; 'lift' and 'swap'
--     are smart constructors for the common cases.
--   * __Sequential / monoidal__ — 'Compose' and 'Par' extend the SMC
--     embedding to arbitrary 'Net' values; they are needed because the
--     bimonoid generators are not SMC morphisms.
--   * __Copy/Discard/Plus/Zero__ — the four atomic bimonoid generators,
--     each carrying its own 'Dg.CopyT' / 'Dg.DiscardT' / 'Dg.MergeT' /
--     'Dg.ZeroT' dictionary.
--
-- 'Dg.CopyT' / 'Dg.DiscardT' and 'Dg.MergeT' / 'Dg.ZeroT' constraints ride
-- as dictionary arguments on the constructors that need them — laws in the
-- typeclass holes, evidence on the GADT rows.
--
-- The bimonoid rows mirror under 'Dg.Dagger': 'Copy' swaps with 'Plus',
-- and 'Discard' swaps with 'Zero' (see 'mirror').
--
-- The wiring monoidal structure is over a generic tensor @w@.  Feedback is
-- not represented inside 'Net'; it lives in 'Trace' and is introduced only
-- at the boundary by 'melt' or by interpreting into a traced target
-- category.
--
-- 'Net' extends 'Trace' inspectably for the wiring rows.  'melt'
-- collapses the structure to the free 'Trace' syntax.
data Net (w :: Type -> Type -> Type) arr a b where
  -- | Embed an 'SMC' circuit whole.  This is the only contact point between
  -- the SMC layer and the bimonoid layer; 'Net' no longer duplicates the
  -- SMC constructors.
  FromSMC :: SMC w arr a b -> Net w arr a b
  -- | Sequential composition.
  Compose :: Net w arr b c -> Net w arr a b -> Net w arr a c
  -- | Parallel composition (monoidal product over @w@).
  Par ::
    Net w arr a b ->
    Net w arr c d ->
    Net w arr (w a c) (w b d)
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
-- Composition of two 'FromSMC' values is pushed back into 'SMC'; all other
-- compositions use the explicit 'Compose' constructor, so 'Copy', 'Plus',
-- and 'Par' stay visible.  'melt' collapses the structure when the normal
-- form is needed.
instance (Category arr) => Category (Net w arr) where
  id = FromSMC id
  FromSMC g . FromSMC f = FromSMC (g . f)
  g . f = Compose g f

-- | Lift a base arrow into 'Net' via 'SMC'.
lift :: arr a b -> Net w arr a b
lift = FromSMC . SMCLift

-- | Symmetric braiding in 'Net' via 'SMC'.
swap :: Net w arr (w a b) (w b a)
swap = FromSMC SMCSwap

-- | Include an 'SMC' circuit into 'Net'.
--
-- 'Net' no longer duplicates the SMC constructors; the injection is a single
-- 'FromSMC' wrapper.  This gives the adjunction between 'SMC' and 'Net'
-- together with 'sift'.
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
-- >>> eval (melt (widen m :: Net (,) (->) Int Int) :: Trace (,) (->) Int Int) 5
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
-- Coherence: mirroring commutes with 'widen'.
--
-- >>> let dm = SMCLift (Dg.Dagger (+1) (subtract 1)) `SMCCompose` SMCLift (Dg.Dagger (*2) (\x -> x `div` 2)) :: SMC (,) (Dg.Dagger (->)) Int Int
-- >>> Dg.front (Dg.transpose (run dm)) 10
-- 4
-- >>> Dg.front (Dg.transpose (run (widen dm :: Net (,) (Dg.Dagger (->)) Int Int))) 10
-- 4
widen :: SMC w arr a b -> Net w arr a b
widen = FromSMC

-- | Forget the bimonoid rows of a 'Net', keeping only the 'SMC' wiring.
--
-- 'sift' collapses the bimonoid rows into 'SMCLift' while leaving
-- 'Compose' and 'Par' inspectable. Together with 'widen' it gives the
-- adjunction between 'SMC' and 'Net'.
-- Note the converse does not hold: @widen . sift ≠ id@ because 'sift'
-- forgets bimonoid structure.
sift ::
  forall w arr a b.
  (Action w arr) =>
  Net w arr a b ->
  SMC w arr a b
sift (FromSMC s) = s
sift (Compose g f) = SMCCompose (sift g) (sift f)
sift (Par f g) = SMCPar (sift f) (sift g)
sift Copy = SMCLift (Dg.copyT @w)
sift Discard = SMCLift (Dg.discardT @w)
sift Plus = SMCLift (Dg.plusT @w)
sift Zero = SMCLift (Dg.zeroT @w)

-- | Melt the structural rows of a 'Net' into the free 'Trace' syntax.
--
-- The interpretation from the free symmetric monoidal category with
-- bimonoid to the free traced monoidal category.  Structural rows ('Par',
-- 'Copy', 'Plus', etc.) become opaque base-arrow operations wrapped in
-- 'base'; @Compose@ uses the 'Category' instance of 'Trace'.
--
-- @'run' @Net = 'eval' . 'melt'@.
--
-- >>> eval (melt (lift (+1) :: Net (,) (->) Int Int) :: Trace (,) (->) Int Int) 5
-- 6
melt ::
  forall w t arr a b.
  (Traced t arr, Action w arr) =>
  Net w arr a b ->
  Trace t arr a b
melt (FromSMC s) = Layer.bind base s
melt (Compose g f) = melt g . melt f
melt (Par f g) = par (melt f) (melt g)
melt Copy = base (Dg.copyT @w)
melt Discard = base (Dg.discardT @w)
melt Plus = base (Dg.plusT @w)
melt Zero = base (Dg.zeroT @w)

-- | Mirror a 'Net' over 'Dg.Dagger'.
--
-- The dagger dualizes the bimonoid rows: 'Copy' becomes 'Plus', 'Discard'
-- becomes 'Zero', and vice versa.  Composition is reversed; parallel
-- composition and the braiding are self-dual.
--
-- This operation is total exactly when the base arrow carries a bimonoid
-- on the wiring tensor for every object, i.e. when
-- @'Dg.BimonoidT' w arr x@ holds for all @x@.  That precondition is the
-- tensor-generic form of the 'Dg.Bimonoid' law that makes 'Dagger' and the
-- bimonoid rows presentable as one structure.
mirror ::
  forall w arr a b.
  (forall x. Dg.BimonoidT w arr x) =>
  Net w (Dg.Dagger arr) a b ->
  Net w (Dg.Dagger arr) b a
mirror (FromSMC s) = FromSMC (SMC.mirror s)
mirror (Compose g f) = Compose (mirror f) (mirror g)
mirror (Par f g) = Par (mirror f) (mirror g)
mirror Copy = Plus
mirror Discard = Zero
mirror Plus = Copy
mirror Zero = Discard

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
  unit = lift
  bind ::
    forall arr' arr a b.
    (Law (Net w) arr') =>
    (arr :~> arr') ->
    Net w arr a b ->
    arr' a b
  bind h (FromSMC s) = Layer.bind h s
  bind h (Compose (g :: Net w arr b1 c) (f :: Net w arr a b1)) =
    bind h g . bind h f
  bind h (Par (f :: Net w arr a1 b1) (g :: Net w arr c d)) =
    par (bind h f) (bind h g)
  bind h Copy = h (Dg.copyT @w)
  bind h Discard = h (Dg.discardT @w)
  bind h Plus = h (Dg.plusT @w)
  bind h Zero = h (Dg.zeroT @w)
