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
-- "Circuit.Dagger", and 'Bm.BimonoidT' is exactly the precondition that
-- lets 'Net' mirrorNet over 'Dg.Dagger' (see 'mirrorNet').
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
    Net,

    -- * Conversion
    widen,
    sift,

    -- * Interpretation
    melt,

    -- * Dagger
    mirrorNet,

    -- * Bimonoid syntax fragments (re-exported compatibility aliases)
    AlgRelevant,
    AlgAffine,
    AlgCartesian,
    AlgCoRelevant,
    AlgCoAffine,
    AlgCocartesian,
    AlgBimonoidal,
    AlgNet,
  )
where

import Circuit.Bimonoid
  ( SigCopy (..),
    SigDiscard (..),
    SigPlus (..),
    SigZero (..),
  )
import Circuit.Bimonoid qualified as Bm
import Circuit.Category (Category (..), (.>))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Circuit.Dagger qualified as Dg
import Circuit.Layer (Layer (..), run, (:~>))
import Circuit.SMC (FreeSMC, SMC, SigPar (..), SigSwap (..))
import Circuit.SMC qualified as SMC
import Circuit.Syntax (Algebra (..), SigCompose (..), Syntax (..), evalInto, (:+:) (..))
import Circuit.Tensor (Action, Tensor (..), Unit)
import Circuit.Trace (Trace, base, yank)
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Dagger qualified as Dg
-- >>> import Circuit.Layer (bind, run, unit)
-- >>> import Circuit.Net
-- >>> import Circuit.Trace (Trace, base, yank)
-- >>> import Circuit.Syntax (Syntax (Lift), eval, evalInto)
-- >>> import Circuit.SMC
-- >>> import Circuit.Category ((.))
-- >>> import Prelude hiding (id, (.))

-- | The free symmetric monoidal category with a bimonoid.
--
-- 'Net' is the free 'Syntax' over the signature sum
--
-- @
-- 'SigCompose' ':+:' 'SigPar' w ':+:' 'SigSwap' w ':+:' 'SigCopy' w ':+:' 'SigDiscard' w ':+:' 'SigPlus' w ':+:' 'SigZero' w
-- @
--
-- The 'Lift' constructor embeds a base arrow; the 'Oper' constructor holds
-- one of the signature nodes.  'widen' embeds an entire 'SMC' circuit.
type Net (w :: Type -> Type -> Type) arr =
  Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w) arr

-- | Free relevant symmetric monoidal category over wiring tensor @w@.
type AlgRelevant w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w) arr

-- | Free affine symmetric monoidal category over wiring tensor @w@.
type AlgAffine w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigDiscard w) arr

-- | Free cartesian symmetric monoidal category over wiring tensor @w@.
type AlgCartesian w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w) arr

-- | Free co-relevant symmetric monoidal category over wiring tensor @w@.
type AlgCoRelevant w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigPlus w) arr

-- | Free co-affine symmetric monoidal category over wiring tensor @w@.
type AlgCoAffine w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigZero w) arr

-- | Free cocartesian symmetric monoidal category over wiring tensor @w@.
type AlgCocartesian w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigPlus w :+: SigZero w) arr

-- | Free bimonoidal category over wiring tensor @w@.
type AlgBimonoidal w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w) arr

-- | Synonym for the full 'Net' syntax.
type AlgNet w arr = Net w arr

-- | The 'Category' instance is the generic free-category instance:
-- 'id' is a lifted identity and composition is a 'SigCompose' node.
instance (Category arr) => Category (Net w arr) where
  id = Lift id
  f . g = Oper (L (SigCompose f g))

-- | Include an 'SMC' circuit into 'Net'.
--
-- The injection recurses through the SMC signature sum and rebuilds each node
-- in the larger 'Net' signature sum.  This gives the adjunction between 'SMC'
-- and 'Net' together with 'sift'.
--
-- >>> let m = Lift (+1) . Lift (*2) :: SMC (,) (->) Int Int
-- >>> run (widen m :: Net (,) (->) Int Int) 5
-- 11
--
-- Coherence: 'sift' projects 'widen' back to the original 'SMC'.
--
-- >>> eval (sift (widen m :: Net (,) (->) Int Int)) 5
-- 11
-- >>> eval m 5
-- 11
--
-- Coherence: 'melt' agrees with the function fold on 'SMC' circuits.
--
-- >>> eval (melt (widen m :: Net (,) (->) Int Int) :: Trace (,) (->) Int Int) 5
-- 11
-- >>> eval m 5
-- 11
--
-- Coherence: 'Net' folds through 'widen' match 'SMC' folds.
--
-- >>> let h f = f
-- >>> (bind h (widen m :: Net (,) (->) Int Int) :: Int -> Int) 5
-- 11
-- >>> (evalInto h m :: Int -> Int) 5
-- 11
--
-- Coherence: mirroring commutes with 'widen'.
--
-- >>> let dm = Lift (Dg.Dagger (+1) (subtract 1)) . Lift (Dg.Dagger (*2) (\x -> x `div` 2)) :: SMC (,) (Dg.Dagger (->)) Int Int
-- >>> Dg.front (Dg.transpose (eval dm)) 10
-- 4
-- >>> Dg.front (Dg.transpose (run (widen dm :: Net (,) (Dg.Dagger (->)) Int Int))) 10
-- 4
widen :: SMC w arr a b -> Net w arr a b
widen (Lift f) = Lift f
widen (Oper op) = case op of
  L (SigCompose g f) -> Oper (L (SigCompose (widen g) (widen f)))
  R (L (SigPar f g)) -> Oper (R (L (SigPar (widen f) (widen g))))
  R (R SigSwap) -> Oper (R (R (L SigSwap)))

-- | Forget the bimonoid rows of a 'Net', keeping only the 'SMC' wiring.
--
-- 'sift' collapses the bimonoid rows into 'Lift' while leaving
-- 'SigCompose' and 'SigPar' inspectable. Together with 'widen' it gives the
-- adjunction between 'SMC' and 'Net'.
-- Note the converse does not hold: @widen . sift ≠ id@ because 'sift'
-- forgets bimonoid structure.
sift ::
  forall w arr a b.
  (Action w arr) =>
  Net w arr a b ->
  SMC w arr a b
sift = evalInto Lift

-- | Melt the structural rows of a 'Net' into the free 'Trace' syntax.
--
-- The interpretation from the free symmetric monoidal category with
-- bimonoid to the free traced monoidal category.  Structural rows ('SigPar',
-- 'SigCopy', 'SigPlus', etc.) become opaque base-arrow operations wrapped in
-- 'base'; @SigCompose@ uses the 'Category' instance of 'Trace'.
--
-- @'run' @Net = 'Circuit.Syntax.eval' . 'melt'@.
--
-- >>> eval (melt (Lift (+1) :: Net (,) (->) Int Int) :: Trace (,) (->) Int Int) 5
-- 6
melt ::
  forall w t arr a b.
  (Yank t arr, Action w arr) =>
  Net w arr a b ->
  Trace t arr a b
melt = evalInto base

-- | Mirror a 'Net' over 'Dg.Dagger'.
--
-- The dagger dualizes the bimonoid rows: 'SigCopy' becomes 'SigPlus',
-- 'SigDiscard' becomes 'SigZero', and vice versa.  Composition is reversed;
-- parallel composition and the braiding are self-dual.
--
-- This operation is total exactly when the base arrow carries a bimonoid
-- on the wiring tensor for every object, i.e. when
-- @'Bm.BimonoidT' w arr x@ holds for all @x@.  That precondition is the
-- tensor-generic form of the 'Dg.Bimonoid' law that makes 'Dagger' and the
-- bimonoid rows presentable as one structure.
mirrorNet ::
  forall w arr a b.
  (forall x. Bm.BimonoidT w arr x) =>
  Net w (Dg.Dagger arr) a b ->
  Net w (Dg.Dagger arr) b a
mirrorNet (Lift d) = Lift (Dg.transpose d)
mirrorNet (Oper op) = case op of
  L (SigCompose g f) -> Oper (L (SigCompose (mirrorNet f) (mirrorNet g)))
  R (L (SigPar f g)) -> Oper (R (L (SigPar (mirrorNet f) (mirrorNet g))))
  R (R (L SigSwap)) -> Oper (R (R (L SigSwap)))
  R (R (R (L SigCopy))) -> Oper (R (R (R (R (R (L SigPlus))))))
  R (R (R (R (L SigDiscard)))) -> Oper (R (R (R (R (R (R SigZero))))))
  R (R (R (R (R (L SigPlus))))) -> Oper (R (R (R (L SigCopy))))
  R (R (R (R (R (R SigZero))))) -> Oper (R (R (R (R (L SigDiscard)))))

-- | Free symmetric monoidal category with a bimonoid.
--
-- Structural rows are interpreted in the target category: parallel
-- composition uses 'tensor', braiding uses 'braid', and the bimonoid
-- generators are the images under @h@ of the source dictionaries carried
-- by the 'SigCopy', 'SigDiscard', 'SigPlus', and 'SigZero' constructors.
--
-- [Conditional] 'bind' @h@ interprets bimonoid generators as images under
-- @h@ of the source arrow's dictionaries.  This is the free-PROP fold
-- only when @h@ is a bimonoid homomorphism (automatic for the generator
-- embedding, but must be verified for custom @h@).
instance Layer (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w)) where
  type Law (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w)) arr' = FreeSMC w arr'
  type Run (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w)) arr = Action w arr
  type Bind (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w)) arr = ()
  unit = Lift
  bind ::
    forall arr' arr a b.
    (Law (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w)) arr') =>
    (arr :~> arr') ->
    Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w) arr a b ->
    arr' a b
  bind = evalInto
