{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-partial-fields #-}

-- | The free symmetric monoidal category with a bimonoid over a primitive set.
--
-- This module hosts the whole widen chain.  The symmetric-monoidal layer
-- ('SigPar', 'SigSwap', the 'SMC' syntax and its 'mirrorSMC' transpose) is
-- the layer on top of the generic free-construction substrate in
-- "Circuit.Syntax"; 'Net' extends it with structural rows for the bimonoid
-- operations: copy, discard, addition, and zero.  Where 'Trace' keeps
-- only 'Lift' arrows and 'yank' in normal form, 'Net' keeps the wiring
-- inspectable — the difference between wiring you can read backwards and
-- wiring that has been melted into a single loop.
--
-- The bimonoid rows are the dagger's fixed structure: they live in
-- "Circuit.Bimonoid" alongside the 'Dagger' type, and 'Bm.BimonoidT' is
-- exactly the precondition that lets 'Net' transpose bimonoid rows over
-- @Dagger arr@ (see 'mirrorNet').
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

    -- * Symmetric-monoidal layer
    SMC,

    -- ** Dagger mirror
    mirrorSMC,

    -- ** Constraint synonym used by Net's Layer law
    FreeSMC,

    -- ** Signatures (exported for other syntax layers)
    SigPar (..),
    SigSwap (..),
  )
where

import Circuit.Bimonoid
  ( Dagger (..),
    SigCopy (..),
    SigDiscard (..),
    SigPlus (..),
    SigZero (..),
    transpose,
  )
import Circuit.Bimonoid qualified as Bm
import Circuit.Category (Category (..))
import Circuit.Syntax
  ( Algebra (..),
    Layer (..),
    SigCompose (..),
    Syntax (..),
    eval,
    evalInto,
    (:+:) (..),
    (:~>),
  )
import Circuit.Tensor (Action, Tensor, Unital)
import Circuit.Tensor qualified as T
import Circuit.Trace (Trace)
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Bimonoid (Dagger (..), transpose)
-- >>> import Circuit.Net
-- >>> import Circuit.Trace (Trace)
-- >>> import Circuit.Syntax (Syntax (Lift), bind, eval, evalInto, run)
-- >>> import Circuit.Category ((.))
-- >>> import Prelude hiding (id, (.))

-- * Symmetric-monoidal layer

-- | This layer packages the symmetric-monoidal structure on top of the
-- generic free-construction substrate in "Circuit.Syntax". The signature
-- sum is
--
-- @
-- 'SigCompose' ':+:' 'SigPar' w ':+:' 'SigSwap' w
-- @
--
-- where 'SigCompose' provides sequential composition, 'SigPar' w provides
-- parallel composition over the wiring tensor @w@, and 'SigSwap' w provides
-- the symmetry / braiding.
--
-- The 'Tensor' and 'Action' instances are the syntactic constructors:
-- @'Tensor.tensor' f g@ builds a 'SigPar' node and @'Action.braid'@ builds
-- a 'SigSwap' node. Folding uses 'Circuit.Syntax.eval' or
-- 'Circuit.Syntax.evalInto'.

-- ** Signatures

-- | Parallel composition over the wiring tensor @w@.
data SigPar (w :: Type -> Type -> Type) arr rec a b where
  SigPar ::
    rec a b ->
    rec c d ->
    SigPar w arr rec (w a c) (w b d)

instance (Tensor w arr') => Algebra (SigPar w) arr arr' where
  type Ctx (SigPar w) arr arr' = Tensor w arr'
  alg _ rec (SigPar f g) = T.tensor (rec f) (rec g)

-- | Symmetric braiding over the wiring tensor @w@.
data SigSwap (w :: Type -> Type -> Type) arr rec a b where
  SigSwap :: SigSwap w arr rec (w a b) (w b a)

instance (Action w arr') => Algebra (SigSwap w) arr arr' where
  type Ctx (SigSwap w) arr arr' = Action w arr'
  alg _ _ SigSwap = T.braid

-- ** Free symmetric monoidal category

-- | Free symmetric monoidal category over wiring tensor @w@.
type SMC w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w) arr

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
-- >>> let dm = Lift (Dagger (+1) (subtract 1)) . Lift (Dagger (*2) (\x -> x `div` 2)) :: SMC (,) (Dagger (->)) Int Int
-- >>> front (transpose (eval dm)) 10
-- 4
-- >>> front (transpose (run (widen dm :: Net (,) (Dagger (->)) Int Int))) 10
-- 4
widen :: SMC w arr a b -> Net w arr a b
widen (Lift f) = Lift f
widen (Oper op) = case op of
  L (SigCompose g f) -> Oper (L (SigCompose (widen g) (widen f)))
  R (L (SigPar f g)) -> Oper (R (L (SigPar (widen f) (widen g))))
  R (R SigSwap) -> Oper (R (R (L SigSwap)))

-- | Mirror an 'SMC' built over 'Dagger'.
--
-- Reverses composition, transposes each Lifted arrow, and leaves 'Circuit.Tensor.tensor'
-- and 'Circuit.Tensor.braid' self-dual. This is the structural transpose of the SMC
-- layer that 'mirrorNet' inlines.
mirrorSMC ::
  forall w arr a b.
  SMC w (Dagger arr) a b ->
  SMC w (Dagger arr) b a
mirrorSMC (Lift d) = Lift (transpose d)
mirrorSMC (Oper op) = case op of
  L (SigCompose g f) -> Oper (L (SigCompose (mirrorSMC f) (mirrorSMC g)))
  R (L (SigPar f g)) -> Oper (R (L (SigPar (mirrorSMC f) (mirrorSMC g))))
  R (R SigSwap) -> Oper (R (R SigSwap))

-- | Free 'SMC' folds target any category with @w@-monoidal action.
class (Action w arr) => FreeSMC w arr

instance (Action w arr) => FreeSMC w arr

-- ** Instances for the free symmetric monoidal category

instance (Category arr) => Category (SMC w arr) where
  id = Lift id
  f . g = Oper (L (SigCompose f g))

instance (Unital w arr) => Unital w (SMC w arr) where
  unitl = Lift T.unitl
  unitl' = Lift T.unitl'
  unitr = Lift T.unitr
  unitr' = Lift T.unitr'

instance (Tensor w arr) => Tensor w (SMC w arr) where
  tensor f g = Oper (R (L (SigPar f g)))

instance (Action w arr) => Action w (SMC w arr) where
  braid = Oper (R (R SigSwap))

instance (Category arr, Assoc t arr) => Assoc t (SMC w arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'

instance (Category arr, Slide t arr) => Slide t (SMC w arr) where
  slide = Lift slide

instance (Strength t arr, Action w arr) => Strength t (SMC w arr) where
  strength f = Lift (strength (eval f))

instance (Yank t arr, Action w arr) => Yank t (SMC w arr) where
  yank body = Lift (yank (eval body))

-- * Net

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
-- 'Lift'; @SigCompose@ uses the 'Category' instance of 'Trace'.
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
melt = evalInto Lift

-- | Mirror a 'Net' over 'Dagger'.
--
-- The dagger dualizes the bimonoid rows: 'SigCopy' becomes 'SigPlus',
-- 'SigDiscard' becomes 'SigZero', and vice versa.  Composition is reversed;
-- parallel composition and the braiding are self-dual.
--
-- This operation is total exactly when the base arrow carries a bimonoid
-- on the wiring tensor for every object, i.e. when
-- @'Bm.BimonoidT' w arr x@ holds for all @x@.  That precondition is the
-- tensor-generic form of the 'Bm.BimonoidT' constraint that makes 'Dagger'
-- and the bimonoid rows presentable as one structure.
mirrorNet ::
  forall w arr a b.
  (forall x. Bm.BimonoidT w arr x) =>
  Net w (Dagger arr) a b ->
  Net w (Dagger arr) b a
mirrorNet (Lift d) = Lift (transpose d)
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
