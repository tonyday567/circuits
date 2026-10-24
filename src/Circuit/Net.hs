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
-- ('SigPar', 'SigSwap', the 'SMC' syntax and its 'daggerSMC') is
-- the layer on top of the generic free-construction substrate in
-- "Circuit.Syntax"; 'Net' extends it with structural rows for the bimonoid
-- operations: copy, discard, addition, and zero.  Where 'FreeTrace' keeps
-- only 'Lift' arrows and 'trace' in normal form, 'Net' keeps the wiring
-- inspectable — the difference between wiring you can read backwards and
-- wiring that has been folded into a single loop.
--
-- The bimonoid rows are the dagger's fixed structure: they live in
-- "Circuit.Bimonoid" alongside the 'Dagger' type, and 'Bm.BimonoidT' is
-- exactly the precondition that lets 'Net' dagger bimonoid rows over
-- @Dagger arr@ (see 'daggerNet').
--
-- @
-- Free = Lift + Compose
-- SMC  = Free + Par + Swap
-- Net  = SMC + Copy + Discard + Plus + Zero
-- @
--
-- 'run' @Net@ interprets a 'Net' to a plain arrow; @'evalInto' 'Lift'@
-- reinterprets the structural rows into the free traced syntax
-- ('FreeTrace'; bimonoid rows become opaque lifted arrows).
module Circuit.Net
  ( -- * Net
    Net,

    -- * Conversion
    widen,
    melt,

    -- * Dagger
    daggerNet,

    -- * Symmetric-monoidal layer
    SMC,

    -- ** Dagger mirror
    daggerSMC,

    -- ** Signatures (exported for other syntax layers)
    SigPar (..),
    SigSwap (..),
  )
where

import Circuit.Bimonoid
  ( Dagger (..),
    SigCopy (..),
    SigDiscard (..),
    SigMerge (..),
    SigZero (..),
    dagger,
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
import Circuit.Tensor (SemiTensor, Symmetric, Tensor, Unital)
import Circuit.Tensor qualified as T
import Circuit.Trace (FreeTrace)
import Circuit.Traced (Assoc (..), OuterSwap (..), Strength (..), Trace (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Bimonoid (Dagger (..), dagger)
-- >>> import Circuit.Net
-- >>> import Circuit.Trace (FreeTrace)
-- >>> import Circuit.Syntax (Syntax (Lift), bind, eval, evalInto, run)
-- >>> import Circuit.Category ((.), (.>))
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
-- The 'Tensor' and 'Symmetric' instances are the syntactic constructors:
-- @'Tensor.tensor' f g@ builds a 'SigPar' node and @'Symmetric.braid'@ builds
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

instance (Symmetric w arr') => Algebra (SigSwap w) arr arr' where
  type Ctx (SigSwap w) arr arr' = Symmetric w arr'
  alg _ _ SigSwap = T.braid

-- ** Free symmetric monoidal category

-- | Free symmetric monoidal category over wiring tensor @w@.
type SMC w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w) arr

-- | Include an 'SMC' circuit into 'Net'.
--
-- The injection recurses through the SMC signature sum and rebuilds each node
-- in the larger 'Net' signature sum.  Composing with @'evalInto' 'Lift'@ in
-- the other direction — projecting the bimonoid rows back to lifted arrows —
-- gives the adjunction between 'SMC' and 'Net'.
--
-- >>> let m = Lift (+1) . Lift (*2) :: SMC (,) (->) Int Int
-- >>> run (widen m :: Net (,) (->) Int Int) 5
-- 11
--
-- Coherence: 'evalInto' 'Lift' projects 'widen' back to the original 'SMC'.
--
-- >>> eval (evalInto Lift (widen m :: Net (,) (->) Int Int) :: SMC (,) (->) Int Int) 5
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
-- >>> front (dagger (eval dm)) 10
-- 4
-- >>> front (dagger (run (widen dm :: Net (,) (Dagger (->)) Int Int))) 10
-- 4
widen :: SMC w arr a b -> Net w arr a b
widen (Lift f) = Lift f
widen (Oper op) = case op of
  L (SigCompose g f) -> Oper (L (SigCompose (widen g) (widen f)))
  R (L (SigPar f g)) -> Oper (R (L (SigPar (widen f) (widen g))))
  R (R SigSwap) -> Oper (R (R (L SigSwap)))

-- | Mirror an 'SMC' built over 'Dagger'.
--
-- Reverses composition, daggers each Lifted arrow, and leaves 'Circuit.Tensor.tensor'
-- and 'Circuit.Tensor.braid' self-dual. This is the structural dagger of the SMC
-- layer that 'daggerNet' inlines.
daggerSMC ::
  forall w arr a b.
  SMC w (Dagger arr) a b ->
  SMC w (Dagger arr) b a
daggerSMC (Lift d) = Lift (dagger d)
daggerSMC (Oper op) = case op of
  L (SigCompose g f) -> Oper (L (SigCompose (daggerSMC f) (daggerSMC g)))
  R (L (SigPar f g)) -> Oper (R (L (SigPar (daggerSMC f) (daggerSMC g))))
  R (R SigSwap) -> Oper (R (R SigSwap))

-- ** Instances for the free symmetric monoidal category

instance (Category arr) => Category (SMC w arr) where
  id = Lift id
  f . g = Oper (L (SigCompose f g))

instance (Unital w arr) => Unital w (SMC w arr) where
  unitl = Lift T.unitl
  unitl' = Lift T.unitl'
  unitr = Lift T.unitr
  unitr' = Lift T.unitr'

instance (SemiTensor w arr) => SemiTensor w (SMC w arr) where
  tensor f g = Oper (R (L (SigPar f g)))

-- | 'Tensor' for 'SMC' is the conjunction: the 'Unital' lift above plus
-- this 'SemiTensor' lift.
instance (Tensor w arr) => Tensor w (SMC w arr)

instance (Symmetric w arr) => Symmetric w (SMC w arr) where
  braid = Oper (R (R SigSwap))

instance (Category arr, Assoc t arr) => Assoc t (SMC w arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'

instance (Category arr, OuterSwap t arr) => OuterSwap t (SMC w arr) where
  outerSwap = Lift outerSwap

instance (Strength t arr, Symmetric w arr) => Strength t (SMC w arr) where
  strength f = Lift (strength (eval f))

instance (Trace t arr, Symmetric w arr) => Trace t (SMC w arr) where
  trace body = Lift (trace (eval body))

-- ** Iteration as a loop with joined wires

-- The codiagonal theorem (stated in "Circuit.Traced"'s
-- 'Circuit.Traced.Unfold'): @unfold g = trace (g . mergeT)@ — an iteration
-- is a loop whose entry and feedback wires are joined. The composite
-- needs no new syntax: the 'SigMerge' node 'Net' already has supplies the
-- join, and the 'Circuit.Trace.SigTrace' node supplies the loop. The body
-- melts Net to a function through the 'Circuit.Bimonoid.MergeT' Either
-- dictionary, lifts into 'FreeTrace', and folds through 'Trace' Either —
-- agreeing with 'Circuit.Traced.unfold' at a point:
--
-- >>> import Circuit.Bimonoid (SigMerge (..))
-- >>> import Circuit.Traced (unfold)
-- >>> import Circuit.Syntax (Syntax (..))
-- >>> import Circuit.Traced (trace)
-- >>> let down n = if n <= (0 :: Int) then Right n else Left (n - 1)
-- >>> let body = Lift down . Oper (R (R (R (R (R (L SigMerge)))))) :: Net Either (->) (Either Int Int) (Either Int Int)
-- >>> run (trace (Lift (run body)) :: FreeTrace Either (->) Int Int) 5
-- 0
-- >>> unfold down 5
-- 0

-- * Net

-- | The free symmetric monoidal category with a bimonoid.
--
-- 'Net' is the free 'Syntax' over the signature sum
--
-- @
-- 'SigCompose' ':+:' 'SigPar' w ':+:' 'SigSwap' w ':+:' 'SigCopy' w ':+:' 'SigDiscard' w ':+:' 'SigMerge' w ':+:' 'SigZero' w
-- @
--
-- The 'Lift' constructor embeds a base arrow; the 'Oper' constructor holds
-- one of the signature nodes.  'widen' embeds an entire 'SMC' circuit.
type Net (w :: Type -> Type -> Type) arr =
  Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigMerge w :+: SigZero w) arr

-- | The 'Category' instance is the generic free-category instance:
-- 'id' is a lifted identity and composition is a 'SigCompose' node.
instance (Category arr) => Category (Net w arr) where
  id = Lift id
  f . g = Oper (L (SigCompose f g))

-- | Mirror a 'Net' over 'Dagger'.
--
-- The dagger dualizes the bimonoid rows: 'SigCopy' becomes 'SigMerge',
-- 'SigDiscard' becomes 'SigZero', and vice versa.  Composition is reversed;
-- parallel composition and the braiding are self-dual.
--
-- This operation is total exactly when the base arrow carries a bimonoid
-- on the wiring tensor for every object, i.e. when
-- @'Bm.BimonoidT' w arr x@ holds for all @x@.  That precondition is the
-- tensor-generic form of the 'Bm.BimonoidT' constraint that makes 'Dagger'
-- and the bimonoid rows presentable as one structure.
daggerNet ::
  forall w arr a b.
  (forall x. Bm.BimonoidT w arr x) =>
  Net w (Dagger arr) a b ->
  Net w (Dagger arr) b a
daggerNet (Lift d) = Lift (dagger d)
daggerNet (Oper op) = case op of
  L (SigCompose g f) -> Oper (L (SigCompose (daggerNet f) (daggerNet g)))
  R (L (SigPar f g)) -> Oper (R (L (SigPar (daggerNet f) (daggerNet g))))
  R (R (L SigSwap)) -> Oper (R (R (L SigSwap)))
  R (R (R (L SigCopy))) -> Oper (R (R (R (R (R (L SigMerge))))))
  R (R (R (R (L SigDiscard)))) -> Oper (R (R (R (R (R (R SigZero))))))
  R (R (R (R (R (L SigMerge))))) -> Oper (R (R (R (L SigCopy))))
  R (R (R (R (R (R SigZero))))) -> Oper (R (R (R (R (L SigDiscard)))))

-- * Interpretation

-- | Melt the structural rows of a 'Net' into the free traced syntax.
--
-- The interpretation from the free symmetric monoidal category with a
-- bimonoid to the free traced monoidal category, at one tensor: structural
-- rows ('SigPar', 'SigCopy', 'SigMerge', etc.) become opaque base-arrow
-- operations wrapped in 'Lift'; @SigCompose@ uses the 'Category' instance
-- of 'FreeTrace'. Totality is free — 'Net' has no feedback constructor, so
-- the domain is a finite wiring tree and 'evalInto' is structural.
--
-- The law: @'run' \@Net = 'eval' . 'melt'@ — folding a net straight to the
-- base arrow agrees with melting to 'FreeTrace' and evaluating there.
--
-- >>> import Circuit.Bimonoid (SigCopy (..))
-- >>> let copyNet = Lift (+1) .> Oper (R (R (R (L SigCopy)))) :: Net (,) (->) Int (Int, Int)
-- >>> eval (melt copyNet :: FreeTrace (,) (->) Int (Int, Int)) 5
-- (6,6)
--
-- On the Either iteration example above, melting commutes with the fold:
--
-- >>> let down n = if n <= (0 :: Int) then Right n else Left (n - 1)
-- >>> let body = Lift down . Oper (R (R (R (R (R (L SigMerge)))))) :: Net Either (->) (Either Int Int) (Either Int Int)
-- >>> run body (Right 5)
-- Left 4
-- >>> eval (melt body) (Right 5)
-- Left 4
--
-- The cross-tensor spelling @Net w arr -> FreeTrace t arr@ is deliberately
-- not restored: the through-'Trace' 'Assoc' instance forces @w ~ t@.
melt ::
  (Symmetric w arr, Trace w arr) =>
  Net w arr a b ->
  FreeTrace w arr a b
melt = evalInto Lift

-- | Free symmetric monoidal category with a bimonoid.
--
-- Structural rows are interpreted in the target category: parallel
-- composition uses 'tensor', braiding uses 'braid', and the bimonoid
-- generators are the images under @h@ of the source dictionaries carried
-- by the 'SigCopy', 'SigDiscard', 'SigMerge', and 'SigZero' constructors.
--
-- [Conditional] 'bind' @h@ interprets bimonoid generators as images under
-- @h@ of the source arrow's dictionaries.  This is the free-PROP fold
-- only when @h@ is a bimonoid homomorphism (automatic for the generator
-- embedding, but must be verified for custom @h@).
instance Layer (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigMerge w :+: SigZero w)) where
  type Law (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigMerge w :+: SigZero w)) arr' = Symmetric w arr'
  type Run (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigMerge w :+: SigZero w)) arr = Symmetric w arr
  type Bind (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigMerge w :+: SigZero w)) arr = ()
  unit = Lift
  bind ::
    forall arr' arr a b.
    (Law (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigMerge w :+: SigZero w)) arr') =>
    (arr :~> arr') ->
    Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigMerge w :+: SigZero w) arr a b ->
    arr' a b
  bind = evalInto
