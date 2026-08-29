{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Free symmetric monoidal category syntax.
--
-- This module packages the symmetric-monoidal layer on top of the generic
-- free-construction substrate in "Circuit.Syntax". The signature sum is
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
-- @'Tensor.tensor' f g@ builds a 'SigPar' node and @'Action.braid'@ builds a
-- 'SigSwap' node. Folding uses 'Circuit.Syntax.eval' or
-- 'Circuit.Syntax.evalInto'.
module Circuit.SMC
  ( -- * Free symmetric monoidal category
    SMC,

    -- * Dagger mirror
    mirrorSMC,

    -- * Constraint synonym used by Net's Layer law
    FreeSMC,

    -- * Signatures (exported for other syntax layers)
    SigPar (..),
    SigSwap (..),
  )
where

import Circuit.Category (Category (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Circuit.Dagger qualified as Dg
import Circuit.Syntax
  ( Algebra (..),
    SigCompose (..),
    Syntax (..),
    eval,
    (:+:) (..),
  )
import Circuit.Tensor (Action, Tensor, Unit, Unital)
import Circuit.Tensor qualified as T
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- Signatures

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

-- Free symmetric monoidal category

-- | Free symmetric monoidal category over wiring tensor @w@.
type SMC w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w) arr

-- Instances for the free symmetric monoidal category

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

-- * Dagger mirror

-- | Mirror an 'SMC' built over 'Dg.Dagger'.
--
-- Reverses composition, transposes each Lifted arrow, and leaves 'Circuit.Tensor.tensor'
-- and 'Circuit.Tensor.braid' self-dual. This is the structural transpose of the SMC
-- layer that 'Circuit.Net.mirrorSMC' delegates to.
mirrorSMC ::
  forall w arr a b.
  SMC w (Dg.Dagger arr) a b ->
  SMC w (Dg.Dagger arr) b a
mirrorSMC (Lift d) = Lift (Dg.transpose d)
mirrorSMC (Oper op) = case op of
  L (SigCompose g f) -> Oper (L (SigCompose (mirrorSMC f) (mirrorSMC g)))
  R (L (SigPar f g)) -> Oper (R (L (SigPar (mirrorSMC f) (mirrorSMC g))))
  R (R SigSwap) -> Oper (R (R SigSwap))

-- Constraint synonym used by Net's Layer law

-- | Free 'SMC' folds target any category with @w@-monoidal action.
class (Action w arr) => FreeSMC w arr

instance (Action w arr) => FreeSMC w arr
