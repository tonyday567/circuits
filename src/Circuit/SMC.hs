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
-- @'par' f g@ builds a 'SigPar' node and @'swap'@ builds a 'SigSwap' node.
-- Folding uses 'Circuit.Syntax.eval' or 'Circuit.Syntax.evalInto'.
module Circuit.SMC
  ( -- * Free symmetric monoidal category
    SMC,
    lift,
    par,
    swap,

    -- * Dagger mirror
    mirror,

    -- * Constraint synonym used by Net's Layer law
    FreeSMC,

    -- * Signatures (exported for other syntax layers)
    SigPar (..),
    SigSwap (..),
  )
where

import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Dagger qualified as Dg
import Circuit.Syntax
  ( Algebra (..),
    SigCompose (..),
    Syntax (..),
    eval,
    (:+:) (..),
  )
import Circuit.Tensor (Action, Tensor, Unit)
import Circuit.Tensor qualified as T
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- Signatures

-- | Parallel composition over the wiring tensor @w@.
data SigPar (w :: Type -> Type -> Type) arr rec a b where
  SigPar ::
    rec a b ->
    rec c d ->
    SigPar w arr rec (w a c) (w b d)

instance (Tensor w arr') => Algebra (SigPar w) arr arr' where
  type Ctx (SigPar w) arr arr' = Tensor w arr'
  alg _ rec (SigPar f g) = T.par (rec f) (rec g)

-- | Symmetric braiding over the wiring tensor @w@.
data SigSwap (w :: Type -> Type -> Type) arr rec a b where
  SigSwap :: SigSwap w arr rec (w a b) (w b a)

instance (Action w arr') => Algebra (SigSwap w) arr arr' where
  type Ctx (SigSwap w) arr arr' = Action w arr'
  alg _ _ SigSwap = T.swap

-- ---------------------------------------------------------------------------
-- Free symmetric monoidal category

-- | Free symmetric monoidal category over wiring tensor @w@.
type SMC w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w) arr

-- | Lift a base arrow into the free symmetric monoidal category.
lift :: arr a b -> SMC w arr a b
lift = Lift

-- | Parallel composition of two SMC morphisms.
par :: SMC w arr a b -> SMC w arr c d -> SMC w arr (w a c) (w b d)
par f g = Op (R (L (SigPar f g)))

-- | Symmetric braiding.
swap :: SMC w arr (w a b) (w b a)
swap = Op (R (R SigSwap))

-- ---------------------------------------------------------------------------
-- Instances for the free symmetric monoidal category

instance (Category arr) => Category (SMC w arr) where
  id = lift id
  f . g = Op (L (SigCompose f g))

instance (Tensor w arr) => Tensor w (SMC w arr) where
  par f g = Op (R (L (SigPar f g)))
  unitl = lift T.unitl
  unitl' = lift T.unitl'
  unitr = lift T.unitr
  unitr' = lift T.unitr'

instance (Action w arr) => Action w (SMC w arr) where
  swap = Op (R (R SigSwap))

instance (Category arr, Channel t arr) => Channel t (SMC w arr) where
  assoc = lift assoc
  assoc' = lift assoc'
  slide = lift slide

instance (Strength t arr, Action w arr) => Strength t (SMC w arr) where
  strength f = lift (strength (eval f))

instance (Traced t arr, Action w arr) => Traced t (SMC w arr) where
  trace body = lift (trace (eval body))

-- ---------------------------------------------------------------------------
-- Dagger mirror

-- | Mirror an 'SMC' built over 'Dg.Dagger'.
--
-- Reverses composition, transposes each lifted arrow, and leaves 'par'
-- and 'swap' self-dual. This is the structural transpose of the SMC
-- layer that 'Circuit.Net.mirror' delegates to.
mirror ::
  forall w arr a b.
  SMC w (Dg.Dagger arr) a b ->
  SMC w (Dg.Dagger arr) b a
mirror (Lift d) = Lift (Dg.transpose d)
mirror (Op op) = case op of
  L (SigCompose g f) -> Op (L (SigCompose (mirror f) (mirror g)))
  R (L (SigPar f g)) -> Op (R (L (SigPar (mirror f) (mirror g))))
  R (R SigSwap) -> Op (R (R SigSwap))

-- ---------------------------------------------------------------------------
-- Constraint synonym used by Net's Layer law

-- | Free 'SMC' folds target any category with @w@-monoidal action.
class (Action w arr) => FreeSMC w arr

instance (Action w arr) => FreeSMC w arr
