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

-- | Change-of-base algebras for modular circuit syntax.
--
-- A 'Circuit.Layer.Layer' evals a free construction back into the /same/
-- base arrow. An 'Algebra' generalises this by allowing the target
-- category to differ from the source: it interprets syntax built over
-- @arr@ into morphisms of some other category @arr'@. The map
-- @emb :: arr :~> arr'@ handles the base-arrow generators, while
-- @eval@ handles the recursive sub-terms.
--
-- In this picture, 'Syntax sig arr' is the tree, 'Algebra sig arr arr''
-- is the interpreter, 'alg' evaluates a single constructor, and 'eval'
-- evals the whole tree. When @arr' = arr@ and @emb = id@, an 'Algebra'
-- collapses to the single universal eval that 'Layer' captures.
--
-- Each language feature is a signature functor. A GADT is the free
-- construction over a chosen combination of signatures. This makes the
-- design space a lattice: start with the features you need, add more
-- when you need them, and forget them via algebras.
--
-- The generic free-construction substrate lives in "Circuit.Syntax"; the
-- core traced-morphism syntax lives in "Circuit.Trace". This module adds
-- the remaining signatures (parallel composition, braiding, copy/discard,
-- shared-medium fusion) and the common combinations built from them.
--
-- The signatures are:
--
-- * @SigCompose@ — sequential composition
-- * @SigYank@    — feedback / trace over a tensor @t@
-- * @SigPar@     — parallel composition (the tensor product ⊗)
-- * @SigShared@  — shared-medium fusion (the tensor product ⅋), parameterised by a schedule
-- * @SigSwap@    — symmetric braiding
-- * @SigCopyDiscard@ — copy, discard
-- * @SigMergeZero@   — plus, zero
--
-- Examples:
--
-- * @'Syntax' @SigCompose@ arr@                              — free category
-- * @'Syntax' (@SigCompose@ ':+:' @SigYank@ t) arr@          — free traced category
-- * @'Syntax' (@SigCompose@ ':+:' @SigPar@ ':+:' @SigSwap@) arr@ — free monoidal category
-- * @'Syntax' (@SigCompose@ ':+:' @SigShared@ t ':+:' @SigYank@ t) arr@ — free traced category with shared-medium fusion
-- * @'Syntax' (@SigCompose@ ':+:' @SigPar@ ':+:' @SigSwap@ ':+:' 'SigCopyDiscard' ':+:' 'SigMergeZero') arr@ — Net
module Circuit.Fragment
  ( -- * Core syntax (re-exported from "Circuit.Syntax" and "Circuit.Trace")
    Sig,
    (:+:) (..),
    Syntax (..),
    Algebra (..),
    eval,
    evalInto,
    SigCompose (..),
    AlgCat,
    SigYank (..),
    Trace,
    base,
    yank,

    -- * Additional signatures
    SigShared (..),

    -- * Bimonoid signatures (re-exported from "Circuit.Bimonoid")
    SigCopy (..),
    SigDiscard (..),
    SigCopyDiscard,
    SigPlus (..),
    SigZero (..),
    SigMergeZero,

    -- * Common syntax combinations
    AlgShared,
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
    SigCopyDiscard,
    SigDiscard (..),
    SigMergeZero,
    SigPlus (..),
    SigZero (..),
  )
import Circuit.Bimonoid qualified as Bm
import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.SMC (SMC, SigPar (..), SigSwap (..))
import Circuit.Shared (Bias (..), Pick, Schedule (..), Shared (..), sharedBy)
import Circuit.Syntax
  ( AlgCat,
    Algebra (..),
    Sig,
    SigCompose (..),
    Syntax (..),
    eval,
    evalInto,
    (:+:) (..),
  )
import Circuit.Tensor (Unit)
import Circuit.Trace (SigYank (..), Trace, base, yank)
import Data.Kind (Constraint, Type)
import Data.These (These (..))
import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- Individual signatures

-- | Shared-medium fusion (the tensor product ⅋), parameterised by a schedule.
--
-- The constructor takes two bodies that already share a feedback type @s@ and
-- produces the untraced shared body.  The surrounding 'SigYank' closes the
-- feedback loop over @s@, yielding a morphism @t a c -> These b d@.
data SigShared (t :: Type -> Type -> Type) arr rec i o where
  SigShared ::
    Schedule s ->
    rec (t s a) (t s b) ->
    rec (t s c) (t s d) ->
    SigShared t arr rec (t s (t a c)) (t s (These b d))

instance (Shared t arr') => Algebra (SigShared t) arr arr' where
  type Ctx (SigShared t) arr arr' = Shared t arr'
  alg _ rec (SigShared sched f g) = sharedBy sched (rec f) (rec g)

-- ---------------------------------------------------------------------------
-- Common syntax combinations

-- | Free traced category with shared-medium fusion (the ⅋ connective).
type AlgShared t arr = Syntax (SigCompose :+: SigShared t :+: SigYank t) arr

-- | Free relevant symmetric monoidal category over wiring tensor @w@.
--
-- SMC plus contraction ('Copy') but no weakening.
type AlgRelevant w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w) arr

-- | Free affine symmetric monoidal category over wiring tensor @w@.
--
-- SMC plus weakening ('Discard') but no contraction.
type AlgAffine w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigDiscard w) arr

-- | Free cartesian symmetric monoidal category over wiring tensor @w@.
--
-- SMC plus the full comonoid ('Copy' and 'Discard').
type AlgCartesian w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w) arr

-- | Free co-relevant symmetric monoidal category over wiring tensor @w@.
--
-- SMC plus co-contraction ('Plus') but no co-weakening.
type AlgCoRelevant w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigPlus w) arr

-- | Free co-affine symmetric monoidal category over wiring tensor @w@.
--
-- SMC plus co-weakening ('Zero') but no co-contraction.
type AlgCoAffine w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigZero w) arr

-- | Free cocartesian symmetric monoidal category over wiring tensor @w@.
--
-- SMC plus the full monoid ('Plus' and 'Zero').
type AlgCocartesian w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigPlus w :+: SigZero w) arr

-- | Free bimonoidal category over wiring tensor @w@.
type AlgBimonoidal w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w) arr

-- | Free symmetric monoidal category with bimonoid over wiring tensor @w@.
type AlgNet w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w) arr
