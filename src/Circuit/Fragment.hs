{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
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
-- shared-medium fusion, mediators) and the common combinations built from
-- them.
--
-- The signatures are:
--
-- * @SigCompose@ — sequential composition
-- * @SigYank@    — feedback / trace over a tensor @t@
-- * @SigPar@     — parallel composition (the tensor product ⊗)
-- * @SigShared@  — shared-medium fusion (the par product ⅋), parameterised by a schedule
-- * @SigMediate@ — exponential / why-not (@?@), parameterised by a mediator
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
    SigMediate (..),
    SigPar (..),
    SigShared (..),
    SigSwap (..),
    SigCopy (..),
    SigDiscard (..),
    SigCopyDiscard,
    SigPlus (..),
    SigZero (..),
    SigMergeZero,

    -- * Mediator interpretation
    Mediable (..),

    -- * Common syntax combinations
    AlgSMC,
    AlgShared,
    AlgMediate,
    AlgRelevant,
    AlgAffine,
    AlgCartesian,
    AlgCoRelevant,
    AlgCoAffine,
    AlgCocartesian,
    AlgBimonoidal,
    AlgNet,

    -- * Direct <-> algebra isomorphisms
    algMediate,
    algNet,
    runAlgNet,
  )
where

import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Dagger qualified as Dg
import Circuit.Mediate (Mediator (..), runMediator)
import Circuit.Net qualified as N
import Circuit.SMC (SMC (..))
import Circuit.Shared (Bias (..), Fire, Schedule (..), Shared (..), sharedBy)
import Circuit.Syntax
  ( Algebra (..),
    AlgCat,
    Sig,
    SigCompose (..),
    Syntax (..),
    (:+:) (..),
    eval,
    evalInto,
  )
import Circuit.Tensor (Action (..), Tensor (..), Unit)
import Circuit.Trace (SigYank (..), Trace, base, yank)
import Data.Kind (Constraint, Type)
import Data.These (These (..))
import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- Individual signatures

-- | Parallel composition (the tensor product ⊗).
--
-- This is the monoidal product over independent state.  It is sound as a
-- bifunctor in any 'Tensor' category; it does not represent shared-medium
-- fusion.  For the shared-state connective ⅋ see 'SigShared'.
data SigPar (w :: Type -> Type -> Type) arr rec a b where
  SigPar ::
    rec a b ->
    rec c d ->
    SigPar w arr rec (w a c) (w b d)

instance (Tensor w arr') => Algebra (SigPar w) arr arr' where
  type Ctx (SigPar w) arr arr' = Tensor w arr'
  alg _ rec (SigPar f g) = par (rec f) (rec g)

-- | Shared-medium fusion (the par product ⅋), parameterised by a schedule.
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

-- | Exponential / why-not (@?@): a mediator policy as a circuit constructor.
--
-- A mediator is a Mealy-style state machine with residual state @s@, input @a@,
-- and optional output @b@.  The @?@ connective embeds it as a stream morphism
-- @[a] -> [b]@.  The residual state is hidden inside the constructor; the
-- algebra interprets the policy in a target category that knows how to run
-- mediators.
--
-- This is the exponential counterpart to the additive and multiplicative
-- connectives: while 'SigCopyDiscard' gives explicit copy/discard capability,
-- 'SigMediate' is the policy that the exponential modalises.
data SigMediate arr rec a b where
  SigMediate :: Mediator s a b -> SigMediate arr rec [a] [b]

-- | Categories that can interpret a mediator as a morphism.
--
-- The canonical instance is over functions, where a mediator denotes the
-- causal stream function @[a] -> [b]@ obtained by running from its seed.
-- Other instances (stateful arrows, Kleisli arrows with state) can be added
-- as needed.
class Mediable arr where
  mediate :: Mediator s a b -> arr [a] [b]

-- | Functions interpret a mediator by running it as a stream transducer.
instance Mediable (->) where
  mediate = runMediator

instance (Mediable arr') => Algebra SigMediate arr arr' where
  type Ctx SigMediate arr arr' = Mediable arr'
  alg _ _ (SigMediate med) = mediate med

-- | Symmetric braiding.
data SigSwap (w :: Type -> Type -> Type) arr rec a b where
  SigSwap :: SigSwap w arr rec (w a b) (w b a)

instance (Action w arr') => Algebra (SigSwap w) arr arr' where
  type Ctx (SigSwap w) arr arr' = Action w arr'
  alg ::
    forall rec a b.
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    SigSwap w arr rec a b ->
    arr' a b
  alg _ _ SigSwap = swap

-- | Copy: the contraction half of the comonoid.
--
-- The constructor carries a 'Dg.CopyT' constraint on the wiring tensor @w@,
-- resolved at pattern-match time rather than in the algebra context.
data SigCopy (w :: Type -> Type -> Type) arr rec a b where
  SigCopy ::
    (Dg.CopyT w arr a) =>
    SigCopy w arr rec a (w a a)

instance Algebra (SigCopy w) arr arr' where
  type Ctx (SigCopy w) arr arr' = ()
  alg emb _ SigCopy = emb (Dg.copyT @w)

-- | Discard: the weakening half of the comonoid.
--
-- The constructor carries a 'Dg.DiscardT' constraint on the wiring tensor
-- @w@, resolved at pattern-match time rather than in the algebra context.
data SigDiscard (w :: Type -> Type -> Type) arr rec a b where
  SigDiscard ::
    (Dg.DiscardT w arr a) =>
    SigDiscard w arr rec a (Unit w)

instance Algebra (SigDiscard w) arr arr' where
  type Ctx (SigDiscard w) arr arr' = ()
  alg emb _ SigDiscard = emb (Dg.discardT @w)

-- | Comonoid operations: copy and discard.
type SigCopyDiscard w = SigCopy w :+: SigDiscard w

-- | Plus: the multiplication half of the monoid.
--
-- The constructor carries a 'Dg.MergeT' constraint on the wiring tensor @w@,
-- resolved at pattern-match time rather than in the algebra context.
data SigPlus (w :: Type -> Type -> Type) arr rec a b where
  SigPlus ::
    (Dg.MergeT w arr a) =>
    SigPlus w arr rec (w a a) a

instance Algebra (SigPlus w) arr arr' where
  type Ctx (SigPlus w) arr arr' = ()
  alg emb _ SigPlus = emb (Dg.plusT @w)

-- | Zero: the unit half of the monoid.
--
-- The constructor carries a 'Dg.ZeroT' constraint on the wiring tensor @w@,
-- resolved at pattern-match time rather than in the algebra context.
data SigZero (w :: Type -> Type -> Type) arr rec a b where
  SigZero ::
    (Dg.ZeroT w arr a) =>
    SigZero w arr rec (Unit w) a

instance Algebra (SigZero w) arr arr' where
  type Ctx (SigZero w) arr arr' = ()
  alg emb _ SigZero = emb (Dg.zeroT @w)

-- | Monoid operations: plus and zero.
type SigMergeZero w = SigPlus w :+: SigZero w

-- ---------------------------------------------------------------------------
-- Common syntax combinations

-- | Free monoidal category over wiring tensor @w@.
type AlgSMC w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w) arr

-- | Free traced category with shared-medium fusion (the ⅋ connective).
type AlgShared t arr = Syntax (SigCompose :+: SigShared t :+: SigYank t) arr

-- | Free traced category with mediator policies (the @?@ connective).
type AlgMediate t arr = Syntax (SigCompose :+: SigMediate :+: SigYank t) arr

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

-- ---------------------------------------------------------------------------
-- Direct <-> algebra isomorphisms

-- | Embed a mediator policy into the free @?@ syntax.
algMediate :: forall t arr s a b. Mediator s a b -> AlgMediate t arr [a] [b]
algMediate med = Op (R (L (SigMediate med)))

-- | Embed the direct 'N.Net' GADT into the signature-based form.
algNet :: forall w arr a b. N.Net w arr a b -> AlgNet w arr a b
algNet (N.FromSMC s) = goSMC s
  where
    goSMC :: forall x y. SMC w arr x y -> AlgNet w arr x y
    goSMC (SMCLift f) = Lift f
    goSMC (SMCCompose g f) = Op (L (SigCompose (goSMC g) (goSMC f)))
    goSMC (SMCPar f g) = Op (R (L (SigPar (goSMC f) (goSMC g))))
    goSMC SMCSwap = Op (R (R (L SigSwap)))
algNet (N.Compose g f) = Op (L (SigCompose (algNet g) (algNet f)))
algNet (N.Par f g) = Op (R (L (SigPar (algNet f) (algNet g))))
algNet N.Copy = Op (R (R (R (L SigCopy))))
algNet N.Discard = Op (R (R (R (R (L SigDiscard)))))
algNet N.Plus = Op (R (R (R (R (R (L SigPlus))))))
algNet N.Zero = Op (R (R (R (R (R (R SigZero))))))

-- | Project the signature-based Net back to the direct GADT.
runAlgNet :: forall w arr a b. AlgNet w arr a b -> N.Net w arr a b
runAlgNet = goTop
  where
    goTop :: forall x y. AlgNet w arr x y -> N.Net w arr x y
    goTop (Lift f) = N.lift f
    goTop (Op op) = goOp op

    goOp ::
      forall x y.
      (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w) arr (AlgNet w arr) x y ->
      N.Net w arr x y
    goOp (L (SigCompose g f)) = N.Compose (goTop g) (goTop f)
    goOp (R (L (SigPar f g))) = N.Par (goTop f) (goTop g)
    goOp (R (R (L SigSwap))) = N.swap
    goOp (R (R (R (L SigCopy)))) = N.Copy
    goOp (R (R (R (R (L SigDiscard))))) = N.Discard
    goOp (R (R (R (R (R (L SigPlus)))))) = N.Plus
    goOp (R (R (R (R (R (R SigZero)))))) = N.Zero
