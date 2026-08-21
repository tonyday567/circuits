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
-- Signatures expose the design space as a lattice: start with the
-- features you need, add more when you need them, and forget them via
-- algebras. The direct GADTs in "Circuit.Loop" and "Circuit.Net" are
-- the canonical circuit types; this module gives those constructions as
-- compositional syntax.
--
-- The signatures are:
--
-- * @SigCompose@ — sequential composition
-- * @SigKnot@    — feedback / trace over a tensor @t@
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
-- * @'Syntax' (@SigCompose@ ':+:' @SigKnot@ t) arr@          — free traced category
-- * @'Syntax' (@SigCompose@ ':+:' @SigPar@ ':+:' @SigSwap@) arr@ — free monoidal category
-- * @'Syntax' (@SigCompose@ ':+:' @SigShared@ t ':+:' @SigKnot@ t) arr@ — free traced category with shared-medium fusion
-- * @'Syntax' (@SigCompose@ ':+:' @SigPar@ ':+:' @SigSwap@ ':+:' 'SigCopyDiscard' ':+:' 'SigMergeZero') arr@ — Net
module Circuit.Fragment
  ( -- * Signatures
    Sig,
    (:+:) (..),

    -- * Syntax and algebra
    Syntax (..),
    Algebra (..),
    eval,
    evalInto,

    -- * Individual signatures
    SigCompose (..),
    SigKnot (..),
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
    AlgCat,
    AlgLoop,
    AlgMediate,
    AlgShared,
    AlgSMC,
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
    algLoop,
    runAlgLoop,
    algNet,
    runAlgNet,
  )
where

import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Dagger qualified as Dg
import Circuit.Layer (Layer, run)
import Circuit.Loop qualified as C
import Circuit.Mediate (Mediator (..), runMediator)
import Circuit.Net qualified as N
import Circuit.SMC (SMC (..))
import Circuit.Tensor (Action (..), Bias (..), Fire, Schedule (..), Shared (..), Tensor (..), Unit, sharedBy)
import Data.Kind (Constraint, Type)
import Data.These (These (..))
import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- Signature functors

-- | A signature describes a set of constructors for a profunctor.
--
-- * @arr@ — the base arrow (used for constructor constraints)
-- * @rec@ — the recursive arrow type being defined
-- * @a@, @b@ — input and output objects
type Sig = (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type

-- | Coproduct of signatures.
data (sig1 :+: sig2) arr rec a b where
  L :: sig1 arr rec a b -> (sig1 :+: sig2) arr rec a b
  R :: sig2 arr rec a b -> (sig1 :+: sig2) arr rec a b

infixr 6 :+:

-- ---------------------------------------------------------------------------
-- Free construction over a signature.

-- | The free construction over a signature.
data Syntax (sig :: Sig) (arr :: Type -> Type -> Type) a b where
  Lift :: arr a b -> Syntax sig arr a b
  Op :: sig arr (Syntax sig arr) a b -> Syntax sig arr a b

-- | Algebra for a signature. Interprets operations of a signature over
-- source arrow @arr@ into a target arrow @arr'@.
--
-- * @emb@ maps base arrows of the source into the target.
-- * @rec@ maps recursive sub-terms into the target.
class Algebra (sig :: Sig) (arr :: Type -> Type -> Type) (arr' :: Type -> Type -> Type) where
  type Ctx sig arr arr' :: Constraint
  type Ctx sig arr arr' = ()
  alg ::
    (Ctx sig arr arr') =>
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    sig arr rec a b ->
    arr' a b

-- | Coproduct algebra dispatches to the appropriate component.
instance (Algebra sig1 arr arr', Algebra sig2 arr arr') => Algebra (sig1 :+: sig2) arr arr' where
  type Ctx (sig1 :+: sig2) arr arr' = (Ctx sig1 arr arr', Ctx sig2 arr arr')
  alg emb rec (L op) = alg emb rec op
  alg emb rec (R op) = alg emb rec op

-- | Fold a free construction into a target arrow using its algebra.
--
-- The embedding @emb@ maps base arrows of the source into the target.
-- For folding to the same arrow, use 'eval'.
--
-- This is the à la carte analogue of 'Circuit.Layer.bind': @evalInto emb@
-- folds syntax into a target just as @bind h@ folds a 'Circuit.Layer.Layer'
-- construction. For example, folding 'AlgNet' into 'AlgLoop' is just
-- @'evalInto' 'Lift'@, playing the same role as a structural forgetting map
-- built with @bind unit@.
--
-- A signature like @@SigKnot@ t@ is best read as a type-level tag that tracks
-- which constructors are present in the union; the coproduct @(':+:')@ is the
-- union of those tags.
evalInto ::
  (Category arr', Algebra sig arr arr', Ctx sig arr arr') =>
  (forall x y. arr x y -> arr' x y) ->
  Syntax sig arr a b ->
  arr' a b
evalInto emb (Lift f) = emb f
evalInto emb (Op op) = alg emb (evalInto emb) op

-- | Fold a free construction into its own base arrow.
eval ::
  (Category arr, Algebra sig arr arr, Ctx sig arr arr) =>
  Syntax sig arr a b ->
  arr a b
eval = evalInto id

-- ---------------------------------------------------------------------------
-- Individual signatures

-- | Sequential composition.
data SigCompose arr rec a b where
  SigCompose :: rec b c -> rec a b -> SigCompose arr rec a c

instance Algebra SigCompose arr arr' where
  type Ctx SigCompose arr arr' = Category arr'
  alg ::
    forall (rec :: Type -> Type -> Type) (a :: Type) (c :: Type).
    (Ctx SigCompose arr arr') =>
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    SigCompose arr rec a c ->
    arr' a c
  alg _ rec (SigCompose @_ @_ @_ @_ @_ g f) = rec g . rec f

-- | Feedback loop / trace over tensor @t@.
data SigKnot (t :: Type -> Type -> Type) arr rec a b where
  SigKnot ::
    rec (t s a) (t s b) ->
    SigKnot t arr rec a b

instance (Traced t arr') => Algebra (SigKnot t) arr arr' where
  type Ctx (SigKnot t) arr arr' = Traced t arr'
  alg ::
    forall (rec :: Type -> Type -> Type) (b :: Type) (c :: Type).
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    SigKnot t arr rec b c ->
    arr' b c
  alg _ rec (SigKnot @_ @_ @_ @_ @_ @_ f) = trace (rec f)

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
-- produces the untraced shared body.  The surrounding 'SigKnot' closes the
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

-- | Free category.
type AlgCat arr = Syntax SigCompose arr

-- | Free traced monoidal category over tensor @t@.
type AlgLoop t arr = Syntax (SigCompose :+: SigKnot t) arr

-- | Free monoidal category over wiring tensor @w@.
type AlgSMC w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w) arr

-- | Free traced category with shared-medium fusion (the ⅋ connective).
type AlgShared t arr = Syntax (SigCompose :+: SigShared t :+: SigKnot t) arr

-- | Free traced category with mediator policies (the @?@ connective).
type AlgMediate t arr = Syntax (SigCompose :+: SigMediate :+: SigKnot t) arr

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
-- Instances for signature-based categories

instance (Category arr) => Category (AlgCat arr) where
  id = Lift id
  f . g = Op (SigCompose f g)

instance (Category arr) => Category (AlgLoop t arr) where
  id = Lift id
  f . g = Op (L (SigCompose f g))

instance (Category arr, Channel t arr) => Channel t (AlgLoop t arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  slide = Lift slide

instance (Category arr, Traced t arr) => Strength t (AlgLoop t arr) where
  strength f = Lift (strength (eval f))

instance (Category arr, Traced t arr) => Traced t (AlgLoop t arr) where
  trace body = Op (R (SigKnot body))

instance (Category arr, Traced t arr, Tensor (,) arr) => Tensor (,) (AlgLoop t arr) where
  par f g = Lift (par (eval f) (eval g))
  unitl = Lift unitl
  unitl' = Lift unitl'
  unitr = Lift unitr
  unitr' = Lift unitr'

instance (Category arr, Traced t arr, Action (,) arr) => Action (,) (AlgLoop t arr) where
  swap = Lift swap

instance (Category arr, Channel t arr) => Channel t (AlgCat arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  slide = Lift slide

instance (Category arr, Strength t arr) => Strength t (AlgCat arr) where
  strength f = Lift (strength (eval f))

instance (Category arr, Traced t arr) => Traced t (AlgCat arr) where
  trace body = Lift (trace (eval body))

-- ---------------------------------------------------------------------------
-- Direct <-> algebra isomorphisms

-- | Embed a mediator policy into the free @?@ syntax.
algMediate :: forall t arr s a b. Mediator s a b -> AlgMediate t arr [a] [b]
algMediate med = Op (R (L (SigMediate med)))

-- | Embed the direct 'C.Loop' GADT into the signature-based form.
algLoop :: forall t arr a b. C.Loop t arr a b -> AlgLoop t arr a b
algLoop (C.Lift f) = Lift f
algLoop (C.Knot f) = Op (R (SigKnot (Lift f)))

-- | Project the signature-based circuit back to the direct GADT.
--
-- @SigCompose@ nodes are interpreted using the 'Category' instance of
-- 'C.Loop', so the result is in normal form (at most one 'C.Knot').
runAlgLoop ::
  forall t a b.
  (C.FreeLoop t (->)) =>
  AlgLoop t (->) a b ->
  C.Loop t (->) a b
runAlgLoop (Lift f) = C.Lift f
runAlgLoop (Op op) = go op
  where
    go ::
      forall x y.
      (SigCompose :+: SigKnot t) (->) (AlgLoop t (->)) x y ->
      C.Loop t (->) x y
    go (L (SigCompose g f)) = runAlgLoop g . runAlgLoop f
    go (R (SigKnot @_ f)) = C.Knot (run (runAlgLoop f))

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
