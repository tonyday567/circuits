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
-- * @SigPar@     — parallel composition
-- * @SigSwap@    — symmetric braiding
-- * @SigCopyDiscard@ — copy, discard
-- * @SigMergeZero@   — plus, zero
--
-- Examples:
--
-- * @'Syntax' @SigCompose@ arr@                              — free category
-- * @'Syntax' (@SigCompose@ ':+:' @SigKnot@ t) arr@          — free traced category
-- * @'Syntax' (@SigCompose@ ':+:' @SigPar@ ':+:' @SigSwap@) arr@ — free monoidal category
-- * @'Syntax' (@SigCompose@ ':+:' @SigKnot@ t ':+:' @SigPar@ ':+:' @SigSwap@ ':+:' 'SigCopyDiscard' ':+:' 'SigMergeZero') arr@ — Net
module Circuit.Algebra
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
    SigPar (..),
    SigSwap (..),
    SigCopyDiscard (..),
    SigMergeZero (..),

    -- * Common syntax combinations
    AlgCat,
    AlgLoop,
    AlgSym,
    AlgBimonoidal,
    AlgNet,

    -- * Direct <-> algebra isomorphisms
    algLoop,
    runAlgLoop,
    algNet,
    runAlgNet,
  )
where

import Circuit.Category (Category (..), Discrete (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Dagger qualified as Dg
import Circuit.Layer (Layer, run)
import Circuit.Loop qualified as C
import Circuit.Net qualified as N
import Circuit.Tensor (Action (..), Tensor (..))
import Data.Kind (Constraint, Type)
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
  SigCompose :: (Ob arr b) => rec b c -> rec a b -> SigCompose arr rec a c

instance Algebra SigCompose arr arr' where
  type Ctx SigCompose arr arr' = Discrete arr'
  alg ::
    forall (rec :: Type -> Type -> Type) (a :: Type) (c :: Type).
    (Ctx SigCompose arr arr') =>
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    SigCompose arr rec a c ->
    arr' a c
  alg _ rec (SigCompose @_ @b1 @_ @_ @_ g f) =
    withOb @arr' @a $
      withOb @arr' @b1 $
        withOb @arr' @c $
          (rec g . rec f)

-- | Feedback loop / trace over tensor @t@.
data SigKnot (t :: Type -> Type -> Type) arr rec a b where
  SigKnot :: (Ob arr a) => rec (t a b) (t a c) -> SigKnot t arr rec b c

instance (Traced t arr') => Algebra (SigKnot t) arr arr' where
  type Ctx (SigKnot t) arr arr' = (Traced t arr', Discrete arr')
  alg ::
    forall (rec :: Type -> Type -> Type) (b :: Type) (c :: Type).
    (Ctx (SigKnot t) arr arr') =>
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    SigKnot t arr rec b c ->
    arr' b c
  alg _ rec (SigKnot @_ @a1 @_ @_ @_ @_ f) =
    withOb @arr' @a1 $
      withOb @arr' @b $
        withOb @arr' @c $
          withOb @arr' @(t a1 b) $
            withOb @arr' @(t a1 c) $
              trace (rec f)

-- | Parallel composition.
data SigPar arr rec a b where
  SigPar :: rec a b -> rec c d -> SigPar arr rec (a, c) (b, d)

instance (Tensor (,) arr') => Algebra SigPar arr arr' where
  type Ctx SigPar arr arr' = Tensor (,) arr'
  alg _ rec (SigPar f g) = par (rec f) (rec g)

-- | Symmetric braiding.
data SigSwap arr rec a b where
  SigSwap :: SigSwap arr rec (a, b) (b, a)

instance (Action (,) arr') => Algebra SigSwap arr arr' where
  type Ctx SigSwap arr arr' = Action (,) arr'
  alg _ _ SigSwap = swap

-- | Comonoid operations: copy, discard.
--
-- Each constructor carries its own 'Dg.CopyDiscard' constraint, resolved at
-- pattern-match time rather than in the algebra context.
data SigCopyDiscard arr rec a b where
  SigCopy :: (Dg.CopyDiscard arr a) => SigCopyDiscard arr rec a (a, a)
  SigDiscard :: (Dg.CopyDiscard arr a) => SigCopyDiscard arr rec a ()

-- | 'alg' for copy/discard generators sends each generator to the image
-- under @emb@ of the source dictionary.
instance Algebra SigCopyDiscard arr arr' where
  alg ::
    forall rec i o.
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    SigCopyDiscard arr rec i o ->
    arr' i o
  alg emb _ SigCopy = emb (Dg.copy :: arr i (i, i))
  alg emb _ SigDiscard = emb (Dg.discard :: arr i ())

-- | Monoid operations: plus, zero.
--
-- Each constructor carries its own 'Dg.MergeZero' constraint, resolved at
-- pattern-match time rather than in the algebra context.
data SigMergeZero arr rec a b where
  SigPlus :: (Dg.MergeZero arr a) => SigMergeZero arr rec (a, a) a
  SigZero :: (Dg.MergeZero arr a) => SigMergeZero arr rec () a

-- | 'alg' for plus/zero generators sends each generator to the image under
-- @emb@ of the source dictionary.
instance Algebra SigMergeZero arr arr' where
  alg ::
    forall rec i o.
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    SigMergeZero arr rec i o ->
    arr' i o
  alg emb _ SigPlus = emb (Dg.plus :: arr (o, o) o)
  alg emb _ SigZero = emb (Dg.zero :: arr () o)

-- ---------------------------------------------------------------------------
-- Common syntax combinations

-- | Free category.
type AlgCat arr = Syntax SigCompose arr

-- | Free traced monoidal category over tensor @t@.
type AlgLoop t arr = Syntax (SigCompose :+: SigKnot t) arr

-- | Free monoidal category.
type AlgSym arr = Syntax (SigCompose :+: SigPar :+: SigSwap) arr

-- | Free bimonoidal category.
type AlgBimonoidal arr = Syntax (SigCompose :+: SigPar :+: SigSwap :+: SigCopyDiscard :+: SigMergeZero) arr

-- | Free traced PROP with bimonoid.
type AlgNet t arr = Syntax (SigCompose :+: SigKnot t :+: SigPar :+: SigSwap :+: SigCopyDiscard :+: SigMergeZero) arr

-- ---------------------------------------------------------------------------
-- Instances for signature-based categories

instance (Category arr) => Category (AlgCat arr) where
  type Ob (AlgCat arr) a = Ob arr a
  id = Lift id
  f . g = Op (SigCompose f g)

instance (Category arr) => Category (AlgLoop t arr) where
  type Ob (AlgLoop t arr) a = Ob arr a
  id = Lift id
  f . g = Op (L (SigCompose f g))

instance (Category arr, Channel t arr) => Channel t (AlgLoop t arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  slide = Lift slide

instance (Category arr, Traced t arr, Discrete arr) => Strength t (AlgLoop t arr) where
  strength f = Lift (strength (eval f))

instance (Category arr, Traced t arr, Discrete arr) => Traced t (AlgLoop t arr) where
  trace body = Op (R (SigKnot body))

instance (Category arr, Traced t arr, Tensor (,) arr, Discrete arr) => Tensor (,) (AlgLoop t arr) where
  par f g = Lift (par (eval f) (eval g))
  unitl = Lift unitl
  unitl' = Lift unitl'
  unitr = Lift unitr
  unitr' = Lift unitr'

instance (Category arr, Traced t arr, Action (,) arr, Discrete arr) => Action (,) (AlgLoop t arr) where
  swap = Lift swap

instance (Category arr, Channel t arr) => Channel t (AlgCat arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  slide = Lift slide

instance (Category arr, Strength t arr, Discrete arr) => Strength t (AlgCat arr) where
  strength f = Lift (strength (eval f))

instance (Category arr, Traced t arr, Discrete arr) => Traced t (AlgCat arr) where
  trace body = Lift (trace (eval body))

-- | A discrete base yields discrete syntax.
--
-- These instances are needed so that 'evalInto Lift' can fold richer syntax
-- into poorer syntax (e.g. 'AlgLoop' into 'AlgCat', 'AlgNet' into 'AlgLoop').
instance (Category arr, Discrete arr) => Discrete (AlgCat arr) where
  withOb @a x = withOb @arr @a x

instance (Category arr, Discrete arr) => Discrete (AlgLoop t arr) where
  withOb @a x = withOb @arr @a x

-- ---------------------------------------------------------------------------
-- Direct <-> algebra isomorphisms

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
algNet :: forall t arr a b. N.Net t arr a b -> AlgNet t arr a b
algNet (N.Lift f) = Lift f
algNet (N.Compose g f) = Op (L (SigCompose (algNet g) (algNet f)))
algNet (N.Par f g) = Op (R (R (L (SigPar (algNet f) (algNet g)))))
algNet N.Swap = Op (R (R (R (L SigSwap))))
algNet N.Copy = Op (R (R (R (R (L SigCopy)))))
algNet N.Discard = Op (R (R (R (R (L SigDiscard)))))
algNet N.Plus = Op (R (R (R (R (R SigPlus)))))
algNet N.Zero = Op (R (R (R (R (R SigZero)))))
algNet (N.Knot f) = Op (R (L (SigKnot (algNet f))))

-- | Project the signature-based Net back to the direct GADT.
runAlgNet :: forall t arr a b. AlgNet t arr a b -> N.Net t arr a b
runAlgNet = goTop
  where
    goTop :: forall x y. AlgNet t arr x y -> N.Net t arr x y
    goTop (Lift f) = N.Lift f
    goTop (Op op) = goOp op

    goOp :: forall x y. (SigCompose :+: SigKnot t :+: SigPar :+: SigSwap :+: SigCopyDiscard :+: SigMergeZero) arr (AlgNet t arr) x y -> N.Net t arr x y
    goOp (L sc) = goCompose sc
    goOp (R rest) = goKnotOrMore rest

    goCompose :: forall x y. SigCompose arr (AlgNet t arr) x y -> N.Net t arr x y
    goCompose (SigCompose g f) = N.Compose (goTop g) (goTop f)

    goKnotOrMore :: forall x y. (SigKnot t :+: SigPar :+: SigSwap :+: SigCopyDiscard :+: SigMergeZero) arr (AlgNet t arr) x y -> N.Net t arr x y
    goKnotOrMore (L sk) = goKnot sk
    goKnotOrMore (R rest) = goParOrMore rest

    goKnot :: forall x y. SigKnot t arr (AlgNet t arr) x y -> N.Net t arr x y
    goKnot (SigKnot f) = N.Knot (goTop f)

    goParOrMore :: forall x y. (SigPar :+: SigSwap :+: SigCopyDiscard :+: SigMergeZero) arr (AlgNet t arr) x y -> N.Net t arr x y
    goParOrMore (L sp) = goPar sp
    goParOrMore (R rest) = goSwapOrMonoid rest

    goPar :: forall x y. SigPar arr (AlgNet t arr) x y -> N.Net t arr x y
    goPar (SigPar f g) = N.Par (goTop f) (goTop g)

    goSwapOrMonoid :: forall x y. (SigSwap :+: SigCopyDiscard :+: SigMergeZero) arr (AlgNet t arr) x y -> N.Net t arr x y
    goSwapOrMonoid (L SigSwap) = N.Swap
    goSwapOrMonoid (R rest) = goCopyDiscardOrMergeZero rest

    goCopyDiscardOrMergeZero :: forall x y. (SigCopyDiscard :+: SigMergeZero) arr (AlgNet t arr) x y -> N.Net t arr x y
    goCopyDiscardOrMergeZero (L scd) = goCopyDiscard scd
    goCopyDiscardOrMergeZero (R smz) = goMergeZero smz

    goCopyDiscard :: forall x y. SigCopyDiscard arr (AlgNet t arr) x y -> N.Net t arr x y
    goCopyDiscard SigCopy = N.Copy
    goCopyDiscard SigDiscard = N.Discard

    goMergeZero :: forall x y. SigMergeZero arr (AlgNet t arr) x y -> N.Net t arr x y
    goMergeZero SigPlus = N.Plus
    goMergeZero SigZero = N.Zero
