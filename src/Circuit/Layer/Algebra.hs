{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
-- This module is a /design tool/, not the working API. The direct
-- GADTs in "Circuit.Trace" and "Circuit.Net" remain the canonical
-- implementation. Signatures are useful for prototyping new features
-- and making the adjunction lattice explicit.
--
-- The signatures are:
--
-- * 'SigCompose' — sequential composition
-- * 'SigKnot'    — feedback / trace over a tensor @t@
-- * 'SigPar'     — parallel composition
-- * 'SigSwap'    — symmetric braiding
-- * 'SigBimonoid'— copy, discard, plus, zero
--
-- Examples:
--
-- * @'Syntax' 'SigCompose' arr@                              — free category
-- * @'Syntax' ('SigCompose' ':+:' 'SigKnot' t) arr@          — free traced category
-- * @'Syntax' ('SigCompose' ':+:' 'SigPar' ':+:' 'SigSwap') arr@ — free monoidal category
-- * @'Syntax' ('SigCompose' ':+:' 'SigKnot' t ':+:' 'SigPar' ':+:' 'SigSwap' ':+:' 'SigBimonoid') arr@ — Net
module Circuit.Layer.Algebra
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
    SigBimonoid (..),

    -- * Common syntax combinations
    AlgCat,
    AlgTrace,
    AlgMonoidal,
    AlgBimonoidal,
    AlgNet,

    -- * Forgetful algebras
    algFreeze,
    algMelt,

    -- * Direct <-> algebra isomorphisms
    traceToAlg,
    algToTrace,
    netToAlg,
    algToNet,

    -- * TraceMon <-> algebra maps
    monKnotToTrace,
    traceToMonKnot,
  )
where

import Circuit.Dagger qualified as Dg
import Circuit.Layer (Layer, run)
import Circuit.Monoidal (Action (..), Tensor (..))
import Circuit.Monoidal.Category (Monoidal (..))
import Circuit.Net qualified as N
import Circuit.Trace (Traced (..), compD, traceD)
import Circuit.Trace qualified as C
import Circuit.Classes (Category (..), Discrete (..))
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

instance (Category arr') => Algebra SigCompose arr arr' where
  type Ctx SigCompose arr arr' = Discrete arr'
  alg _ rec (SigCompose g f) = rec g `compD` rec f

-- | Feedback loop / trace over tensor @t@.
data SigKnot (t :: Type -> Type -> Type) arr rec a b where
  SigKnot :: rec (t a b) (t a c) -> SigKnot t arr rec b c

instance (Traced t arr') => Algebra (SigKnot t) arr arr' where
  type Ctx (SigKnot t) arr arr' = (Traced t arr', Discrete arr')
  alg _ rec (SigKnot f) = traceD (rec f)

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

-- | Bimonoid operations: copy, discard, plus, zero.
--
-- Each constructor carries its own 'Dg.Bimonoid' constraint, resolved at
-- pattern-match time rather than in the algr context.
data SigBimonoid arr rec a b where
  SigCopy :: (Dg.Bimonoid arr a) => SigBimonoid arr rec a (a, a)
  SigDiscard :: (Dg.Bimonoid arr a) => SigBimonoid arr rec a ()
  SigPlus :: (Dg.Bimonoid arr a) => SigBimonoid arr rec (a, a) a
  SigZero :: (Dg.Bimonoid arr a) => SigBimonoid arr rec () a

instance Algebra SigBimonoid arr arr' where
  alg ::
    forall rec i o.
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    SigBimonoid arr rec i o ->
    arr' i o
  alg emb _ SigCopy = emb (Dg.copy :: arr i (i, i))
  alg emb _ SigDiscard = emb (Dg.discard :: arr i ())
  alg emb _ SigPlus = emb (Dg.plus :: arr (o, o) o)
  alg emb _ SigZero = emb (Dg.zero :: arr () o)

-- ---------------------------------------------------------------------------
-- Common syntax combinations

-- | Free category.
type AlgCat arr = Syntax SigCompose arr

-- | Free traced monoidal category over tensor @t@.
type AlgTrace t arr = Syntax (SigCompose :+: SigKnot t) arr

-- | Free monoidal category.
type AlgMonoidal arr = Syntax (SigCompose :+: SigPar :+: SigSwap) arr

-- | Free bimonoidal category.
type AlgBimonoidal arr = Syntax (SigCompose :+: SigPar :+: SigSwap :+: SigBimonoid) arr

-- | Free traced PROP with bimonoid.
type AlgNet t arr = Syntax (SigCompose :+: SigKnot t :+: SigPar :+: SigSwap :+: SigBimonoid) arr

-- | Free traced monoidal category — the 'TraceMon' layer made real.
--
-- Both the trace ('SigKnot') and the monoidal product ('SigPar'/'SigSwap')
-- are explicit syntax.  This is the conceptual middle ground between
-- 'AlgMonoidal' and 'AlgTrace'.
type AlgMonKnot t arr = Syntax (SigCompose :+: SigKnot t :+: SigPar :+: SigSwap) arr

-- ---------------------------------------------------------------------------
-- Instances for signature-based categories

instance (Category arr) => Category (AlgCat arr) where
  type Ob (AlgCat arr) a = Ob arr a
  id = Lift id
  f . g = Op (SigCompose f g)

instance Discrete (AlgCat (->)) where
  withOb x = x

instance (Category arr) => Category (AlgTrace t arr) where
  type Ob (AlgTrace t arr) a = Ob arr a
  id = Lift id
  f . g = Op (L (SigCompose f g))

instance Discrete (AlgTrace t (->)) where
  withOb x = x

instance (Category arr, Monoidal t arr) => Monoidal t (AlgTrace t arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  braid = Lift braid

instance (Category arr, Traced t arr, Discrete arr) => Traced t (AlgTrace t arr) where
  trace body = Op (R (SigKnot body))
  untrace f = Lift (untrace (eval f))

instance (Category arr, Traced t arr, Tensor (,) arr, Discrete arr) => Tensor (,) (AlgTrace t arr) where
  par f g = Lift (par (eval f) (eval g))
  unitl = Lift unitl
  unitl' = Lift unitl'
  unitr = Lift unitr
  unitr' = Lift unitr'

instance (Category arr, Traced t arr, Action (,) arr, Discrete arr) => Action (,) (AlgTrace t arr) where
  swap = Lift swap

instance (Category arr, Monoidal t arr) => Monoidal t (AlgCat arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  braid = Lift braid

instance (Category arr, Traced t arr, Discrete arr) => Traced t (AlgCat arr) where
  trace body = Lift (trace (eval body))
  untrace f = Lift (untrace (eval f))

-- ---------------------------------------------------------------------------
-- Forgetful algrs

-- | Dissolve 'SigKnot' into 'SigCompose' by calling the base 'trace' on the
-- free category.  This is the forgetful map from the free traced
-- category to the free category.
algFreeze ::
  (Traced t (->)) =>
  AlgTrace t (->) a b ->
  AlgCat (->) a b
algFreeze = evalInto Lift

-- | Melt structural rows ('SigPar', 'SigSwap', 'SigBimonoid') into 'Lift'
-- calls.  This is the forgetful map from 'AlgNet' to 'AlgTrace'.
algMelt ::
  (Traced t (->), Action (,) (->)) =>
  AlgNet t (->) a b ->
  AlgTrace t (->) a b
algMelt = evalInto Lift

-- ---------------------------------------------------------------------------
-- Direct <-> signature isomorphisms

-- | Embed the direct 'C.Trace' GADT into the signature-based form.
traceToAlg :: forall t arr a b. C.Trace t arr a b -> AlgTrace t arr a b
traceToAlg (C.Arr f) = Lift f
traceToAlg (C.Knot f) = Op (R (SigKnot (Lift f)))

-- | Project the signature-based circuit back to the direct GADT.
--
-- 'SigCompose' nodes are interpreted using the 'Category' instance of
-- 'C.Trace', so the result is in normal form (at most one 'C.Knot').
algToTrace ::
  forall t a b.
  (Traced t (->)) =>
  AlgTrace t (->) a b ->
  C.Trace t (->) a b
algToTrace (Lift f) = C.Arr f
algToTrace (Op op) = go op
  where
    go ::
      forall x y.
      (SigCompose :+: SigKnot t) (->) (AlgTrace t (->)) x y ->
      C.Trace t (->) x y
    go (L (SigCompose g f)) = algToTrace g . algToTrace f
    go (R (SigKnot f)) = C.Knot (run (algToTrace f))

-- | Forget the explicit monoidal rows of 'AlgMonKnot', collapsing them
-- into the base arrow and leaving only 'SigCompose' and 'SigKnot'.
--
-- This is the signature-based version of 'melt' restricted to the
-- TraceMon layer.
monKnotToTrace ::
  forall t a b.
  (Traced t (->), Action (,) (->)) =>
  AlgMonKnot t (->) a b ->
  AlgTrace t (->) a b
monKnotToTrace = evalInto Lift

-- | Embed 'AlgTrace' into 'AlgMonKnot' by constructor injection.
traceToMonKnot ::
  forall t arr a b.
  AlgTrace t arr a b ->
  AlgMonKnot t arr a b
traceToMonKnot (Lift f) = Lift f
traceToMonKnot (Op op) = goOp op
  where
    goOp ::
      forall x y.
      (SigCompose :+: SigKnot t) arr (AlgTrace t arr) x y ->
      AlgMonKnot t arr x y
    goOp (L (SigCompose g f)) =
      Op (L (SigCompose (traceToMonKnot g) (traceToMonKnot f)))
    goOp (R (SigKnot f)) =
      Op (R (L (SigKnot (traceToMonKnot f))))

-- | Embed the direct 'N.Net' GADT into the signature-based form.
netToAlg :: forall t arr a b. N.Net t arr a b -> AlgNet t arr a b
netToAlg (N.Lift f) = Lift f
netToAlg (N.Compose g f) = Op (L (SigCompose (netToAlg g) (netToAlg f)))
netToAlg (N.Par f g) = Op (R (R (L (SigPar (netToAlg f) (netToAlg g)))))
netToAlg N.Swap = Op (R (R (R (L SigSwap))))
netToAlg N.Copy = Op (R (R (R (R SigCopy))))
netToAlg N.Discard = Op (R (R (R (R SigDiscard))))
netToAlg N.Plus = Op (R (R (R (R SigPlus))))
netToAlg N.Zero = Op (R (R (R (R SigZero))))
netToAlg (N.Knot f) = Op (R (L (SigKnot (netToAlg f))))

-- | Project the signature-based Net back to the direct GADT.
algToNet :: forall t arr a b. AlgNet t arr a b -> N.Net t arr a b
algToNet = goTop
  where
    goTop :: forall x y. AlgNet t arr x y -> N.Net t arr x y
    goTop (Lift f) = N.Lift f
    goTop (Op op) = goOp op

    goOp :: forall x y. (SigCompose :+: SigKnot t :+: SigPar :+: SigSwap :+: SigBimonoid) arr (AlgNet t arr) x y -> N.Net t arr x y
    goOp (L sc) = goCompose sc
    goOp (R rest) = goKnotOrMore rest

    goCompose :: forall x y. SigCompose arr (AlgNet t arr) x y -> N.Net t arr x y
    goCompose (SigCompose g f) = N.Compose (goTop g) (goTop f)

    goKnotOrMore :: forall x y. (SigKnot t :+: SigPar :+: SigSwap :+: SigBimonoid) arr (AlgNet t arr) x y -> N.Net t arr x y
    goKnotOrMore (L sk) = goKnot sk
    goKnotOrMore (R rest) = goParOrMore rest

    goKnot :: forall x y. SigKnot t arr (AlgNet t arr) x y -> N.Net t arr x y
    goKnot (SigKnot f) = N.Knot (goTop f)

    goParOrMore :: forall x y. (SigPar :+: SigSwap :+: SigBimonoid) arr (AlgNet t arr) x y -> N.Net t arr x y
    goParOrMore (L sp) = goPar sp
    goParOrMore (R rest) = goSwapOrBimonoid rest

    goPar :: forall x y. SigPar arr (AlgNet t arr) x y -> N.Net t arr x y
    goPar (SigPar f g) = N.Par (goTop f) (goTop g)

    goSwapOrBimonoid :: forall x y. (SigSwap :+: SigBimonoid) arr (AlgNet t arr) x y -> N.Net t arr x y
    goSwapOrBimonoid (L SigSwap) = N.Swap
    goSwapOrBimonoid (R sb) = goBimonoid sb

    goBimonoid :: forall x y. SigBimonoid arr (AlgNet t arr) x y -> N.Net t arr x y
    goBimonoid SigCopy = N.Copy
    goBimonoid SigDiscard = N.Discard
    goBimonoid SigPlus = N.Plus
    goBimonoid SigZero = N.Zero
