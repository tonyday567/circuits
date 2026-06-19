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

-- | Signatures and free constructions for modular circuit syntax.
--
-- Each language feature is a signature functor.  A GADT is the free
-- construction over a chosen combination of signatures.  This makes
-- the design space a lattice: start with the features you need, add
-- more when you need them, and forget them via handlers.
--
-- This module is a /design tool/, not the working API.  The direct
-- GADTs in "Circuit.Trace" and "Circuit.Net" remain the canonical
-- implementation.  Signatures are useful for prototyping new features
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
-- * @'Free' 'SigCompose' arr@                              — free category
-- * @'Free' ('SigCompose' ':+:' 'SigKnot' t) arr@          — free traced category
-- * @'Free' ('SigCompose' ':+:' 'SigPar' ':+:' 'SigSwap') arr@ — free monoidal category
-- * @'Free' ('SigCompose' ':+:' 'SigKnot' t ':+:' 'SigPar' ':+:' 'SigSwap' ':+:' 'SigBimonoid') arr@ — Net
module Circuit.Signature
  ( -- * Signatures
    Sig,
    (:+:) (..),

    -- * Free construction
    Free (..),
    Handler (..),
    fold,
    foldInto,

    -- * Individual signatures
    SigCompose (..),
    SigKnot (..),
    SigPar (..),
    SigSwap (..),
    SigBimonoid (..),

    -- * Common syntax combinations
    SigFreeCat,
    SigTrace,
    SigMonoidal,
    SigBimonoidal,
    SigNet,

    -- * Forgetful handlers
    sigFreeze,
    sigMelt,

    -- * Direct <-> signature isomorphisms
    traceToSig,
    sigToTrace,
    netToSig,
    sigToNet,
  )
where

import Circuit.Dagger qualified as Dg
import Circuit.Monoidal (MonoidalP (..))
import Circuit.Net qualified as N
import Circuit.Trace qualified as C
import Circuit.Traced
import Control.Category (Category (..))
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
-- Free construction

-- | The free construction over a signature.
data Free (sig :: Sig) (arr :: Type -> Type -> Type) a b where
  Lift :: arr a b -> Free sig arr a b
  Op :: sig arr (Free sig arr) a b -> Free sig arr a b

-- | Handler for a signature.  Interprets operations of a signature over
-- source arrow @arr@ into a target arrow @arr'@.
--
-- * @emb@ maps base arrows of the source into the target.
-- * @eval@ maps recursive sub-terms into the target.
class Handler (sig :: Sig) (arr :: Type -> Type -> Type) (arr' :: Type -> Type -> Type) where
  type HCtx sig arr arr' :: Constraint
  type HCtx sig arr arr' = ()
  handle ::
    (HCtx sig arr arr') =>
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    sig arr rec a b ->
    arr' a b

-- | Handler for a coproduct dispatches to the appropriate component.
instance (Handler sig1 arr arr', Handler sig2 arr arr') => Handler (sig1 :+: sig2) arr arr' where
  type HCtx (sig1 :+: sig2) arr arr' = (HCtx sig1 arr arr', HCtx sig2 arr arr')
  handle emb eval (L op) = handle emb eval op
  handle emb eval (R op) = handle emb eval op

-- | Fold a free construction into a target arrow using its handler.
--
-- The embedding @emb@ maps base arrows of the source into the target.
-- For folding to the same arrow, use 'fold'.
foldInto ::
  (Category arr', Handler sig arr arr', HCtx sig arr arr') =>
  (forall x y. arr x y -> arr' x y) ->
  Free sig arr a b ->
  arr' a b
foldInto emb (Lift f) = emb f
foldInto emb (Op op) = handle emb (foldInto emb) op

-- | Fold a free construction into its own base arrow.
fold ::
  (Category arr, Handler sig arr arr, HCtx sig arr arr) =>
  Free sig arr a b ->
  arr a b
fold = foldInto id

-- ---------------------------------------------------------------------------
-- Individual signatures

-- | Sequential composition.
data SigCompose arr rec a b where
  SigCompose :: rec b c -> rec a b -> SigCompose arr rec a c

instance (Category arr') => Handler SigCompose arr arr' where
  type HCtx SigCompose arr arr' = Category arr'
  handle _ eval (SigCompose g f) = eval g . eval f

-- | Feedback loop / trace over tensor @t@.
data SigKnot (t :: Type -> Type -> Type) arr rec a b where
  SigKnot :: rec (t a b) (t a c) -> SigKnot t arr rec b c

instance (Traced arr' t) => Handler (SigKnot t) arr arr' where
  type HCtx (SigKnot t) arr arr' = Traced arr' t
  handle _ eval (SigKnot f) = trace (eval f)

-- | Parallel composition.
data SigPar arr rec a b where
  SigPar :: rec a b -> rec c d -> SigPar arr rec (a, c) (b, d)

instance (MonoidalP arr') => Handler SigPar arr arr' where
  type HCtx SigPar arr arr' = MonoidalP arr'
  handle _ eval (SigPar f g) = par (eval f) (eval g)

-- | Symmetric braiding.
data SigSwap arr rec a b where
  SigSwap :: SigSwap arr rec (a, b) (b, a)

instance (MonoidalP arr') => Handler SigSwap arr arr' where
  type HCtx SigSwap arr arr' = MonoidalP arr'
  handle _ _ SigSwap = swap

-- | Bimonoid operations: copy, discard, plus, zero.
--
-- Each constructor carries its own 'Bimonoid' constraint, resolved at
-- pattern-match time rather than in the handler context.
data SigBimonoid arr rec a b where
  SigCopy :: (Dg.Bimonoid arr a) => SigBimonoid arr rec a (a, a)
  SigDiscard :: (Dg.Bimonoid arr a) => SigBimonoid arr rec a ()
  SigPlus :: (Dg.Bimonoid arr a) => SigBimonoid arr rec (a, a) a
  SigZero :: (Dg.Bimonoid arr a) => SigBimonoid arr rec () a

instance Handler SigBimonoid arr arr' where
  handle ::
    forall rec i o.
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    SigBimonoid arr rec i o ->
    arr' i o
  handle emb _ SigCopy = emb (Dg.copy :: arr i (i, i))
  handle emb _ SigDiscard = emb (Dg.discard :: arr i ())
  handle emb _ SigPlus = emb (Dg.plus :: arr (o, o) o)
  handle emb _ SigZero = emb (Dg.zero :: arr () o)

-- ---------------------------------------------------------------------------
-- Common syntax combinations

-- | Free category.
type SigFreeCat arr = Free SigCompose arr

-- | Free traced monoidal category over tensor @t@.
type SigTrace t arr = Free (SigCompose :+: SigKnot t) arr

-- | Free monoidal category.
type SigMonoidal arr = Free (SigCompose :+: SigPar :+: SigSwap) arr

-- | Free bimonoidal category.
type SigBimonoidal arr = Free (SigCompose :+: SigPar :+: SigSwap :+: SigBimonoid) arr

-- | Free traced PROP with bimonoid.
type SigNet t arr = Free (SigCompose :+: SigKnot t :+: SigPar :+: SigSwap :+: SigBimonoid) arr

-- ---------------------------------------------------------------------------
-- Instances for signature-based categories

instance (Category arr) => Category (SigFreeCat arr) where
  id = Lift id
  f . g = Op (SigCompose f g)

instance (Category arr) => Category (SigTrace t arr) where
  id = Lift id
  f . g = Op (L (SigCompose f g))

instance (Category arr, Traced arr t) => Traced (SigTrace t arr) t where
  trace body = Op (R (SigKnot body))
  untrace f = Lift (untrace (fold f))

instance (Category arr, Traced arr t, MonoidalP arr) => MonoidalP (SigTrace t arr) where
  par f g = Lift (par (fold f) (fold g))
  swap = Lift swap

instance (Category arr, Traced arr t) => Traced (SigFreeCat arr) t where
  trace body = Lift (trace (fold body))
  untrace f = Lift (untrace (fold f))

-- ---------------------------------------------------------------------------
-- Forgetful handlers

-- | Dissolve 'SigKnot' into 'SigCompose' by calling the base 'trace' on the
-- free category.  This is the forgetful map from the free traced
-- category to the free category.
sigFreeze ::
  (Category arr, Traced arr t) =>
  SigTrace t arr a b ->
  SigFreeCat arr a b
sigFreeze = foldInto Lift

-- | Melt structural rows ('SigPar', 'SigSwap', 'SigBimonoid') into 'Lift'
-- calls.  This is the forgetful map from 'SigNet' to 'SigTrace'.
sigMelt ::
  (Traced arr t, MonoidalP arr) =>
  SigNet t arr a b ->
  SigTrace t arr a b
sigMelt = foldInto Lift

-- ---------------------------------------------------------------------------
-- Direct <-> signature isomorphisms

-- | Embed the direct 'C.Trace' GADT into the signature-based form.
traceToSig :: forall t arr a b. C.Trace t arr a b -> SigTrace t arr a b
traceToSig (C.Lift f) = Lift f
traceToSig (C.Compose g f) = Op (L (SigCompose (traceToSig g) (traceToSig f)))
traceToSig (C.Trace f) = Op (R (SigKnot (traceToSig f)))

-- | Project the signature-based circuit back to the direct GADT.
sigToTrace :: forall t arr a b. SigTrace t arr a b -> C.Trace t arr a b
sigToTrace = go
  where
    go :: forall x y. SigTrace t arr x y -> C.Trace t arr x y
    go (Lift f) = C.Lift f
    go (Op op) = goOp op

    goOp :: forall x y. (SigCompose :+: SigKnot t) arr (SigTrace t arr) x y -> C.Trace t arr x y
    goOp (L sc) = case sc of
      SigCompose g f -> C.Compose (go g) (go f)
    goOp (R sk) = case sk of
      SigKnot f -> C.Trace (go f)

-- | Embed the direct 'N.Net' GADT into the signature-based form.
netToSig :: forall t arr a b. N.Net t arr a b -> SigNet t arr a b
netToSig (N.Lift f) = Lift f
netToSig (N.Compose g f) = Op (L (SigCompose (netToSig g) (netToSig f)))
netToSig (N.Par f g) = Op (R (R (L (SigPar (netToSig f) (netToSig g)))))
netToSig N.Swap = Op (R (R (R (L SigSwap))))
netToSig N.Copy = Op (R (R (R (R SigCopy))))
netToSig N.Discard = Op (R (R (R (R SigDiscard))))
netToSig N.Plus = Op (R (R (R (R SigPlus))))
netToSig N.Zero = Op (R (R (R (R SigZero))))
netToSig (N.Trace f) = Op (R (L (SigKnot (netToSig f))))

-- | Project the signature-based Net back to the direct GADT.
sigToNet :: forall t arr a b. SigNet t arr a b -> N.Net t arr a b
sigToNet = goTop
  where
    goTop :: forall x y. SigNet t arr x y -> N.Net t arr x y
    goTop (Lift f) = N.Lift f
    goTop (Op op) = goOp op

    goOp :: forall x y. (SigCompose :+: SigKnot t :+: SigPar :+: SigSwap :+: SigBimonoid) arr (SigNet t arr) x y -> N.Net t arr x y
    goOp (L sc) = goCompose sc
    goOp (R rest) = goKnotOrMore rest

    goCompose :: forall x y. SigCompose arr (SigNet t arr) x y -> N.Net t arr x y
    goCompose (SigCompose g f) = N.Compose (goTop g) (goTop f)

    goKnotOrMore :: forall x y. (SigKnot t :+: SigPar :+: SigSwap :+: SigBimonoid) arr (SigNet t arr) x y -> N.Net t arr x y
    goKnotOrMore (L sk) = goKnot sk
    goKnotOrMore (R rest) = goParOrMore rest

    goKnot :: forall x y. SigKnot t arr (SigNet t arr) x y -> N.Net t arr x y
    goKnot (SigKnot f) = N.Trace (goTop f)

    goParOrMore :: forall x y. (SigPar :+: SigSwap :+: SigBimonoid) arr (SigNet t arr) x y -> N.Net t arr x y
    goParOrMore (L sp) = goPar sp
    goParOrMore (R rest) = goSwapOrBimonoid rest

    goPar :: forall x y. SigPar arr (SigNet t arr) x y -> N.Net t arr x y
    goPar (SigPar f g) = N.Par (goTop f) (goTop g)

    goSwapOrBimonoid :: forall x y. (SigSwap :+: SigBimonoid) arr (SigNet t arr) x y -> N.Net t arr x y
    goSwapOrBimonoid (L ss) = goSwap ss
    goSwapOrBimonoid (R sb) = goBimonoid sb

    goSwap :: forall x y. SigSwap arr (SigNet t arr) x y -> N.Net t arr x y
    goSwap SigSwap = N.Swap

    goBimonoid :: forall x y. SigBimonoid arr (SigNet t arr) x y -> N.Net t arr x y
    goBimonoid SigCopy = N.Copy
    goBimonoid SigDiscard = N.Discard
    goBimonoid SigPlus = N.Plus
    goBimonoid SigZero = N.Zero
