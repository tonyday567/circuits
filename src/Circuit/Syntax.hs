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

-- | The generic substrate for modular circuit syntax.
--
-- This module holds the à-la-carte machinery: signatures, the free
-- construction over a signature, algebras, and the universal folds. Each
-- concrete language layer ('Circuit.Trace.Trace', 'Circuit.SMC.SMC',
-- 'Circuit.Net.Net', ...) is obtained by choosing a signature sum and adding
-- smart constructors and structural instances on top of this substrate.
--
-- The design is a profunctor-shaped variation of the classic "datatypes à la
-- carte":
--
-- * A 'Sig' is a signature functor indexed by a base arrow @arr@ and a
--   recursive arrow @rec@.
-- * @'Syntax' sig arr@ is the free construction over @sig@ with generators
--   drawn from @arr@.
-- * An 'Algebra' interprets the operations of a signature into a target arrow.
-- * 'evalInto' is the universal fold out of the free construction; 'eval' is
--   the same fold back into the base arrow.
module Circuit.Syntax
  ( -- * Signatures
    Sig,
    (:+:) (..),

    -- * Syntax and algebra
    Syntax (..),
    Algebra (..),
    eval,
    evalInto,

    -- * Sequential composition
    SigCompose (..),

    -- * Free category
    AlgCat,
  )
where

import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Data.Kind (Constraint, Type)
import Prelude hiding (id, (.))

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

-- Free construction over a signature

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

-- Sequential composition

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

-- Common syntax combinations

-- | Free category.
type AlgCat arr = Syntax SigCompose arr

-- Instances for the free category

instance (Category arr) => Category (AlgCat arr) where
  id = Lift id
  f . g = Op (SigCompose f g)

instance (Category arr, Channel t arr) => Channel t (AlgCat arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'
  slide = Lift slide

instance (Category arr, Strength t arr) => Strength t (AlgCat arr) where
  strength f = Lift (strength (eval f))

instance (Category arr, Traced t arr) => Traced t (AlgCat arr) where
  trace body = Lift (trace (eval body))
