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

module Circuit.Syntax
  ( Sig,
    (:+:) (..),
    Syntax (..),
    Algebra (..),
    eval,
    evalInto,
    SigCompose (..),
    Cat2,
    (:~>),
    Layer (..),
    Free (..),
  )
where

import Circuit.Category (Category (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Kind (Constraint, Type)
import Prelude hiding (id, (.))

type Sig = (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type

data (sig1 :+: sig2) arr rec a b where
  L :: sig1 arr rec a b -> (sig1 :+: sig2) arr rec a b
  R :: sig2 arr rec a b -> (sig1 :+: sig2) arr rec a b

infixr 6 :+:

data Syntax (sig :: Sig) (arr :: Type -> Type -> Type) a b where
  Lift :: arr a b -> Syntax sig arr a b
  Oper :: sig arr (Syntax sig arr) a b -> Syntax sig arr a b

class Algebra (sig :: Sig) (arr :: Type -> Type -> Type) (arr' :: Type -> Type -> Type) where
  type Ctx sig arr arr' :: Constraint
  type Ctx sig arr arr' = ()
  alg ::
    (Ctx sig arr arr') =>
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    sig arr rec a b ->
    arr' a b

instance (Algebra sig1 arr arr', Algebra sig2 arr arr') => Algebra (sig1 :+: sig2) arr arr' where
  type Ctx (sig1 :+: sig2) arr arr' = (Ctx sig1 arr arr', Ctx sig2 arr arr')
  alg emb rec (L op) = alg emb rec op
  alg emb rec (R op) = alg emb rec op

evalInto ::
  (Category arr', Algebra sig arr arr', Ctx sig arr arr') =>
  (forall x y. arr x y -> arr' x y) ->
  Syntax sig arr a b ->
  arr' a b
evalInto emb (Lift f) = emb f
evalInto emb (Oper op) = alg emb (evalInto emb) op

eval ::
  (Category arr, Algebra sig arr arr, Ctx sig arr arr) =>
  Syntax sig arr a b ->
  arr a b
eval = evalInto id

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

type AlgCat arr = Syntax SigCompose arr

instance (Category arr) => Category (AlgCat arr) where
  id = Lift id
  f . g = Oper (SigCompose f g)

instance (Category arr, Assoc t arr) => Assoc t (AlgCat arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'

instance (Category arr, Slide t arr) => Slide t (AlgCat arr) where
  slide = Lift slide

instance (Category arr, Strength t arr) => Strength t (AlgCat arr) where
  strength f = Lift (strength (eval f))

instance (Category arr, Yank t arr) => Yank t (AlgCat arr) where
  yank body = Lift (yank (eval body))

type Cat2 = Type -> Type -> Type

type arr :~> arr' = forall x y. arr x y -> arr' x y

class Layer (f :: Cat2 -> Cat2) where
  type Law f (arr' :: Cat2) :: Constraint

  type Run f (arr :: Cat2) :: Constraint

  type Run f arr = ()

  type Bind f (arr :: Cat2) :: Constraint

  type Bind f arr = ()

  unit :: (Category arr) => arr :~> f arr

  run ::
    (Run f arr, Law f arr, Bind f arr) =>
    f arr a b ->
    arr a b
  run = bind id

  bind ::
    (Law f arr', Bind f arr) =>
    (arr :~> arr') ->
    f arr a b ->
    arr' a b

data Free arr a b where
  FreeLift :: arr a b -> Free arr a b
  FreeCompose :: Free arr b c -> Free arr a b -> Free arr a c

instance (Category arr) => Category (Free arr) where
  id = FreeLift id
  (.) = FreeCompose

instance Layer Free where
  type Law Free arr' = Category arr'
  type Run Free arr = Category arr
  type Bind Free arr = ()
  unit = FreeLift
  bind :: forall arr' arr a b. (Law Free arr') => (arr :~> arr') -> Free arr a b -> arr' a b
  bind h (FreeLift f) = h f
  bind h (FreeCompose @_ @_ g f) = bind h g . bind h f

instance (Assoc t arr) => Assoc t (Free arr) where
  assoc = FreeLift assoc
  assoc' = FreeLift assoc'

instance (Slide t arr) => Slide t (Free arr) where
  slide = FreeLift slide

instance (Strength t arr) => Strength t (Free arr) where
  strength = FreeLift . strength . run

instance (Yank t arr) => Yank t (Free arr) where
  yank = FreeLift . yank . run
