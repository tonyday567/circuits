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

module Circuit.Trace
  ( Trace,
    SigYank (..),
    Knot (..),
    Wire,
    Step,
  )
where

import Circuit.Category (Category (..), (.>))
import Circuit.Syntax (Algebra (..), Layer (..), SigCompose (..), Syntax (..), (:+:) (..), (:~>))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

data SigYank (t :: Type -> Type -> Type) arr rec a b where
  YankBody ::
    rec (t s a) (t s b) ->
    SigYank t arr rec a b

instance (Yank t arr') => Algebra (SigYank t) arr arr' where
  type Ctx (SigYank t) arr arr' = Yank t arr'
  alg ::
    forall (rec :: Type -> Type -> Type) (b :: Type) (c :: Type).
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    SigYank t arr rec b c ->
    arr' b c
  alg _ rec (YankBody @_ @_ @_ @_ @_ @_ f) = yank (rec f)

type Trace t arr = Syntax (SigCompose :+: SigYank t) arr

instance (Category arr) => Category (Trace t arr) where
  id = Lift id
  f . g = Oper (L (SigCompose f g))

instance (Category arr, Assoc t arr) => Assoc t (Trace t arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'

instance (Category arr, Slide t arr) => Slide t (Trace t arr) where
  slide = Lift slide

instance (Category arr, Slide t arr, Strength t arr) => Strength t (Trace t arr) where
  strength (Lift f) = Lift (strength f)
  strength (Oper (L (SigCompose g f))) = strength g . strength f
  strength (Oper (R (YankBody body))) = yank (Lift slide .> strength body .> Lift slide)

instance (Category arr, Slide t arr, Strength t arr) => Yank t (Syntax (SigCompose :+: SigYank t) arr) where
  yank body = Oper (R (YankBody body))

data Knot (t :: Type -> Type -> Type) arr a b where
  Arr :: arr a b -> Knot t arr a b
  Knot :: arr (t s a) (t s b) -> Knot t arr a b

type Wire = Knot (,) (->)

type Step = Knot Either (->)

instance (Strength t arr) => Category (Knot t arr) where
  id = Arr id
  Arr f . Arr g = Arr (f . g)
  Knot f . Arr g = Knot (strength g .> f)
  Arr f . Knot g = Knot (g .> strength f)
  Knot f . Knot g = Knot (assoc .> strength g .> slide .> strength f .> slide .> assoc')

instance (Strength t arr) => Assoc t (Knot t arr) where
  assoc = Arr assoc
  assoc' = Arr assoc'

instance (Strength t arr) => Slide t (Knot t arr) where
  slide = Arr slide

instance (Strength t arr) => Strength t (Knot t arr) where
  strength (Arr f) = Arr (strength f)
  strength (Knot f) = Knot (slide .> strength f .> slide)

instance (Yank t arr) => Yank t (Knot t arr) where
  yank (Arr f) = Knot f
  yank (Knot f) = Knot (assoc .> f .> assoc')

instance (Bifunctor t) => Functor (Knot t (->) a) where
  fmap f (Arr g) = Arr (g .> f)
  fmap f (Knot g) = Knot (g .> second f)

instance Layer (Knot t) where
  type Law (Knot t) arr' = Yank t arr'

  type Run (Knot t) arr = Yank t arr

  type Bind (Knot t) arr = ()

  unit = Arr

  bind ::
    (Law (Knot t) arr') =>
    (arr :~> arr') ->
    Knot t arr a b ->
    arr' a b
  bind h (Arr f) = h f
  bind h (Knot f) = yank (h f)
