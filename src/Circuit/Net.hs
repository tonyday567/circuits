{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-partial-fields #-}

module Circuit.Net
  ( Net,
    widen,
    mirrorNet,
    SMC,
    mirrorSMC,
    FreeSMC,
    SigPar (..),
    SigSwap (..),
  )
where

import Circuit.Bimonoid
  ( Dagger (..),
    SigCopy (..),
    SigDiscard (..),
    SigPlus (..),
    SigZero (..),
    transpose,
  )
import Circuit.Bimonoid qualified as Bm
import Circuit.Category (Category (..))
import Circuit.Syntax
  ( Algebra (..),
    Layer (..),
    SigCompose (..),
    Syntax (..),
    eval,
    evalInto,
    (:+:) (..),
    (:~>),
  )
import Circuit.Tensor (Action, SemiTensor, Tensor, Unital)
import Circuit.Tensor qualified as T
import Circuit.Trace (Trace)
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

data SigPar (w :: Type -> Type -> Type) arr rec a b where
  SigPar ::
    rec a b ->
    rec c d ->
    SigPar w arr rec (w a c) (w b d)

instance (Tensor w arr') => Algebra (SigPar w) arr arr' where
  type Ctx (SigPar w) arr arr' = Tensor w arr'
  alg _ rec (SigPar f g) = T.tensor (rec f) (rec g)

data SigSwap (w :: Type -> Type -> Type) arr rec a b where
  SigSwap :: SigSwap w arr rec (w a b) (w b a)

instance (Action w arr') => Algebra (SigSwap w) arr arr' where
  type Ctx (SigSwap w) arr arr' = Action w arr'
  alg _ _ SigSwap = T.braid

type SMC w arr = Syntax (SigCompose :+: SigPar w :+: SigSwap w) arr

widen :: SMC w arr a b -> Net w arr a b
widen (Lift f) = Lift f
widen (Oper op) = case op of
  L (SigCompose g f) -> Oper (L (SigCompose (widen g) (widen f)))
  R (L (SigPar f g)) -> Oper (R (L (SigPar (widen f) (widen g))))
  R (R SigSwap) -> Oper (R (R (L SigSwap)))

mirrorSMC ::
  forall w arr a b.
  SMC w (Dagger arr) a b ->
  SMC w (Dagger arr) b a
mirrorSMC (Lift d) = Lift (transpose d)
mirrorSMC (Oper op) = case op of
  L (SigCompose g f) -> Oper (L (SigCompose (mirrorSMC f) (mirrorSMC g)))
  R (L (SigPar f g)) -> Oper (R (L (SigPar (mirrorSMC f) (mirrorSMC g))))
  R (R SigSwap) -> Oper (R (R SigSwap))

class (Action w arr) => FreeSMC w arr

instance (Action w arr) => FreeSMC w arr

instance (Category arr) => Category (SMC w arr) where
  id = Lift id
  f . g = Oper (L (SigCompose f g))

instance (Unital w arr) => Unital w (SMC w arr) where
  unitl = Lift T.unitl
  unitl' = Lift T.unitl'
  unitr = Lift T.unitr
  unitr' = Lift T.unitr'

instance (SemiTensor w arr) => SemiTensor w (SMC w arr) where
  tensor f g = Oper (R (L (SigPar f g)))

instance (Tensor w arr) => Tensor w (SMC w arr)

instance (Action w arr) => Action w (SMC w arr) where
  braid = Oper (R (R SigSwap))

instance (Category arr, Assoc t arr) => Assoc t (SMC w arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'

instance (Category arr, Slide t arr) => Slide t (SMC w arr) where
  slide = Lift slide

instance (Strength t arr, Action w arr) => Strength t (SMC w arr) where
  strength f = Lift (strength (eval f))

instance (Yank t arr, Action w arr) => Yank t (SMC w arr) where
  yank body = Lift (yank (eval body))

type Net (w :: Type -> Type -> Type) arr =
  Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w) arr

instance (Category arr) => Category (Net w arr) where
  id = Lift id
  f . g = Oper (L (SigCompose f g))

mirrorNet ::
  forall w arr a b.
  (forall x. Bm.BimonoidT w arr x) =>
  Net w (Dagger arr) a b ->
  Net w (Dagger arr) b a
mirrorNet (Lift d) = Lift (transpose d)
mirrorNet (Oper op) = case op of
  L (SigCompose g f) -> Oper (L (SigCompose (mirrorNet f) (mirrorNet g)))
  R (L (SigPar f g)) -> Oper (R (L (SigPar (mirrorNet f) (mirrorNet g))))
  R (R (L SigSwap)) -> Oper (R (R (L SigSwap)))
  R (R (R (L SigCopy))) -> Oper (R (R (R (R (R (L SigPlus))))))
  R (R (R (R (L SigDiscard)))) -> Oper (R (R (R (R (R (R SigZero))))))
  R (R (R (R (R (L SigPlus))))) -> Oper (R (R (R (L SigCopy))))
  R (R (R (R (R (R SigZero))))) -> Oper (R (R (R (R (L SigDiscard)))))

instance Layer (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w)) where
  type Law (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w)) arr' = FreeSMC w arr'
  type Run (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w)) arr = Action w arr
  type Bind (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w)) arr = ()
  unit = Lift
  bind ::
    forall arr' arr a b.
    (Law (Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w)) arr') =>
    (arr :~> arr') ->
    Syntax (SigCompose :+: SigPar w :+: SigSwap w :+: SigCopy w :+: SigDiscard w :+: SigPlus w :+: SigZero w) arr a b ->
    arr' a b
  bind = evalInto
