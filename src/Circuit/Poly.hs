{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Circuit.Poly
  ( Poly (..),
    Eval (..),
    Pos,
    Dir,
    Netlist (..),
    netRoundTrip,
    tensorUnitorL,
    tensorUnitorL',
    tensorUnitorR,
    tensorUnitorR',
    morphAt,
    parT,
    nestedToComp,
    compToNested,
    compUnitorL,
    compUnitorL',
    compUnitorR,
    compUnitorR',
    compAssocL,
    compAssocR,
    tensorEval,
    Morphism (..),
    runMorphism,
    Mono,
    monoIn,
    monoDir,
    Lens,
    lens,
    dagger,
    applyLens,
    prism,
    prismMatch,
  )
where

import Circuit.Category (Category (..))
import Data.Bifunctor
import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

data Poly
  = Y
  | Konst Type
  | Exp Type
  | Sum Poly Poly
  | Prod Poly Poly
  | PTensor Poly Poly
  | Comp Poly Poly

type family Pos (p :: Poly) :: Type where
  Pos 'Y = ()
  Pos ('Konst a) = a
  Pos ('Exp a) = ()
  Pos ('Sum p q) = Either (Pos p) (Pos q)
  Pos ('Prod p q) = (Pos p, Pos q)
  Pos ('PTensor p q) = (Pos p, Pos q)
  Pos ('Comp p q) = (Pos p, Dir p -> Pos q)

type family Dir (p :: Poly) :: Type where
  Dir 'Y = ()
  Dir ('Konst a) = Void
  Dir ('Exp a) = a
  Dir ('Sum p q) = Either (Dir p) (Dir q)
  Dir ('Prod p q) = Either (Dir p) (Dir q)
  Dir ('PTensor p q) = (Dir p, Dir q)
  Dir ('Comp p q) = (Dir p, Dir q)

data Eval (p :: Poly) (x :: Type) where
  EY :: x -> Eval 'Y x
  EK :: c -> Eval ('Konst c) x
  EE :: (a -> x) -> Eval ('Exp a) x
  ES :: Either (Eval p x) (Eval q x) -> Eval ('Sum p q) x
  EP :: (Eval p x, Eval q x) -> Eval ('Prod p q) x
  ET :: (Pos p, Pos q) -> ((Dir p, Dir q) -> x) -> Eval ('PTensor p q) x
  EC ::
    (Pos p, Dir p -> Pos q) ->
    ((Dir p, Dir q) -> x) ->
    Eval ('Comp p q) x

instance Functor (Eval p) where
  fmap f = \case
    EY x -> EY (f x)
    EK c -> EK c
    EE g -> EE (f . g)
    ES e -> ES (bimap (fmap f) (fmap f) e)
    EP (a, b) -> EP (fmap f a, fmap f b)
    ET pos g -> ET pos (f . g)
    EC pos g -> EC pos (f . g)

class Netlist (p :: Poly) where
  toNet :: Eval p x -> (Pos p, Dir p -> x)

  fromNet :: Pos p -> (Dir p -> x) -> Eval p x

instance Netlist 'Y where
  toNet (EY x) = ((), \() -> x)
  fromNet () k = EY (k ())

instance Netlist ('Konst a) where
  toNet (EK c) = (c, absurd)
  fromNet c _ = EK c

instance Netlist ('Exp a) where
  toNet (EE f) = ((), f)
  fromNet () = EE

instance (Netlist p, Netlist q) => Netlist ('Prod p q) where
  toNet (EP (u, v)) =
    let (i, f) = toNet u
        (j, g) = toNet v
     in ((i, j), either f g)
  fromNet (i, j) k = EP (fromNet i (k . Left), fromNet j (k . Right))

instance Netlist ('PTensor p q) where
  toNet (ET ij f) = (ij, f)
  fromNet = ET

instance Netlist ('Comp p q) where
  toNet (EC i k) = (i, k)
  fromNet = EC

netRoundTrip :: (Netlist p) => Eval p x -> Eval p x
netRoundTrip v = uncurry fromNet (toNet v)

tensorUnitorL :: (Netlist p) => Eval ('PTensor 'Y p) x -> Eval p x
tensorUnitorL (ET ((), i) f) = fromNet i (\dp -> f ((), dp))

tensorUnitorL' :: (Netlist p) => Eval p x -> Eval ('PTensor 'Y p) x
tensorUnitorL' v =
  let (i, k) = toNet v
   in ET ((), i) (\((), dp) -> k dp)

tensorUnitorR :: (Netlist p) => Eval ('PTensor p 'Y) x -> Eval p x
tensorUnitorR (ET (i, ()) f) = fromNet i (\dp -> f (dp, ()))

tensorUnitorR' :: (Netlist p) => Eval p x -> Eval ('PTensor p 'Y) x
tensorUnitorR' v =
  let (i, k) = toNet v
   in ET (i, ()) (\(dp, ()) -> k dp)

morphAt :: (Netlist p, Netlist p') => Morphism p p' -> Pos p -> (Pos p', Dir p' -> Dir p)
morphAt m i =
  let (i', k) = toNet (runMorphism m (fromNet i id))
   in (i', k)

parT ::
  (Netlist p, Netlist q, Netlist p', Netlist q') =>
  Morphism p p' ->
  Morphism q q' ->
  Eval ('PTensor p q) x ->
  Eval ('PTensor p' q') x
parT m n (ET (i, j) f) =
  let (i', pullM) = morphAt m i
      (j', pullN) = morphAt n j
   in ET (i', j') (f . bimap pullM pullN)

nestedToComp :: (Netlist p, Netlist q) => Eval p (Eval q x) -> Eval ('Comp p q) x
nestedToComp v =
  let (i, g) = toNet v
   in EC (i, fst . toNet . g) (\(dp, dq) -> snd (toNet (g dp)) dq)

compToNested :: (Netlist p, Netlist q) => Eval ('Comp p q) x -> Eval p (Eval q x)
compToNested (EC (i, hang) k) =
  fromNet i (\dp -> fromNet (hang dp) (\dq -> k (dp, dq)))

compUnitorL :: (Netlist p) => Eval ('Comp 'Y p) x -> Eval p x
compUnitorL (EC ((), hang) k) =
  fromNet (hang ()) (\dp -> k ((), dp))

compUnitorL' :: (Netlist p) => Eval p x -> Eval ('Comp 'Y p) x
compUnitorL' v =
  let (i, k) = toNet v
   in EC ((), const i) (\((), dp) -> k dp)

compUnitorR :: (Netlist p) => Eval ('Comp p 'Y) x -> Eval p x
compUnitorR (EC (i, _) k) =
  fromNet i (\dp -> k (dp, ()))

compUnitorR' :: (Netlist p) => Eval p x -> Eval ('Comp p 'Y) x
compUnitorR' v =
  let (i, k) = toNet v
   in EC (i, const ()) (\(dp, ()) -> k dp)

compAssocL :: Eval ('Comp ('Comp p q) r) x -> Eval ('Comp p ('Comp q r)) x
compAssocL (EC ((i, f), g) k) =
  EC
    ( i,
      \dp ->
        let j = f dp
            h dq = g (dp, dq)
         in (j, h)
    )
    (\(dp, (dq, dr)) -> k ((dp, dq), dr))

compAssocR :: Eval ('Comp p ('Comp q r)) x -> Eval ('Comp ('Comp p q) r) x
compAssocR (EC (i, h) k) =
  let f = fst . h
      g (dp, dq) = snd (h dp) dq
   in EC ((i, f), g) (\((dp, dq), dr) -> k (dp, (dq, dr)))

compT ::
  Morphism (Mono da a) (Mono db b) ->
  Morphism (Mono dc c) (Mono dd d) ->
  Eval ('Comp (Mono da a) (Mono dc c)) x ->
  Eval ('Comp (Mono db b) (Mono dd d)) x
compT f g (EC (aPos, hang) k) =
  let ((bPos, ()), fBw) = morphAt f aPos
      newHang db =
        let da = fBw db
            cPos = hang da
            (dPos, _) = morphAt g cPos
         in dPos
      newK (db, dd) =
        let da = fBw db
            cPos = hang da
            (_, gBw) = morphAt g cPos
            dc = gBw dd
         in k (da, dc)
   in EC ((bPos, ()), newHang) newK

tensorEval :: (Netlist p, Netlist q) => Eval p a -> Eval q b -> Eval (PTensor p q) (a, b)
tensorEval v w =
  let (i, fv) = toNet v
      (j, fw) = toNet w
   in ET (i, j) (bimap fv fw)

data Morphism (p :: Poly) (q :: Poly) where
  Id :: Morphism p p
  Point :: Eval q () -> Morphism 'Y q
  ConstMap :: (a -> b) -> Morphism ('Konst a) ('Konst b)
  ExpMap :: (a -> b) -> Morphism ('Exp b) ('Exp a)
  Compose :: Morphism q r -> Morphism p q -> Morphism p r
  Par :: Morphism p p' -> Morphism q q' -> Morphism ('Prod p q) ('Prod p' q')
  Inl :: Morphism p ('Sum p q)
  Inr :: Morphism q ('Sum p q)
  Case :: Morphism p r -> Morphism q r -> Morphism ('Sum p q) r
  Fst :: Morphism ('Prod p q) p
  Snd :: Morphism ('Prod p q) q
  Pair :: Morphism r p -> Morphism r q -> Morphism r ('Prod p q)
  Global :: b -> Morphism p ('Konst b)
  Depend :: (a -> Morphism p q) -> Morphism ('Prod ('Konst a) p) q
  TensorAssocL :: Morphism ('PTensor ('PTensor p q) r) ('PTensor p ('PTensor q r))
  TensorAssocR :: Morphism ('PTensor p ('PTensor q r)) ('PTensor ('PTensor p q) r)
  TensorBraid :: Morphism ('PTensor p q) ('PTensor q p)
  ParT ::
    Morphism (Mono da a) (Mono db b) ->
    Morphism (Mono dc c) (Mono dd d) ->
    Morphism ('PTensor (Mono da a) (Mono dc c)) ('PTensor (Mono db b) (Mono dd d))
  CompUnitL :: (Netlist p) => Morphism ('Comp 'Y p) p
  CompUnitL' :: (Netlist p) => Morphism p ('Comp 'Y p)
  CompUnitR :: (Netlist p) => Morphism ('Comp p 'Y) p
  CompUnitR' :: (Netlist p) => Morphism p ('Comp p 'Y)
  CompAssocL :: Morphism ('Comp ('Comp p q) r) ('Comp p ('Comp q r))
  CompAssocR :: Morphism ('Comp p ('Comp q r)) ('Comp ('Comp p q) r)
  CompT ::
    Morphism (Mono da a) (Mono db b) ->
    Morphism (Mono dc c) (Mono dd d) ->
    Morphism ('Comp (Mono da a) (Mono dc c)) ('Comp (Mono db b) (Mono dd d))
  Prism ::
    (s -> Either a s) ->
    (a -> s) ->
    Morphism (Mono s s) ('Sum (Mono a a) (Mono s s))

instance Category Morphism where
  id = Id
  (.) = Compose

runMorphism :: Morphism p q -> (forall x. Eval p x -> Eval q x)
runMorphism = \case
  Id -> id
  Point u -> \(EY v) -> fmap (const v) u
  ConstMap f -> \(EK a) -> EK (f a)
  ExpMap f -> \(EE g) -> EE (g . f)
  Compose g f -> runMorphism g . runMorphism f
  Par f g -> \(EP (a, b)) -> EP (runMorphism f a, runMorphism g b)
  Inl -> ES . Left
  Inr -> ES . Right
  Case f g -> \case
    ES (Left a) -> runMorphism f a
    ES (Right b) -> runMorphism g b
  Fst -> \(EP (a, _)) -> a
  Snd -> \(EP (_, b)) -> b
  Pair f g -> \r -> EP (runMorphism f r, runMorphism g r)
  Global b -> \_ -> EK b
  Depend k -> \(EP (EK a, p)) -> runMorphism (k a) p
  TensorAssocL -> \(ET ((pp, pq), pr) f) ->
    ET (pp, (pq, pr)) (f . (\(dp, (dq, dr)) -> ((dp, dq), dr)))
  TensorAssocR -> \(ET (pp, (pq, pr)) f) ->
    ET ((pp, pq), pr) (f . (\((dp, dq), dr) -> (dp, (dq, dr))))
  TensorBraid -> \(ET (pp, pq) f) ->
    ET (pq, pp) (f . (\(dq, dp) -> (dp, dq)))
  ParT m n -> parT m n
  CompUnitL -> compUnitorL
  CompUnitL' -> compUnitorL'
  CompUnitR -> compUnitorR
  CompUnitR' -> compUnitorR'
  CompAssocL -> compAssocL
  CompAssocR -> compAssocR
  CompT m n -> compT m n
  Prism match build -> \case
    EP (EK s, EE k) -> case match s of
      Left a -> ES (Left (EP (EK a, EE (k . build))))
      Right s' -> ES (Right (EP (EK s', EE k)))

type Mono i o = 'Prod ('Konst o) ('Exp i)

monoIn :: i -> Dir (Mono i o)
monoIn = Right

monoDir :: Dir (Mono i o) -> i
monoDir (Right i) = i
monoDir (Left v) = absurd v

type Lens s t a b = Morphism (Mono t s) (Mono b a)

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens f g = Depend (\s -> Pair (Global (f s)) (ExpMap (g s)))

dagger :: (s -> a) -> (b -> t) -> Lens s t a b
dagger f g = Pair (Compose (ConstMap f) Fst) (Compose (ExpMap g) Snd)

applyLens :: Lens s t a b -> s -> (a, b -> t)
applyLens m s = case runMorphism m (EP (EK s, EE id)) of
  EP (EK a, EE g) -> (a, g)

prism ::
  (s -> Either a s) ->
  (a -> s) ->
  Morphism (Mono s s) ('Sum (Mono a a) (Mono s s))
prism = Prism

prismMatch ::
  Morphism (Mono s s) ('Sum (Mono a a) (Mono s s)) ->
  s ->
  Either a s
prismMatch p s = case runMorphism p (EP (EK s, EE id)) of
  ES (Left (EP (EK a, _))) -> Left a
  ES (Right (EP (EK s', _))) -> Right s'
