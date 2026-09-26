{-# LANGUAGE TypeFamilies #-}

module Circuit.Container
  ( Branch (..),
    Skel (..),
    PosAt (..),
    SomePos (..),
    posOf,
    skelOf,
    DirAt,
    toFlat,
    fromFlat,
    FlatFibre (..),
    Fibred (..),
    Located (..),
    Container (..),
    monoFibreFlat,
    Bundle (..),
    morphAtC,
    parTC,
    netViaFibred,
  )
where

import Circuit.Category (id, (.))
import Circuit.Poly (Dir, Eval (..), Mono, Morphism, Poly (..), Pos, runMorphism)
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

data Branch
  = BY
  | BK
  | BE
  | BL Branch
  | BR Branch
  | BP Branch Branch
  | BT Branch Branch

data Skel
  = SY
  | SK
  | SE
  | SL Skel
  | SR Skel
  | SP Skel Skel
  | ST Skel Skel
  deriving (Eq, Show)

data PosAt :: Poly -> Branch -> Type where
  PosY :: PosAt 'Y 'BY
  PosK :: c -> PosAt ('Konst c) 'BK
  PosE :: PosAt ('Exp a) 'BE
  PosL :: PosAt p b -> PosAt (Sum p q) ('BL b)
  PosR :: PosAt q b -> PosAt (Sum p q) ('BR b)
  PosP :: PosAt p b -> PosAt q c -> PosAt (Prod p q) ('BP b c)
  PosT :: PosAt p b -> PosAt q c -> PosAt (PTensor p q) ('BT b c)

posOf :: PosAt p b -> Pos p
posOf = \case
  PosY -> ()
  PosK c -> c
  PosE -> ()
  PosL i -> Left (posOf i)
  PosR j -> Right (posOf j)
  PosP i j -> (posOf i, posOf j)
  PosT i j -> (posOf i, posOf j)

skelOf :: PosAt p b -> Skel
skelOf = \case
  PosY -> SY
  PosK _ -> SK
  PosE -> SE
  PosL i -> SL (skelOf i)
  PosR j -> SR (skelOf j)
  PosP i j -> SP (skelOf i) (skelOf j)
  PosT i j -> ST (skelOf i) (skelOf j)

data SomePos :: Poly -> Type where
  SomePos :: PosAt p b -> SomePos p

type family DirAt (p :: Poly) (b :: Branch) :: Type where
  DirAt 'Y 'BY = ()
  DirAt ('Konst c) 'BK = Void
  DirAt ('Exp a) 'BE = a
  DirAt (Sum p q) ('BL b) = DirAt p b
  DirAt (Sum p q) ('BR b) = DirAt q b
  DirAt (Prod p q) ('BP b c) = Either (DirAt p b) (DirAt q c)
  DirAt (PTensor p q) ('BT b c) = (DirAt p b, DirAt q c)

toFlat :: PosAt p b -> DirAt p b -> Dir p
toFlat = \case
  PosY -> \() -> ()
  PosK _ -> absurd
  PosE -> id
  PosL i -> \d -> Left (toFlat i d)
  PosR j -> \d -> Right (toFlat j d)
  PosP i j -> either (Left . toFlat i) (Right . toFlat j)
  PosT i j -> \(d1, d2) -> (toFlat i d1, toFlat j d2)

fromFlat :: PosAt p b -> Dir p -> Maybe (DirAt p b)
fromFlat = \case
  PosY -> \() -> Just ()
  PosK _ -> absurd
  PosE -> \d -> Just d
  PosL i -> \case
    Left d -> fromFlat i d
    Right _ -> Nothing
  PosR j -> \case
    Left _ -> Nothing
    Right d -> fromFlat j d
  PosP i j -> either (fmap Left . fromFlat i) (fmap Right . fromFlat j)
  PosT i j -> \(d1, d2) -> (,) <$> fromFlat i d1 <*> fromFlat j d2

class FlatFibre (p :: Poly) where
  narrow :: PosAt p b -> Dir p -> DirAt p b

instance FlatFibre 'Y where
  narrow PosY () = ()

instance FlatFibre ('Konst c) where
  narrow _ = absurd

instance FlatFibre ('Exp a) where
  narrow PosE d = d

instance (FlatFibre p, FlatFibre q) => FlatFibre (Prod p q) where
  narrow (PosP i j) = either (Left . narrow i) (Right . narrow j)

instance (FlatFibre p, FlatFibre q) => FlatFibre (PTensor p q) where
  narrow (PosT i j) (d1, d2) = (narrow i d1, narrow j d2)

data Fibred :: Poly -> Type -> Type where
  Fibred :: PosAt p b -> (DirAt p b -> x) -> Fibred p x

class Located (p :: Poly) where
  posAt :: Pos p -> SomePos p

instance Located 'Y where
  posAt () = SomePos PosY

instance Located ('Konst c) where
  posAt = SomePos . PosK

instance Located ('Exp a) where
  posAt () = SomePos PosE

instance (Located p, Located q) => Located (Sum p q) where
  posAt = \case
    Left i -> case posAt i of SomePos pi -> SomePos (PosL pi)
    Right j -> case posAt j of SomePos pj -> SomePos (PosR pj)

instance (Located p, Located q) => Located (Prod p q) where
  posAt (i, j) = case (posAt i, posAt j) of
    (SomePos pi, SomePos pj) -> SomePos (PosP pi pj)

instance (Located p, Located q) => Located (PTensor p q) where
  posAt (i, j) = case (posAt i, posAt j) of
    (SomePos pi, SomePos pj) -> SomePos (PosT pi pj)

class Container (p :: Poly) where
  toFibred :: Eval p x -> Fibred p x
  fromFibred :: Fibred p x -> Eval p x

instance Container 'Y where
  toFibred (EY x) = Fibred PosY (\() -> x)
  fromFibred (Fibred PosY k) = EY (k ())

instance Container ('Konst c) where
  toFibred (EK c) = Fibred (PosK c) absurd
  fromFibred (Fibred (PosK c) _) = EK c

instance Container ('Exp a) where
  toFibred (EE f) = Fibred PosE f
  fromFibred (Fibred PosE k) = EE k

instance (Container p, Container q) => Container (Sum p q) where
  toFibred (ES e) = case e of
    Left u -> case toFibred u of Fibred i k -> Fibred (PosL i) k
    Right v -> case toFibred v of Fibred j k -> Fibred (PosR j) k
  fromFibred (Fibred i k) = case i of
    PosL i' -> ES (Left (fromFibred (Fibred i' k)))
    PosR j' -> ES (Right (fromFibred (Fibred j' k)))

instance (Container p, Container q) => Container (Prod p q) where
  toFibred (EP (u, v)) = case (toFibred u, toFibred v) of
    (Fibred i f, Fibred j g) -> Fibred (PosP i j) (either f g)
  fromFibred (Fibred (PosP i j) k) =
    EP (fromFibred (Fibred i (k . Left)), fromFibred (Fibred j (k . Right)))

instance
  (Located p, Located q, FlatFibre p, FlatFibre q) =>
  Container (PTensor p q)
  where
  toFibred (ET (i, j) f) = case (posAt i, posAt j) of
    (SomePos pi, SomePos pj) -> Fibred (PosT pi pj) (\(dp, dq) -> f (toFlat pi dp, toFlat pj dq))
  fromFibred (Fibred (PosT i j) k) =
    ET (posOf i, posOf j) (\(d1, d2) -> k (narrow i d1, narrow j d2))

netViaFibred :: (Container p, FlatFibre p) => Eval p x -> (Pos p, Dir p -> x)
netViaFibred v = case toFibred v of
  Fibred i k -> (posOf i, k . narrow i)

data Bundle p p' b = forall b'. Bundle (PosAt p' b') (DirAt p' b' -> DirAt p b)

morphAtC ::
  (Container p, Container p') =>
  Morphism p p' ->
  PosAt p b ->
  Bundle p p' b
morphAtC m i = case toFibred (runMorphism m v) of
  Fibred j k -> Bundle j k
  where
    v = fromFibred (Fibred i id)

parTC ::
  (Container p, Container q, Container p', Container q') =>
  Morphism p p' ->
  Morphism q q' ->
  Fibred (PTensor p q) x ->
  Fibred (PTensor p' q') x
parTC m n (Fibred (PosT i j) f) = case (morphAtC m i, morphAtC n j) of
  (Bundle i' pullM, Bundle j' pullN) ->
    Fibred (PosT i' j') (\(d1, d2) -> f (pullM d1, pullN d2))

monoFibreFlat :: DirAt (Mono Int Int) ('BP 'BK 'BE) :~: Dir (Mono Int Int)
monoFibreFlat = Refl
