module Axioma.Container
  ( containerTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Container
import Circuit.Poly (Eval (..), Mono, Morphism (Id), Netlist (..), Poly (..), Pos, prism)
import Control.Category (id, (.))
import Control.Monad (when)
import Data.Maybe (fromJust, isNothing)
import Data.Void (absurd)
import Prelude hiding (id, (.))

hSumPositions :: [Pos (Sum (Mono Int Int) (Mono Bool Bool))]
hSumPositions = [Left (1, ()), Right (True, ())]

posOfSome :: SomePos p -> Pos p
posOfSome (SomePos i) = posOf i

sameSomePos :: (Eq (Pos p)) => SomePos p -> SomePos p -> Bool
sameSomePos (SomePos x) (SomePos y) = skelOf x == skelOf y && posOf x == posOf y

sumRoundTripOk :: Bool
sumRoundTripOk =
  case fromFibred (toFibred v) of
    ES (Left (EP (EK c, EE f))) -> c == (1 :: Int) && f 4 == 12
    _ -> False
  where
    v :: Eval (Sum (Mono Int Int) (Mono Bool Bool)) Int
    v = ES (Left (EP (EK 1, EE (* 3))))

prodRoundTripOk :: Bool
prodRoundTripOk =
  case fromFibred (toFibred v) of
    EP (EK c, EE f) -> c == (3 :: Int) && f 5 == 10
  where
    v :: Eval (Mono Int Int) Int
    v = EP (EK 3, EE (* 2))

ptensorRoundTripOk :: Bool
ptensorRoundTripOk =
  case fromFibred (toFibred v) of
    ET _ g -> g (Right 7, ()) == (7 :: Int)
  where
    v :: Eval (PTensor (Mono Int Int) Y) Int
    v = ET ((5, ()), ()) (\(d, ()) -> either absurd id d)

yRoundTripOk :: Bool
yRoundTripOk =
  case fromFibred (toFibred v) of
    EY x -> x == (5 :: Int)
  where
    v :: Eval Y Int
    v = EY 5

constRoundTripOk :: Bool
constRoundTripOk =
  case fromFibred (toFibred v) of
    EK c -> c == (3 :: Int)
  where
    v :: Eval (Konst Int) Bool
    v = EK 3

expRoundTripOk :: Bool
expRoundTripOk =
  case fromFibred (toFibred v) of
    EE f -> f 5 == (7 :: Int)
  where
    v :: Eval (Exp Int) Int
    v = EE (+ 2)

locatedRoundTripOk :: Bool
locatedRoundTripOk =
  all forward hSumPositions
    && all (sameBack . posAt @(Sum (Mono Int Int) (Mono Bool Bool))) hSumPositions
  where
    forward :: Pos (Sum (Mono Int Int) (Mono Bool Bool)) -> Bool
    forward v = posOfSome (posAt @(Sum (Mono Int Int) (Mono Bool Bool)) v) == v

    sameBack :: SomePos (Sum (Mono Int Int) (Mono Bool Bool)) -> Bool
    sameBack s = sameSomePos s (posAt @(Sum (Mono Int Int) (Mono Bool Bool)) (posOfSome s))

sectionOk :: Bool
sectionOk =
  all (\d -> fromFlat m (toFlat m (Right d)) == Just (Right d)) [1 .. 4 :: Int]
  where
    m :: PosAt (Mono Int Int) (BP BK BE)
    m = PosP (PosK 5) PosE

offFibreOk :: Bool
offFibreOk =
  isNothing (fromFlat i (Right ()))
    && isNothing (fromFlat j (Left 5))
  where
    i :: PosAt (Sum (Konst Int) Y) (BL BK)
    i = PosL (PosK 3)
    j :: PosAt (Sum (Exp Int) (Exp Int)) (BR BE)
    j = PosR PosE

gradeAgreementOk :: Bool
gradeAgreementOk =
  case toFibred v of
    Fibred i k ->
      posOf i == flatPos
        && all (\d -> k (fromJust (fromFlat i (Right d))) == net (Right d)) [0 .. 4 :: Int]
  where
    v :: Eval (Mono Int Int) Int
    v = EP (EK 5, EE (+ 1))
    (flatPos, net) = toNet v

netAgreementOk :: Bool
netAgreementOk =
  nfPos == flatPos
    && all (\d -> nfK (Right d) == net (Right d)) [0 .. 4 :: Int]
  where
    v :: Eval (Mono Int Int) Int
    v = EP (EK 5, EE (+ 1))
    (flatPos, net) = toNet v
    (nfPos, nfK) = netViaFibred v

netAgreementPTensorOk :: Bool
netAgreementPTensorOk =
  nfPos == flatPos
    && all (\(d, ()) -> nfK (d, ()) == net (d, ())) [(Right n, ()) | n <- [0 .. 4 :: Int]]
  where
    v :: Eval (PTensor (Mono Int Int) Y) Int
    v = ET ((5, ()), ()) (\(d, ()) -> either absurd id d)
    (flatPos, net) = toNet v
    (nfPos, nfK) = netViaFibred v

prismMorphAtOk :: Bool
prismMorphAtOk =
  case morphAtC p i of
    Bundle (PosL j'@(PosP (PosK n) PosE)) k ->
      n == 7
        && skelOf j' == SP SK SE
        && posOf j' == (7, ())
        && k (Right 3) == Right (Left 3)
    _ -> False
  where
    p ::
      Morphism
        (Mono (Either Int String) (Either Int String))
        (Sum (Mono Int Int) (Mono (Either Int String) (Either Int String)))
    p = prism (\case Left n -> Left n; Right s -> Right (Right s)) Left
    i :: PosAt (Mono (Either Int String) (Either Int String)) (BP BK BE)
    i = PosP (PosK (Left 7)) PosE

parTCAcceptOk :: Bool
parTCAcceptOk =
  case parTC p Id v of
    Fibred (PosT (PosL (PosP (PosK n) PosE)) PosY) g -> n == 7 && g (Right 5, ()) == 5
    _ -> False
  where
    p ::
      Morphism
        (Mono (Either Int String) (Either Int String))
        (Sum (Mono Int Int) (Mono (Either Int String) (Either Int String)))
    p = prism (\case Left n -> Left n; Right s -> Right (Right s)) Left
    v :: Fibred (PTensor (Mono (Either Int String) (Either Int String)) Y) Int
    v = Fibred (PosT i PosY) (\(d, ()) -> either absurd (either id (const 0)) d)
    i :: PosAt (Mono (Either Int String) (Either Int String)) (BP BK BE)
    i = PosP (PosK (Left 7)) PosE

containerTopic :: Verbosity -> IO [Bool]
containerTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Container oracles"
  sequence
    [ checkV verbosity "round trip at Y" yRoundTripOk,
      checkV verbosity "round trip at Konst" constRoundTripOk,
      checkV verbosity "round trip at Exp" expRoundTripOk,
      checkV verbosity "round trip at Sum (the wall oracle)" sumRoundTripOk,
      checkV verbosity "round trip at Prod" prodRoundTripOk,
      checkV verbosity "round trip at PTensor" ptensorRoundTripOk,
      checkV verbosity "posAt round trips both ways on a heterogeneous sum" locatedRoundTripOk,
      checkV verbosity "fromFlat . toFlat is identity on-fibre" sectionOk,
      checkV verbosity "off-fibre narrowing is Nothing" offFibreOk,
      checkV verbosity "fibred and netlist views agree on the monomial" gradeAgreementOk,
      checkV verbosity "netViaFibred agrees with toNet (Mono)" netAgreementOk,
      checkV verbosity "netViaFibred agrees with toNet (PTensor)" netAgreementPTensorOk,
      checkV verbosity "morphAtC reads a prism at the fibre" prismMorphAtOk,
      checkV verbosity "parTC composes with a prism factor" parTCAcceptOk
    ]
