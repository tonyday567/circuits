-- | Container oracles — the fibred view of polynomials, checked against
-- the flat grade.
--
-- Mutation notes (per buff/verify.md):
--
-- * The wrong-branch mutant of 'toFibred' for 'Sum' — mapping 'PosL' to
--   the @q@ pins — is a /compile-time/ mutation: it does not typecheck,
--   so a green suite will never show it.  The 'DirAt' equations are the
--   witness; the module haddock records the claim.
-- * A 'posAt' mutant that always takes 'Left' is caught by
--   'locatedRoundTripOk': 'hSumPositions' is heterogeneous
--   (@Sum (Mono Int Int) (Mono Bool Bool)@), so the mutant cannot
--   accidentally agree on the right branch.
module Axioma.Container
  ( containerTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Container
import Circuit.Poly (Eval (..), Mono, Netlist (..), Poly (..), Pos)
import Control.Category ((.), id)
import Control.Monad (when)
import Data.Maybe (fromJust, isNothing)
import Data.Void (absurd)
import Prelude hiding (id, (.))

-- | Positions of a heterogeneous sum — the shape that keeps the
-- 'posAt' oracle honest: left and right branches differ in both
-- skeleton and payload.
hSumPositions :: [Pos (Sum (Mono Int Int) (Mono Bool Bool))]
hSumPositions = [Left (1, ()), Right (True, ())]

posOfSome :: SomePos p -> Pos p
posOfSome (SomePos i) = posOf i

sameSomePos :: (Eq (Pos p)) => SomePos p -> SomePos p -> Bool
sameSomePos (SomePos x) (SomePos y) = skelOf x == skelOf y && posOf x == posOf y

-- | Round trip at every structural constructor of the polynomial
-- grammar, including 'Sum' — the oracle 'netRoundTrip' cannot express.
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
    _ -> False
  where
    v :: Eval (Mono Int Int) Int
    v = EP (EK 3, EE (* 2))

ptensorRoundTripOk :: Bool
ptensorRoundTripOk =
  case fromFibred (toFibred v) of
    ET _ g -> g (Right 7, ()) == (7 :: Int)
    _ -> False
  where
    v :: Eval (PTensor (Mono Int Int) Y) Int
    v = ET ((5, ()), ()) (\(d, ()) -> either absurd id d)

yRoundTripOk :: Bool
yRoundTripOk =
  case fromFibred (toFibred v) of
    EY x -> x == (5 :: Int)
    _ -> False
  where
    v :: Eval Y Int
    v = EY 5

constRoundTripOk :: Bool
constRoundTripOk =
  case fromFibred (toFibred v) of
    EK c -> c == (3 :: Int)
    _ -> False
  where
    v :: Eval (Const Int) Bool
    v = EK 3

expRoundTripOk :: Bool
expRoundTripOk =
  case fromFibred (toFibred v) of
    EE f -> f 5 == (7 :: Int)
    _ -> False
  where
    v :: Eval (Exp Int) Int
    v = EE (+ 2)

-- | The position recovers in both directions: skeleton-and-payload
-- round-trips the flat position, and back.
locatedRoundTripOk :: Bool
locatedRoundTripOk =
  all forward hSumPositions
    && all (sameBack . posAt @(Sum (Mono Int Int) (Mono Bool Bool))) hSumPositions
  where
    forward :: Pos (Sum (Mono Int Int) (Mono Bool Bool)) -> Bool
    forward v = posOfSome (posAt @(Sum (Mono Int Int) (Mono Bool Bool)) v) == v

    sameBack :: SomePos (Sum (Mono Int Int) (Mono Bool Bool)) -> Bool
    sameBack s = sameSomePos s (posAt @(Sum (Mono Int Int) (Mono Bool Bool)) (posOfSome s))

-- | Section law for the bridge maps: narrowing after widening is the
-- identity, on-fibre.
sectionOk :: Bool
sectionOk =
  all (\d -> fromFlat m (toFlat m (Right d)) == Just (Right d)) [1 .. 4 :: Int]
  where
    m :: PosAt (Mono Int Int) (BP BK BE)
    m = PosP (PosK 5) PosE

-- | The wall, restated positively: a flat direction on the wrong
-- branch narrows to nothing.
offFibreOk :: Bool
offFibreOk =
  isNothing (fromFlat i (Right ()))
    && isNothing (fromFlat j (Left 5))
  where
    i :: PosAt (Sum (Const Int) Y) (BL BK)
    i = PosL (PosK 3)
    j :: PosAt (Sum (Exp Int) (Exp Int)) (BR BE)
    j = PosR PosE

-- | Grade agreement with the flat netlist view on the monomial
-- fragment: same position, and the pin maps agree on-fibre.
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

containerTopic :: Verbosity -> IO [Bool]
containerTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Container oracles"
  sequence
    [ checkV verbosity "round trip at Y" yRoundTripOk,
      checkV verbosity "round trip at Const" constRoundTripOk,
      checkV verbosity "round trip at Exp" expRoundTripOk,
      checkV verbosity "round trip at Sum (the wall oracle)" sumRoundTripOk,
      checkV verbosity "round trip at Prod" prodRoundTripOk,
      checkV verbosity "round trip at PTensor" ptensorRoundTripOk,
      checkV verbosity "posAt round trips both ways on a heterogeneous sum" locatedRoundTripOk,
      checkV verbosity "fromFlat . toFlat is identity on-fibre" sectionOk,
      checkV verbosity "off-fibre narrowing is Nothing" offFibreOk,
      checkV verbosity "fibred and netlist views agree on the monomial" gradeAgreementOk
    ]
