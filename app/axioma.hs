{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Circuit.Category (id, (.), (.>))
import Circuit.Channel (assoc, assoc', strength, trace)
import Circuit.Dagger (CopyDiscard (..), MergeZero (..))
import Circuit.Ends (Ends (..), box, ends, splay)
import Circuit.FinRel
import Circuit.Layer (run)
import Circuit.Poly (Mono, System (..), monoDir, monoIn)
import Circuit.Prob (Prob (..), choiceBy, copyP, discardP, embed, fromWeighted, mass, orP, parFG, parGF, score, traceE, traceEN)
import Circuit.Process (Process (..), delay, encode, fold, register, scan)
import Circuit.Tensor (Action (..), Tensor (..))
import Data.List (foldl', scanl')
import Data.Maybe (isNothing)
import Data.Proxy (Proxy (..))
import Data.Tuple qualified as Tuple
import GHC.TypeNats (KnownNat, natVal)
import Test.QuickCheck
  ( Arbitrary (..),
    Gen,
    Property,
    Testable,
    chatty,
    chooseInt,
    isSuccess,
    quickCheckWithResult,
    stdArgs,
    vectorOf,
    (===),
  )
import Prelude hiding (id, (.))

type F = Bool

type N1 = FinObj 1

type N2 = FinObj 2

-- | Swap the second and third @n@-wire blocks of @((a,b),(c,d))@.
swapBlocks ::
  forall n.
  (KnownNat n) =>
  FinRel F ((FinObj n, FinObj n), (FinObj n, FinObj n)) ((FinObj n, FinObj n), (FinObj n, FinObj n))
swapBlocks = wiring perm
  where
    n = fromIntegral (natVal (Proxy @n))
    perm i
      | i < n = i
      | i < 2 * n = i + n
      | i < 3 * n = i - n
      | otherwise = i

swapMiddle :: FinRel F ((N1, N1), (N1, N1)) ((N1, N1), (N1, N1))
swapMiddle = swapBlocks @1

swapMiddle2 :: FinRel F ((N2, N2), (N2, N2)) ((N2, N2), (N2, N2))
swapMiddle2 = swapBlocks @2

-- | Simple additive process for oracles.
sumP :: Process Int Int
sumP = Process id (+) id

-- | Pair swap for the (,) trace yanking oracle.
swapPairP :: Process (Int, Int) (Int, Int)
swapPairP = Process id (\_ x -> x) (\(a, b) -> (b, a))

-- | Either swap for the Either trace yanking oracle.
swapEitherP :: Process (Either Int Int) (Either Int Int)
swapEitherP = Process id (\_ x -> x) swapEither
  where
    swapEither (Left a) = Right a
    swapEither (Right b) = Left b

-- | EWMA body: stateless affine box with feedback.
ewmaBody :: Double -> Process (Double, Double) (Double, Double)
ewmaBody alpha =
  Process
    (\(x, prev) -> alpha * x + (1 - alpha) * prev)
    (\s (x, _) -> alpha * x + (1 - alpha) * s)
    (\s -> (s, s))

-- | Exponentially weighted moving average with initial feedback.
ewma :: Double -> Double -> Process Double Double
ewma alpha s0 = register s0 (ewmaBody alpha)

-- ---------------------------------------------------------------------------
-- Prob helpers for fragment oracles
-- ---------------------------------------------------------------------------

-- | Fair coin with total mass 1.
coin :: Prob (->) Double () Bool
coin = fromWeighted [(True, 0.25), (False, 0.75)]

-- | Unnormalised weighted measure with total mass 1.5.
unnorm :: Prob (->) Double () Bool
unnorm = fromWeighted [(True, 0.5), (False, 1.0)]

-- | A deliberately non-linear inhabitant: squares its continuation.
squareK :: Prob (->) Double a a
squareK = Prob $ \k p -> k p * k p

-- | Evaluate a measure-free morphism against a continuation on the output.
ev :: Prob (->) Double () b -> ((b -> Double) -> Double)
ev (Prob f) k = f (\((), b) -> k b) ((), ())

-- | Approximate equality for floating-point oracles.
approx :: Double -> Double -> Bool
approx x y = abs (x - y) < 1e-9

-- | Geometric trial body: state counts flips; heads escapes with the count.
geomBody :: Double -> Prob (->) Double (Either () Int) (Either Int Int)
geomBody p = Prob $ \k (x, e) ->
  let n = case e of Left () -> 0; Right m -> m
   in p * k (x, Left (n + 1)) + (1 - p) * k (x, Right (n + 1))

-- | A three-state walk on 'Int': from s, either exit with s (Left) or move to
-- s+1 (Right). Used for the Bool trace reachability oracle.
walkBody :: Prob (->) Bool (Either Int Int) (Either Int Int)
walkBody = orP (embed exit) (embed stepR)
  where
    exit e = Left (either id id e)
    stepR e = Right (either id id e + 1)

-- | Reachability test via the Bool least-fixpoint trace.
reach :: Int -> Bool
reach target = runProb (traceE walkBody) (\((), s) -> s == target) ((), 0)

-- | Annotated helpers to avoid ambiguous overloads.
id1 :: FinRel F N1 N1
id1 = id

id2 :: FinRel F N2 N2
id2 = id

copy1 :: FinRel F N1 (N1, N1)
copy1 = copy

copy2 :: FinRel F N2 (N2, N2)
copy2 = copy

discard1 :: FinRel F N1 ()
discard1 = discard

discard2 :: FinRel F N2 ()
discard2 = discard

plus1 :: FinRel F (N1, N1) N1
plus1 = plus

plus2 :: FinRel F (N2, N2) N2
plus2 = plus

zero1 :: FinRel F () N1
zero1 = zero

zero2 :: FinRel F () N2
zero2 = zero

unitl1' :: FinRel F N1 ((), N1)
unitl1' = unitl'

unitr1' :: FinRel F N1 (N1, ())
unitr1' = unitr'

unitl2' :: FinRel F N2 ((), N2)
unitl2' = unitl'

unitr2' :: FinRel F N2 (N2, ())
unitr2' = unitr'

unitr0 :: FinRel F ((), ()) ()
unitr0 = unitr

discard0 :: FinRel F () ()
discard0 = discard

zero0 :: FinRel F () ()
zero0 = zero

-- ---------------------------------------------------------------------------
-- QuickCheck oracles for Process / Loop equivalence
-- ---------------------------------------------------------------------------

-- | A small finite type so processes can be generated as lookup tables.
newtype Small = Small Int
  deriving (Eq, Ord, Show)

instance Arbitrary Small where
  arbitrary = Small <$> chooseInt (0, 2)
  shrink (Small n) = [Small m | m <- [0 .. n - 1]]

smallIndex :: Small -> Int
smallIndex (Small n) = n

-- | Lookup-table function @Small -> Small@.
smallFun1 :: Gen (Small -> Small)
smallFun1 = do
  table <- vectorOf 3 arbitrary
  pure (\(Small i) -> table !! i)

-- | Lookup-table function @Small -> Small -> Small@.
smallFun2 :: Gen (Small -> Small -> Small)
smallFun2 = do
  table <- vectorOf 3 (vectorOf 3 arbitrary)
  pure (\(Small i) (Small j) -> table !! i !! j)

-- | Lookup-table function @(Small, Small) -> Small@.
smallPairFun1 :: Gen ((Small, Small) -> Small)
smallPairFun1 = do
  table <- vectorOf 9 arbitrary
  pure (\(Small i, Small j) -> table !! (i * 3 + j))

-- | Lookup-table function @Small -> (Small, Small)@.
smallFunToPair :: Gen (Small -> (Small, Small))
smallFunToPair = do
  table <- vectorOf 3 arbitrary
  pure (\(Small i) -> table !! i)

-- | Arbitrary process with a three-element state space.
genProcess :: Gen (Process Small Small)
genProcess = do
  inject <- smallFun1
  step <- smallFun2
  Process inject step <$> smallFun1

-- | Arbitrary process with pair-typed input/output and a three-element state
-- space.  Used to test cross-tick feedback.
genProcessPair :: Gen (Process (Small, Small) (Small, Small))
genProcessPair = do
  inject <- smallPairFun1
  step <- do
    table <- vectorOf 3 (vectorOf 9 arbitrary)
    pure (\s p -> table !! smallIndex s !! pairIndex p)
  Process inject step <$> smallFunToPair
  where
    pairIndex (Small i, Small j) = i * 3 + j

instance Arbitrary (Process Small Small) where
  arbitrary = genProcess
  shrink = const []

instance Show (Process Small Small) where
  show _ = "Process Small Small"

instance Arbitrary (Process (Small, Small) (Small, Small)) where
  arbitrary = genProcessPair
  shrink = const []

instance Show (Process (Small, Small) (Small, Small)) where
  show _ = "Process (Small, Small) (Small, Small)"

-- | Process ~ Loop: running the encoding equals scanning the process.
prop_scan_encode :: Process Small Small -> [Small] -> Property
prop_scan_encode p xs = scan p xs === run (encode p) xs

-- | Cross-tick register agrees with explicit one-tick-delayed feedback.
prop_register_trace :: Process (Small, Small) (Small, Small) -> Small -> [Small] -> Property
prop_register_trace body s0 xs =
  scan (register s0 body) xs === manualRegister s0 body xs
  where
    manualRegister _ _ [] = []
    manualRegister s (Process i st ex) (a : as) =
      let s0' = i (a, s)
          states = scanl' (\s' a' -> st s' (a', snd (ex s'))) s0' as
       in map (fst . ex) states

qcCheck :: (Testable prop) => String -> prop -> IO Bool
qcCheck name p = do
  putStrLn ("  " ++ name)
  result <- quickCheckWithResult (stdArgs {chatty = False}) p
  if isSuccess result
    then pure True
    else do
      putStrLn ("    FAIL: " ++ show result)
      pure False

check :: String -> Bool -> IO Bool
check name ok = do
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok

-- ---------------------------------------------------------------------------
-- Keystone: System (Prob (->) r) s (Mono i o)
--
-- The stochastic Moore machine, stepped by expectation. The scalar @r@ selects
-- the semantics: @Double@ for probability, @Tropical@ for min-plus / Viterbi.
-- ---------------------------------------------------------------------------

-- | A tiny semiring class local to the executable so the same runner works for
-- probability and tropical semantics without pulling in NumHask prelude.
class Semiring r where
  sAdd :: r -> r -> r
  sMul :: r -> r -> r
  sZero :: r
  sOne :: r

instance Semiring Double where
  sAdd = (+)
  sMul = (*)
  sZero = 0
  sOne = 1

-- | Min-plus tropical semiring over 'Double'.
--
-- Addition is 'min', multiplication is ordinary addition, the additive unit is
-- positive infinity, and the multiplicative unit is zero.
newtype Tropical = Tropical {getTropical :: Double}
  deriving (Eq, Ord, Show)

instance Semiring Tropical where
  sAdd (Tropical a) (Tropical b) = Tropical (min a b)
  sMul (Tropical a) (Tropical b) = Tropical (a + b)
  sZero = Tropical (1 / 0)
  sOne = Tropical 0

-- | Run a finite-state stochastic Moore machine by expectation.
--
-- Given an enumeration of the state space, the machine, a list of inputs, a
-- query on the final state, and an initial state, return the expected query
-- value.
--
-- For @r = Double@ this is ordinary expectation over the final state
-- distribution. For @r = Tropical@ it is the min-plus cost of the cheapest
-- final state.
expectSystem ::
  (Eq s, Semiring r) =>
  [s] ->
  System (Prob (->) r) s (Mono i o) ->
  [i] ->
  (s -> r) ->
  s ->
  r
expectSystem states (System sys) is q s0 =
  foldl' sAdd sZero [q s `sMul` distFinal s | s <- states]
  where
    distFinal = foldl' step initDist is
    initDist s = if s == s0 then sOne else sZero
    step dist i s' =
      foldl' sAdd sZero [dist s `sMul` pTrans s i s' | s <- states]
    pTrans s i s' =
      runProb
        sys
        (\((), (s'', _)) -> if s' == s'' then sOne else sZero)
        ((), (s, monoIn i))

-- | Three-state chain for the keystone doctests.
data S3 = S0 | S1 | S2
  deriving (Eq, Show, Enum, Bounded)

-- | Probability semantics: a lazy random walk on three states.
--
-- From each state, stay with probability 0.5 and move to the next state
-- (cyclically) with probability 0.5.
chain3Prob :: System (Prob (->) Double) S3 (Mono () ())
chain3Prob = System $ Prob $ \k (x, (s, d)) ->
  let next = case s of
        S0 -> [(S0, 0.5), (S1, 0.5)]
        S1 -> [(S1, 0.5), (S2, 0.5)]
        S2 -> [(S2, 0.5), (S0, 0.5)]
   in foldl' (+) 0 [p * k (x, (s', ((), ()))) | (s', p) <- next]

-- | Tropical semantics: the same graph with transition costs.
--
-- Staying costs 1, moving costs 2. The cheapest n-step path to a state is the
-- Viterbi value.
chain3Tropical :: System (Prob (->) Tropical) S3 (Mono () ())
chain3Tropical = System $ Prob $ \k (x, (s, d)) ->
  let next = case s of
        S0 -> [(S0, Tropical 1), (S1, Tropical 2)]
        S1 -> [(S1, Tropical 1), (S2, Tropical 2)]
        S2 -> [(S2, Tropical 1), (S0, Tropical 2)]
   in foldl' sAdd sZero [c `sMul` k (x, (s', ((), ()))) | (s', c) <- next]

-- | Exact occupancy probabilities for the 3-state chain after @n@ steps,
-- starting from @S0@.
--
-- >>> occupancyProb 0
-- [1.0,0.0,0.0]
--
-- >>> occupancyProb 1
-- [0.5,0.5,0.0]
--
-- >>> occupancyProb 2
-- [0.25,0.5,0.25]
--
-- >>> occupancyProb 3
-- [0.25,0.375,0.375]
occupancyProb :: Int -> [Double]
occupancyProb n =
  [getMass s | s <- [S0, S1, S2]]
  where
    getMass s = expectSystem [S0, S1, S2] chain3Prob (replicate n ()) (\s' -> if s' == s then 1 else 0) S0

-- | Tropical (Viterbi) cost to be in each state after @n@ steps, starting from
-- @S0@.
--
-- >>> viterbiCost 0
-- [0.0,Infinity,Infinity]
--
-- >>> viterbiCost 1
-- [1.0,2.0,Infinity]
--
-- >>> viterbiCost 2
-- [2.0,3.0,4.0]
viterbiCost :: Int -> [Double]
viterbiCost n =
  [getTropical (expectSystem [S0, S1, S2] chain3Tropical (replicate n ()) (\s' -> if s' == s then sOne else sZero) S0) | s <- [S0, S1, S2]]

main :: IO ()
main = do
  results <-
    sequence
      [ -- copy/discard comonoid laws
        check "copy coassociative (n=1)" $
          par copy1 id1 . copy1 == assoc' . par id1 copy1 . copy1,
        check "copy coassociative (n=2)" $
          par copy2 id2 . copy2 == assoc' . par id2 copy2 . copy2,
        check "copy left counit (n=1)" $
          par discard1 id1 . copy1 == unitl1',
        check "copy left counit (n=2)" $
          par discard2 id2 . copy2 == unitl2',
        check "copy right counit (n=1)" $
          par id1 discard1 . copy1 == unitr1',
        check "copy right counit (n=2)" $
          par id2 discard2 . copy2 == unitr2',
        check "copy cocommutative (n=1)" $
          swap . copy1 == copy1,
        check "copy cocommutative (n=2)" $
          swap . copy2 == copy2,
        -- plus/zero monoid laws
        check "plus associative (n=1)" $
          plus1 . par plus1 id1 == plus1 . par id1 plus1 . assoc,
        check "plus associative (n=2)" $
          plus2 . par plus2 id2 == plus2 . par id2 plus2 . assoc,
        check "plus left unit (n=1)" $
          plus1 . par zero1 id1 . unitl1' == id1,
        check "plus left unit (n=2)" $
          plus2 . par zero2 id2 . unitl2' == id2,
        check "plus right unit (n=1)" $
          plus1 . par id1 zero1 . unitr1' == id1,
        check "plus right unit (n=2)" $
          plus2 . par id2 zero2 . unitr2' == id2,
        check "plus commutative (n=1)" $
          plus1 . swap == plus1,
        check "plus commutative (n=2)" $
          plus2 . swap == plus2,
        -- bialgebra laws
        check "bialgebra copy-plus (n=1)" $
          copy1 . plus1 == par plus1 plus1 . swapMiddle . par copy1 copy1,
        check "bialgebra copy-plus (n=2)" $
          copy2 . plus2 == par plus2 plus2 . swapMiddle2 . par copy2 copy2,
        check "bialgebra discard-plus (n=1)" $
          discard1 . plus1 == unitr0 . par discard1 discard1,
        check "bialgebra discard-plus (n=2)" $
          discard2 . plus2 == unitr0 . par discard2 discard2,
        check "bialgebra zero-copy (n=1)" $
          copy1 . zero1 == par zero1 zero1 . unitr',
        check "bialgebra zero-copy (n=2)" $
          copy2 . zero2 == par zero2 zero2 . unitr',
        check "bialgebra discard-zero" $
          discard0 . zero0 == (id :: FinRel F () ()),
        -- scalar arithmetic over GF(2)
        check "scalar True is identity" $
          finScalar True == id1,
        check "scalar False is idempotent" $
          (finScalar False :: FinRel F N1 N1) . finScalar False == finScalar False,
        check "scalar False absorbs scalar True" $
          (finScalar False :: FinRel F N1 N1) . finScalar True == finScalar False,
        check "scalar True after scalar False" $
          (finScalar True :: FinRel F N1 N1) . finScalar False == finScalar False,
        -- traced structure
        check "trace yanking (n=1)" $
          trace (swap :: FinRel F (N1, N1) (N1, N1)) == id1,
        check "trace of identity pair" $
          trace (par id1 id1 :: FinRel F (N1, N1) (N1, N1)) == id1,
        -- Para laws: the constant-state slice of Loop(,)
        check "L1: snd . <fst, f> == f" $
          let f :: Int -> String
              f = show
              h (p, a) = (p, f a)
           in trace h 42 == "42",
        check "L2: threading a constant state == exposing it" $
          let f :: Int -> Int
              f = (+ 10)
              h (p, a) = (p, f a)
           in trace h 5 == 15,
        -- Circuit.Process oracles
        check "Process seed emits first output" $
          scan sumP [5] == [5],
        check "Process scan semantics" $
          scan sumP [1, 2, 3] == [1, 3, 6],
        check "Process fold semantics" $
          fold sumP [1, 2, 3] == Just 6,
        check "Process fold empty" $
          isNothing (fold sumP []),
        check "Process scan == run . encode" $
          run (encode sumP) [1, 2, 3] == scan sumP [1, 2, 3],
        check "Process Traced (,) yanking" $
          scan (trace swapPairP) [1, 2, 3] == [1, 2, 3],
        check "Process Traced Either yanking" $
          scan (trace swapEitherP) [1, 2, 3] == [1, 2, 3],
        check "Process register (EWMA)" $
          scan (ewma 0.5 0.0) [1.0, 1.0, 1.0] == [0.5, 0.75, 0.875],
        check "Process register == trace . strength . delay (EWMA)" $
          let body = ewmaBody 0.5
              s0 = 0.0
              xs = [1.0, 1.0, 1.0]
              swapP (Process i st ex) =
                Process (i . Tuple.swap) (\s -> st s . Tuple.swap) (Tuple.swap . ex)
           in scan (register s0 body) xs
                == scan (trace (swapP (body . strength (delay s0)))) xs,
        -- QuickCheck Process / Loop equivalence
        qcCheck "QC: scan == run . encode" prop_scan_encode,
        qcCheck "QC: register agrees with delayed feedback" prop_register_trace,
        -- Circuit.Prob oracles
        -- Deterministic fragment
        check "Prob embed preserves identity" $
          let k ((), b) = fromIntegral b :: Double
           in runProb (embed id) k ((), 5 :: Int) == k ((), 5 :: Int),
        check "Prob embed preserves composition" $
          let f = (+ 10) :: Int -> Int
              g = (* 3) :: Int -> Int
              k ((), c) = fromIntegral c :: Double
           in runProb (embed (f . g)) k ((), 5)
                == runProb (embed f . embed g) k ((), 5),
        -- Score modality structure
        check "Prob score anti-homomorphism" $
          let w = (* 2.0) :: Double -> Double
              v = (+ 3.0) :: Double -> Double
              k ((), _) = 1.0 :: Double
           in runProb (score w . score v) k ((), 5 :: Int)
                == runProb (score (v . w)) k ((), 5 :: Int),
        check "Prob score endos need not commute" $
          let w = (* 2.0) :: Double -> Double
              v = (+ 3.0) :: Double -> Double
              k ((), _) = 1.0 :: Double
           in runProb (score w . score v) k ((), 5 :: Int)
                /= runProb (score v . score w) k ((), 5 :: Int),
        -- Linear fragment: multiplicative endos central against real measures
        check "Prob centrality of (*2) vs coin (linear fragment)" $
          approx
            (ev (score (* 2) . coin) (\b -> if b then 10 else 1))
            (ev (coin . score (* 2)) (\b -> if b then 10 else 1)),
        -- Affine/Markov fragment: affine endos central exactly on mass-1
        check "Prob centrality of (+3) vs coin (mass 1, affine fragment)" $
          approx
            (ev (score (+ 3) . coin) (\b -> if b then 10 else 1))
            (ev (coin . score (+ 3)) (\b -> if b then 10 else 1)),
        check "Prob centrality of (+3) fails off mass-1 fragment" $
          not
            ( approx
                (ev (score (+ 3) . unnorm) (\b -> if b then 10 else 1))
                (ev (unnorm . score (+ 3)) (\b -> if b then 10 else 1))
            ),
        -- Outside the linear fragment even normalised measures fail centrality
        check "Prob centrality of (^2) fails vs coin" $
          not
            ( approx
                (ev (score (^ (2 :: Int)) . coin) (\b -> if b then 10 else 1))
                (ev (coin . score (^ (2 :: Int))) (\b -> if b then 10 else 1))
            ),
        -- Fubini on the linear fragment
        check "Prob parFG == parGF on coin x coin (Fubini)" $
          let k ((), (b, d)) = (if b then 10 else 1) * (if d then 100 else 1) :: Double
           in approx
                (runProb (parFG coin coin) k ((), ((), ())))
                (runProb (parGF coin coin) k ((), ((), ()))),
        check "Prob parFG != parGF with squareK x coin (premonoidal)" $
          let k ((), (b, d)) = b + (if d then 10 else 1) :: Double
           in not
                ( approx
                    (runProb (parFG squareK coin) k ((), (2.0, ())))
                    (runProb (parGF squareK coin) k ((), (2.0, ())))
                ),
        -- Mass detects affineness / discardability
        check "Prob mass detects score breaking affineness" $
          approx (mass (1.0 :: Double) (score (* 2) . coin) ()) 2.0
            && approx (mass (1.0 :: Double) coin ()) 1.0,
        -- Copy naturality: the Markov law
        check "Prob copy natural for embed (deterministic fragment)" $
          let kSame ((), (b1, b2)) = if b1 == b2 then 1 else 0 :: Double
           in runProb (copyP . embed not) kSame ((), True)
                == runProb (parFG (embed not) (embed not) . copyP) kSame ((), True),
        check "Prob copy NOT natural for coin (correlation vs independence)" $
          let kSame ((), (b1, b2)) = if b1 == b2 then 1 else 0 :: Double
              corr = runProb (copyP . coin) kSame ((), ())
              indep = runProb (parFG coin coin . copyP) kSame ((), ())
           in approx corr 1.0 && approx indep 0.625 && corr /= indep,
        -- Discard on the mass-1 fragment
        check "Prob discard natural for coin (mass-1 fragment)" $
          runProb (coin . discardP) (\_ -> 1.0 :: Double) ((), ())
            == runProb discardP (\_ -> 1.0 :: Double) ((), ()),
        check "Prob discard fails for unnormalised score (*2) . coin" $
          runProb (score (* 2) . coin . discardP) (\_ -> 1.0 :: Double) ((), ())
            /= runProb discardP (\_ -> 1.0 :: Double) ((), ()),
        -- Traced Either: computability graded by scalar
        check "Prob traceEN converges to 1/p for geometric (error ~ q^fuel)" $
          let e n = ev (traceEN 0 n (geomBody 0.5)) fromIntegral
           in approx (e 60) 2.0 && e 5 < e 20 && e 20 < e 60,
        check "Prob Bool trace reachability via lazy (||)" $
          reach 2,
        -- Ends oracles
        check "O9 ends . splay == id" $
          let e :: Ends (->) () Int
              e = ends (const ()) (const 42)
              (write', receive') = splay e
              e' = ends write' receive'
           in run (box @(,) e') () == 42 && run (box @(,) e) () == 42,
        -- Keystone: System (Prob (->) r) s (Mono i o)
        check "Keystone: System (Prob Double) S3 (Mono () ()) typechecks" $
          length (occupancyProb 0) == 3,
        check "Keystone: exact occupancy after 2 steps" $
          occupancyProb 2 == [0.25, 0.5, 0.25],
        check "Keystone: exact occupancy after 3 steps" $
          let [p0, p1, p2] = occupancyProb 3
           in approx p0 0.25 && approx p1 0.375 && approx p2 0.375,
        check "Keystone: System (Prob Tropical) S3 (Mono () ()) typechecks" $
          length (viterbiCost 0) == 3,
        check "Keystone: tropical Viterbi cost after 2 steps" $
          viterbiCost 2 == [2.0, 3.0, 4.0],
        check "Keystone: tropical Viterbi cost after 3 steps" $
          viterbiCost 3 == [3.0, 4.0, 5.0]
      ]
  if and results
    then putStrLn "\nAll tests passed."
    else error "Some tests failed."
