{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Circuit.Category (id, (.), (.>))
import Circuit.Channel (assoc, assoc', strength, trace)
import Circuit.Dagger (CopyDiscard (..), MergeZero (..))
import Circuit.Ends (Ends (..), box, ends, splay)
import Circuit.FinRel
import Circuit.Layer (run)
import Circuit.Process (Process (..), encode, fold, register, scan)
import Circuit.Tensor (Action (..), Tensor (..))
import Data.List (scanl')
import Data.Maybe (isNothing)
import Data.Proxy (Proxy (..))
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
        -- QuickCheck Process / Loop equivalence
        qcCheck "QC: scan == run . encode" prop_scan_encode,
        qcCheck "QC: register agrees with delayed feedback" prop_register_trace,
        -- Ends oracles
        check "O9 ends . splay == id" $
          let e :: Ends (->) () Int
              e = ends (const ()) (const 42)
              (write', receive') = splay e
              e' = ends write' receive'
           in run (box @(,) e') () == 42 && run (box @(,) e) () == 42
      ]
  if and results
    then putStrLn "\nAll tests passed."
    else error "Some tests failed."
