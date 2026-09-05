{-# LANGUAGE DataKinds #-}

-- | Mealy, Mealy, Body, Trace, Net, and Shared-in-Mealy oracles.
module Axioma.Process
  ( processTopic,
  )
where

import Axioma.Common
  ( Verbosity (..),
    checkV,
    ewma,
    ewmaBody,
    sharedAddP,
    sharedDoubleP,
    sumP,
    swapEitherP,
    swapPairP,
  )
import Circuit.Bimonoid (Copy (..), Merge (..))
import Circuit.Body (Body (..))
import Circuit.Category (id, (.))
import Circuit.Net qualified as Net
import Circuit.Process (Mealy (..), Process (..), bodyToMealy, delay, encodeList, fold, foldProcess, mealy, register, runMealy, scan, scanProcess)
import Circuit.Shared (Pick (..), Schedule (..), sharedBy)
import Circuit.Syntax (Syntax (..), run)
import Circuit.Syntax qualified as Syn
import Circuit.Tensor (Bias (..))
import Circuit.Trace (Trace)
import Circuit.Traced (strength, yank)
import Control.Monad (when)
import Data.Maybe (catMaybes, isNothing)
import Data.These (These (..))
import Data.Tuple qualified as Tuple
import Prelude hiding (curry, id, uncurry, (.))

-- | Residual state for the pair-sum mealy process.
data PS = Empty | Held Int
  deriving (Eq, Show)

-- | Mealy process that forwards every input.
linearP :: Mealy Int (Maybe Int)
linearP = mealy () (\() a -> ((), Just a))

-- | Mealy process that sums consecutive pairs.
pairSumP :: Mealy Int (Maybe Int)
pairSumP = mealy Empty $ \s x -> case s of
  Empty -> (Held x, Nothing)
  Held y -> (Empty, Just (x + y))

-- | Mealy process that emits the count of inputs seen so far.
countP :: Mealy () (Maybe Int)
countP = mealy 0 (\n _ -> let n' = n + 1 in (n', Just n'))

-- | Body whose output never reads the carrier: the state counts, the
-- output echoes the input.
countBody :: Body (,) Int (->) Int Int
countBody = Body $ \(s, a) -> (s + 1, a)

-- | Body that reads its carrier: the output is the previous state — a
-- one-tick delay.
delayBody :: Body (,) Int (->) Int Int
delayBody = Body $ \(s, a) -> (a, s)

processTopic :: Verbosity -> IO [Bool]
processTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Process, Mealy, Body, Trace, and Net oracles"
  sequence
    [ -- Para laws promoted to circuits-learn-axioma (11 Aug 2026).
      -- The L1/L2 constant-state trace checks now live there alongside
      -- the full Category associativity and identity oracles for Para.
      -- Circuit.Process oracles
      checkV verbosity "Mealy seed emits first output" $
        scan sumP [5] == [5],
      checkV verbosity "Mealy scan semantics" $
        scan sumP [1, 2, 3] == [1, 3, 6],
      checkV verbosity "Mealy fold semantics" $
        fold sumP [1, 2, 3] == Just 6,
      checkV verbosity "Mealy fold empty" $
        isNothing (fold sumP []),
      -- Process oracles
      checkV verbosity "Process scan matches Mealy scan" $
        let pp = Process 0 (+) id
         in scanProcess pp [1, 2, 3 :: Int] == [1, 3, 6],
      checkV verbosity "Process fold matches Mealy fold" $
        let pp = Process 0 (+) id
         in foldProcess pp [1, 2, 3 :: Int] == Just 6,
      checkV verbosity "Mealy scan == run . encodeList" $
        Syn.eval (encodeList sumP) [1, 2, 3] == scan sumP [1, 2, 3],
      checkV verbosity "Mealy Yank (,) yanking" $
        scan (yank swapPairP) [1, 2, 3] == [1, 2, 3],
      checkV verbosity "Mealy Yank Either yanking" $
        scan (yank swapEitherP) [1, 2, 3] == [1, 2, 3],
      checkV verbosity "Mealy register (EWMA)" $
        scan (ewma 0.5 0.0) [1.0, 1.0, 1.0] == [0.5, 0.75, 0.875],
      checkV verbosity "Mealy register == trace . strength . delay (EWMA)" $
        let body = ewmaBody 0.5
            s0 = 0.0
            xs = [1.0, 1.0, 1.0]
            swapP (Mealy i st ex) =
              Mealy (i . Tuple.swap) (\s -> st s . Tuple.swap) (Tuple.swap . ex)
         in scan (register s0 body) xs
              == scan (yank (swapP (body . strength (delay s0)))) xs,
      -- Body runner
      checkV verbosity "scanning a body via bodyToMealy agrees with a known body" $
        let sumBody = Body $ \(s, a) -> (s + a, s + a)
         in scan (bodyToMealy sumBody 0) [1, 2, 3 :: Int] == [1, 3, 6],
      -- Pointing discharge oracles
      checkV verbosity "pointing: closure discharge agrees with any seed on a seed-independent body" $
        let Body f = countBody
         in map (yank f) [3, 5, 7] == [3, 5, 7]
              && scan (bodyToMealy countBody 0) [3, 5, 7] == [3, 5, 7]
              && scan (bodyToMealy countBody 99) [3, 5, 7] == [3, 5, 7],
      checkV verbosity "pointing: explicit discharge carries the seed the closure drops" $
        let Body f = delayBody
         in scan (bodyToMealy delayBody 0) [3, 5, 7] == [0, 3, 5]
              && map (yank f) [3, 5, 7] == [3, 5, 7],
      -- Mealy as a base arrow for Trace / Net / Shared
      checkV verbosity "Mealy lifts into Trace (,) Mealy" $
        scan (Syn.eval (Lift sumP :: Trace (,) Mealy Int Int)) [1, 2, 3]
          == scan sumP [1, 2, 3],
      checkV verbosity "Net (,) Mealy copy uses Process.copy" $
        let p = run (Lift (copy :: Mealy Int (Int, Int)) :: Net.Net (,) Mealy Int (Int, Int)) :: Mealy Int (Int, Int)
         in scan p [5] == [(5, 5)],
      checkV verbosity "Net (,) Mealy plus uses Process.plus" $
        let p = run (Lift (plus :: Mealy (Int, Int) Int) :: Net.Net (,) Mealy (Int, Int) Int) :: Mealy (Int, Int) Int
         in scan p [(2, 3)] == [5],
      checkV verbosity "Shared (,) Mealy LR order differs from RL" $
        let lr = sharedBy (Schedule (,Both LeftFirst) :: Schedule Int) sharedAddP sharedDoubleP
            rl = sharedBy (Schedule (,Both RightFirst) :: Schedule Int) sharedAddP sharedDoubleP
         in scan lr [(1, (2, 3))] == [(6, These 3 6)]
              && scan rl [(1, (2, 3))] == [(4, These 4 2)],
      -- Mealy process oracles
      checkV verbosity "mealy linear forwards every input" $
        runMealy linearP [1, 2, 3 :: Int] == [1, 2, 3],
      checkV verbosity "mealy pairSum buffers and sums pairs" $
        runMealy pairSumP [1, 2, 3, 4 :: Int] == [3, 7],
      checkV verbosity "mealy pairSum leaves one input unemitted" $
        runMealy pairSumP [1, 2, 3 :: Int] == [3],
      checkV verbosity "mealy count emits accumulating count" $
        runMealy countP [(), (), ()] == [1, 2, 3],
      checkV verbosity "mealy scan matches runMealy" $
        catMaybes (scan pairSumP [1, 2, 3, 4 :: Int]) == runMealy pairSumP [1, 2, 3, 4],
      checkV verbosity "mealy process encodeLists to Trace Either" $
        Syn.eval (encodeList pairSumP) [1, 2, 3, 4 :: Int]
          == scan pairSumP [1, 2, 3, 4]
    ]
