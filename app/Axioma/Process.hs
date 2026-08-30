{-# LANGUAGE DataKinds #-}

-- | Process, Mealy, Body, Trace, Net, and Shared-in-Process oracles.
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
import Circuit.Body (Body, SomeBody (..), runSomeBody)
import Circuit.Body qualified as Body
import Circuit.Category (id, (.), (.>))
import Circuit.Layer (run)
import Circuit.Moore (Boundary (..), Moore, isMark, isPayload, markMoore, mooreMachine)
import Circuit.Net qualified as Net
import Circuit.Poly (Mono)
import Circuit.Process (PProcess (..), Process (..), asPProcess, asProcess, delay, encodeList, fold, foldPProcess, mealy, pprocessAsMoore, register, runMealy, scan, scanPProcess)
import Circuit.Process qualified as Process
import Circuit.Shared (Pick (..), Schedule (..), sharedBy)
import Circuit.Syntax (Syntax (..), eval)
import Circuit.Syntax qualified as Syn
import Circuit.Tensor (Bias (..), tensor)
import Circuit.Trace (Trace, base)
import Circuit.Traced (assoc, assoc', slide, strength, yank)
import Control.Monad (when)
import Data.Maybe (catMaybes, isNothing)
import Data.These (These (..))
import Data.Tuple qualified as Tuple
import Prelude hiding (curry, id, uncurry, (.))
import Prelude qualified as Pre

-- | Helper that fixes the Either tensor for 'yank' over list functions.
yankEither :: (Either s a -> Either s b) -> Trace Either (->) a b
yankEither = yank . base

-- | Residual state for the pair-sum mealy process.
data PS = Empty | Held Int
  deriving (Eq, Show)

-- | Mealy process that forwards every input.
linearP :: Process Int (Maybe Int)
linearP = mealy () (\() a -> ((), Just a))

-- | Mealy process that sums consecutive pairs.
pairSumP :: Process Int (Maybe Int)
pairSumP = mealy Empty $ \s x -> case s of
  Empty -> (Held x, Nothing)
  Held y -> (Empty, Just (x + y))

-- | Mealy process that emits the count of inputs seen so far.
countP :: Process () (Maybe Int)
countP = mealy 0 (\n _ -> let n' = n + 1 in (n', Just n'))

processTopic :: Verbosity -> IO [Bool]
processTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Process, Body, Trace, Net, and Mealy oracles"
  sequence
    [ -- Para laws promoted to circuits-learn-axioma (11 Aug 2026).
      -- The L1/L2 constant-state trace checks now live there alongside
      -- the full Category associativity and identity oracles for Para.
      -- Circuit.Process oracles
      checkV verbosity "Process seed emits first output" $
        scan sumP [5] == [5],
      checkV verbosity "Process scan semantics" $
        scan sumP [1, 2, 3] == [1, 3, 6],
      checkV verbosity "Process fold semantics" $
        fold sumP [1, 2, 3] == Just 6,
      checkV verbosity "Process fold empty" $
        isNothing (fold sumP []),
      -- PProcess oracles
      checkV verbosity "PProcess scan matches Process scan" $
        let pp = PProcess 0 (+) id
         in scanPProcess pp 0 [1, 2, 3 :: Int] == [1, 3, 6],
      checkV verbosity "asPProcess converts monomial Moore" $
        let sys = mooreMachine (+) id :: Moore (,) (->) Int (Mono Int Int)
            pp = asPProcess sys 0
         in scanPProcess pp 0 [1, 2, 3 :: Int] == [1, 3, 6],
      checkV verbosity "asProcess . asPProcess round-trips" $
        let sys = mooreMachine (+) id :: Moore (,) (->) Int (Mono Int Int)
            pp = asPProcess sys 0
         in scan (asProcess pp) [1, 2, 3 :: Int] == [1, 3, 6],
      checkV verbosity "PProcess fold matches Process fold" $
        let pp = PProcess 0 (+) id
         in foldPProcess pp 0 [1, 2, 3 :: Int] == Just 6,
      checkV verbosity "pprocessAsMoore round-trips" $
        let sys = mooreMachine (+) id :: Moore (,) (->) Int (Mono Int Int)
            pp = asPProcess sys 0
            sys' = pprocessAsMoore pp
            pp' = asPProcess sys' 0
         in scanPProcess pp' 0 [1, 2, 3 :: Int] == [1, 3, 6],
      checkV verbosity "Process scan == run . encodeList" $
        Syn.eval (encodeList sumP) [1, 2, 3] == scan sumP [1, 2, 3],
      checkV verbosity "Process Yank (,) yanking" $
        scan (yank swapPairP) [1, 2, 3] == [1, 2, 3],
      checkV verbosity "Process Yank Either yanking" $
        scan (yank swapEitherP) [1, 2, 3] == [1, 2, 3],
      checkV verbosity "Process register (EWMA)" $
        scan (ewma 0.5 0.0) [1.0, 1.0, 1.0] == [0.5, 0.75, 0.875],
      checkV verbosity "Process register == trace . strength . delay (EWMA)" $
        let body = ewmaBody 0.5
            s0 = 0.0
            xs = [1.0, 1.0, 1.0]
            swapP (Process i st ex) =
              Process (i . Tuple.swap) (\s -> st s . Tuple.swap) (Tuple.swap . ex)
         in scan (register s0 body) xs
              == scan (yank (swapP (body . strength (delay s0)))) xs,
      -- Process / Body equivalence
      checkV verbosity "processToSomeBody sumP agrees with scan" $
        runSomeBody (Process.processToSomeBody sumP) [1, 2, 3 :: Int] == scan sumP [1, 2, 3],
      checkV verbosity "processToSomeBody swapPairP agrees with scan" $
        runSomeBody (Process.processToSomeBody swapPairP) [(1, 2), (3, 4), (5, 6)] == scan swapPairP [(1, 2), (3, 4), (5, 6)],
      checkV verbosity "processToSomeBody ewma agrees with scan" $
        runSomeBody (Process.processToSomeBody (ewma 0.5 0.0)) [1.0, 1.0, 1.0] == scan (ewma 0.5 0.0) [1.0, 1.0, 1.0],
      -- Process / Trace Either round-trip factors through Body Either ch (->)
      checkV verbosity "Process encodeList factors through Body Either ch (->)" $
        let viaBody p = case Process.processToBody p of SomeBody _ (Body.Body f) -> yankEither f
         in scan sumP [1, 2, 3] == Syn.eval (viaBody sumP) [1, 2, 3]
              && scan swapPairP [(1, 2), (3, 4), (5, 6)] == Syn.eval (viaBody swapPairP) [(1, 2), (3, 4), (5, 6)]
              && scan (ewma 0.5 0.0) [1.0, 1.0, 1.0] == Syn.eval (viaBody (ewma 0.5 0.0)) [1.0, 1.0, 1.0],
      -- Process as a base arrow for Trace / Net / Shared
      checkV verbosity "Process lifts into Trace (,) Process" $
        scan (Syn.eval (base sumP :: Trace (,) Process Int Int)) [1, 2, 3]
          == scan sumP [1, 2, 3],
      checkV verbosity "Net (,) Process copy uses Process.copy" $
        let p = run (Lift (copy :: Process Int (Int, Int)) :: Net.Net (,) Process Int (Int, Int)) :: Process Int (Int, Int)
         in scan p [5] == [(5, 5)],
      checkV verbosity "Net (,) Process plus uses Process.plus" $
        let p = run (Lift (plus :: Process (Int, Int) Int) :: Net.Net (,) Process (Int, Int) Int) :: Process (Int, Int) Int
         in scan p [(2, 3)] == [5],
      checkV verbosity "Shared (,) Process LR order differs from RL" $
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
