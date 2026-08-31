{-# LANGUAGE DataKinds #-}

-- | Moore machine and polynomial channel oracles.
module Axioma.Moore
  ( mooreTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Moore (Moore, TMoore (..), fromEvalMoore, mooreToTMoore, toEvalMoore)
import Circuit.Par (Par (..), distL, distR)
import Circuit.Poly (Eval (..), Mono)
import Circuit.Syntax (eval)
import Control.Category (id)
import Control.Monad (when)
import Data.Void (Void)
import Prelude hiding (id, (.))

mkMoore :: (s -> a -> s) -> (s -> b) -> Moore (,) s (->) (Mono a b)
mkMoore st ex = fromEvalMoore $ \s -> EP (EK (ex s), EE (st s))

peekM :: Moore (,) s (->) (Mono i o) -> s -> o
peekM sys s = case toEvalMoore sys s of EP (EK o, EE _) -> o

stepM :: Moore (,) s (->) (Mono i o) -> s -> i -> s
stepM sys s i = case toEvalMoore sys s of EP (EK _, EE f) -> f i

runMono :: Moore (,) s (->) (Mono i o) -> s -> (o, i -> s)
runMono sys s = case toEvalMoore sys s of EP (EK o, EE f) -> (o, f)

mooreTopic :: Verbosity -> IO [Bool]
mooreTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Moore machine and Par oracles"
  sequence
    [ -- Par / linear distributivity
      checkV verbosity "Par distL is the one-way (,) / Either distributor" $
        distL ('x', Left True :: Either Bool Int) == Left ('x', True)
          && distR (Left True :: Either Bool Int, 'x') == Left True,
      checkV verbosity "Par unitlP collapses Void on Either" $
        unitlP (Right 42 :: Either Void Int) == (42 :: Int),
      checkV verbosity "Par unitrP collapses Void on Either" $
        unitrP (Left 42 :: Either Int Void) == (42 :: Int),
      -- Moore peek/step oracles
      checkV verbosity "peekM reads current output without consuming input" $
        let sys = mkMoore (\s i -> s + i) (\s -> s * 2) :: Moore (,) Int (->) (Mono Int Int)
         in peekM sys 5 == 10,
      checkV verbosity "stepM advances state by one input" $
        let sys = mkMoore (\s i -> s + i) (\s -> s * 2) :: Moore (,) Int (->) (Mono Int Int)
         in stepM sys 5 3 == 8,
      checkV verbosity "runMono exposes output and transition" $
        let sys = mkMoore (\s i -> s + i) (\s -> s * 2) :: Moore (,) Int (->) (Mono Int Int)
            (o, next) = runMono sys 5
         in o == 10 && next 3 == 8,
      checkV verbosity "Moore id lens emits committed input" $
        let sys = mkMoore (\_s d -> d) id :: Moore (,) Int (->) (Mono Int Int)
         in peekM sys (stepM sys 0 (42 :: Int)) == 42,
      checkV verbosity "Moore const lens ignores state" $
        let sys = mkMoore (\s _d -> s) (const (7 :: Int)) :: Moore (,) Int (->) (Mono Int Int)
         in peekM sys (stepM sys 0 (99 :: Int)) == 7,
      checkV verbosity "mooreToTMoore hides state as a feedback trace" $
        let sys = mkMoore (\_s d -> d) id :: Moore (,) Int (->) (Mono Int Int)
            TMoore tr = mooreToTMoore sys
         in eval tr (Right 42 :: Either Void Int) == (42 :: Int, ())
    ]
