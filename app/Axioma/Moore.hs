{-# LANGUAGE DataKinds #-}

-- | Moore machine and polynomial channel oracles.
module Axioma.Moore
  ( mooreTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Moore (Moore, TMoore (..), mooreMachine, mooreToTMoore, peekMoore, runMooreMono, stepMoore)
import Circuit.Par (Par (..), distL, distR)
import Circuit.Poly (Mono)
import Circuit.Syntax (eval)
import Control.Category (id)
import Control.Monad (when)
import Data.Void (Void)
import Prelude hiding (id, (.))

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
      checkV verbosity "peekMoore reads current output without consuming input" $
        let sys = mooreMachine (\s i -> s + i) (\s -> s * 2) :: Moore (,) Int (->) (Mono Int Int)
         in peekMoore sys 5 == 10,
      checkV verbosity "stepMoore advances state by one input" $
        let sys = mooreMachine (\s i -> s + i) (\s -> s * 2) :: Moore (,) Int (->) (Mono Int Int)
         in stepMoore sys 5 3 == 8,
      checkV verbosity "runMooreMono exposes output and transition" $
        let sys = mooreMachine (\s i -> s + i) (\s -> s * 2) :: Moore (,) Int (->) (Mono Int Int)
            (o, next) = runMooreMono sys 5
         in o == 10 && next 3 == 8,
      checkV verbosity "Moore id lens emits committed input" $
        let sys = mooreMachine (\_s d -> d) id :: Moore (,) Int (->) (Mono Int Int)
         in peekMoore sys (stepMoore sys 0 (42 :: Int)) == 42,
      checkV verbosity "Moore const lens ignores state" $
        let sys = mooreMachine (\s _d -> s) (const (7 :: Int)) :: Moore (,) Int (->) (Mono Int Int)
         in peekMoore sys (stepMoore sys 0 (99 :: Int)) == 7,
      checkV verbosity "mooreToTMoore hides state as a feedback trace" $
        let sys = mooreMachine (\_s d -> d) id :: Moore (,) Int (->) (Mono Int Int)
            TMoore tr = mooreToTMoore sys
         in eval tr (Right 42 :: Either Void Int) == (42 :: Int, ())
    ]
