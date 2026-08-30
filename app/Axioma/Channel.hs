{-# LANGUAGE DataKinds #-}

-- | Par / linear distributivity and Poly.Channel oracles.
module Axioma.Channel
  ( channelTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Channel (Channel (..), commitChannel, constChannel, emitChannel, idChannel, mapChannel)
import Circuit.Moore (monoIn)
import Circuit.Par (Par (..), distL, distR, mix)
import Circuit.Poly (Eval (..), Mono, lens)
import Control.Monad (when)
import Data.Void (Void)
import Prelude hiding (id, (.))

channelTopic :: Verbosity -> IO [Bool]
channelTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Par and Poly.Channel oracles"
  sequence
    [ -- Par / linear distributivity
      checkV verbosity "Par distL is the one-way (,) / Either distributor" $
        distL ('x', Left True :: Either Bool Int) == Left ('x', True)
          && distR (Left True :: Either Bool Int, 'x') == Left True,
      checkV verbosity "Par unitlP collapses Void on Either" $
        unitlP (Right 42 :: Either Void Int) == (42 :: Int),
      checkV verbosity "Par unitrP collapses Void on Either" $
        unitrP (Left 42 :: Either Int Void) == (42 :: Int),
      -- Poly.Channel oracles (B2)
      checkV verbosity "Poly Channel id emits committed input" $
        case emitChannel (commitChannel (idChannel 0) (monoIn (42 :: Int))) of
          EP (EK o, EE _) -> o == 42,
      checkV verbosity "Poly Channel const ignores state" $
        case emitChannel (commitChannel (constChannel (7 :: Int)) (monoIn (99 :: Int))) of
          EP (EK o, EE _) -> o == 7,
      checkV verbosity "Poly Channel mapChannel applies lens forward and backward" $
        let ch0 = mapChannel (lens (+ 1) (\_ d -> d - 1 :: Int)) (idChannel 0)
            ev0 = emitChannel ch0
            ch1 = commitChannel ch0 (monoIn 5)
            ev1 = emitChannel ch1
         in case (ev0, ev1) of
              (EP (EK o0, EE _), EP (EK o1, EE _)) -> o0 == 1 && o1 == 5
    ]
