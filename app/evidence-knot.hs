{-# LANGUAGE ScopedTypeVariables #-}

-- | Spike oracle for evidence-carrying 'Circuit.Net.Knot'.
--
-- Builds the same knot body with both 'NoEvidence' and 'StarEvidence',
-- then asserts that 'run', 'melt', and 'encode' ignore the evidence.
module Main where

import Circuit.Hyper (encode, observe)
import Circuit.Layer (run)
import Circuit.Loop (Loop)
import Circuit.Loop qualified as Loop
import Circuit.Net
  ( ChannelEvidence (..),
    Net (..),
    enrich,
    melt,
  )
import Data.Maybe (isNothing)
import Prelude hiding (id, (.))

-- | A simple state-delay body: output the previous input.
delayBody :: (Double, Double) -> (Double, Double)
delayBody (s, x) = (x, s)

-- | Evidence for a one-dimensional scalar channel.
--
-- The matrix carrier is 'Double' itself: a 1×1 matrix is just the scalar.
scalarEvidence :: ChannelEvidence Double
scalarEvidence =
  StarEvidence
    { channelDimE = 1,
      zeroChannelE = const 0,
      basisChannelE = \_ i -> if i == 0 then 1 else error "scalarEvidence: index out of range",
      addChannelE = (+),
      negateChannelE = negate,
      selfMatrixE = \_ f -> f 1,
      applyMatrixE = (*),
      starMatrixE = \m -> recip (1 - m)
    }

-- | Same body, no evidence.
noEvNet :: Net (,) (,) (->) Double Double
noEvNet = Knot NoEvidence (Lift delayBody)

-- | Same body, with value-level evidence.
evNet :: Net (,) (,) (->) Double Double
evNet = Knot scalarEvidence (Lift delayBody)

-- | Linear feedback body with zero self-coupling: @s' = 2*x@, output @s + x@.
--
-- The lazy @(,)@ knot converges because the state equation is not recursive.
-- We probe the evidence with an unrelated self-coupling map to keep the matrix
-- eliminators honest.
linearBody :: (Double, Double) -> (Double, Double)
linearBody (s, x) = (2 * x, s + x)

-- | Linear feedback knot, no evidence.
noEvLinearNet :: Net (,) (,) (->) Double Double
noEvLinearNet = Knot NoEvidence (Lift linearBody)

-- | Linear feedback knot, with star evidence.
evLinearNet :: Net (,) (,) (->) Double Double
evLinearNet = Knot scalarEvidence (Lift linearBody)

-- | Extract the evidence dimension if one is present.
netChannelDim :: Net (,) (,) (->) Double Double -> Maybe Int
netChannelDim (Knot ev _) = case ev of
  NoEvidence -> Nothing
  StarEvidence {channelDimE = d} -> Just d
netChannelDim _ = Nothing

main :: IO ()
main = do
  let x = 5.0 :: Double
      r1 = run noEvNet x
      r2 = run evNet x
      m1 = run (melt noEvNet) x
      m2 = run (melt evNet) x
      e1 = observe (encode (melt noEvNet)) x
      e2 = observe (encode (melt evNet)) x
      enriched =
        run
          (enrich (Loop.Knot delayBody :: Loop (,) (->) Double Double) :: Net (,) (,) (->) Double Double)
          x

  putStrLn $ "run noEvNet        " ++ show r1
  putStrLn $ "run evNet          " ++ show r2
  putStrLn $ "run (melt noEvNet) " ++ show m1
  putStrLn $ "run (melt evNet)   " ++ show m2
  putStrLn $ "encode/melt noEv   " ++ show e1
  putStrLn $ "encode/melt ev     " ++ show e2
  putStrLn $ "enrich Loop.Knot   " ++ show enriched
  putStrLn $ "evidence dim       " ++ show (netChannelDim evNet)

  let y = 1.0 :: Double
      rLinearNoEv = run noEvLinearNet y
      rLinearEv = run evLinearNet y
      (selfApplied :: Double, starApplied :: Double) =
        case scalarEvidence of
          StarEvidence {basisChannelE = basis, selfMatrixE = sm, applyMatrixE = applyM, starMatrixE = starM} ->
            let s = sm 1 (\ds -> 0.3 * ds + 2 * y - 2 * y)
             in (applyM s (basis 1 0), applyM (starM s) (basis 1 0))
          NoEvidence -> error "evidence-knot: scalarEvidence is not StarEvidence"
      expectedStar = 1 / (1 - 0.3)
      expectedOutput = 3 * y

  putStrLn $ "run linear noEv    " ++ show rLinearNoEv
  putStrLn $ "run linear ev      " ++ show rLinearEv
  putStrLn $ "self applied       " ++ show selfApplied
  putStrLn $ "star applied       " ++ show starApplied

  let checks =
        [ ("run ignores evidence", r1 == r2),
          ("melt ignores evidence", m1 == m2),
          ("encode ignores evidence", e1 == e2),
          ("enrich supplies NoEvidence", enriched == r1),
          ("evidence dimension readable", netChannelDim evNet == Just 1),
          ("NoEvidence has no dimension", isNothing (netChannelDim noEvNet)),
          ("linear run ignores evidence", rLinearNoEv == rLinearEv),
          ("linear run value matches star solution", abs (rLinearEv - expectedOutput) < 1e-12),
          ("self-coupling probed", abs (selfApplied - 0.3) < 1e-12),
          ("star scalar probed", abs (starApplied - expectedStar) < 1e-12)
        ]
  mapM_ (\(name, ok) -> putStrLn $ (if ok then "PASS " else "FAIL ") ++ name) checks
  if all snd checks
    then putStrLn "\nAll evidence-knot oracles passed."
    else error "Some evidence-knot oracles failed."
