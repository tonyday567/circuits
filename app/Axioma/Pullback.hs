module Axioma.Pullback
  ( pullbackTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Axioma.Test (approx)
import Circuit.Bimonoid (Copy (..), Merge (..))
import Circuit.Category ((.))
import Circuit.Net (Net, widen)
import Circuit.Pullback (Pullback (..), evalPullback)
import Circuit.Syntax (Layer (unit), Syntax (Lift))
import Circuit.Tensor (SemiTensor (..), Tensor)
import Circuit.Traced (Yank (..))
import Control.Exception (evaluate)
import Control.Monad (when)
import Data.Maybe (isNothing)
import System.Timeout (timeout)
import Prelude hiding (id, (.))

chainNet :: Net (,) Pullback Double Double
chainNet = plusN . parN . copyN
  where
    copyN :: Net (,) Pullback Double (Double, Double)
    copyN = unit (copy :: Pullback Double (Double, Double))
    parN :: Net (,) Pullback (Double, Double) (Double, Double)
    parN = widen (tensor (Lift (Pullback (* 2))) (Lift (Pullback (* 3))))
    plusN :: Net (,) Pullback (Double, Double) Double
    plusN = unit (plus :: Pullback (Double, Double) Double)

convergentBody :: Pullback (Double, Double) (Double, Double)
convergentBody = Pullback (\(dx', dy) -> (3.0 * dy, 2.0 * dx'))

divergentBody :: Pullback (Double, Double) (Double, Double)
divergentBody = Pullback (\(dx', dy) -> (a * dx' + c * dy, b * dx'))
  where
    a = 0.5
    b = 2.0
    c = 2.0

divergentGradient :: Double -> Double
divergentGradient = evalPullback net
  where
    a = 0.5
    b = 2.0
    c = 2.0
    starA = 1 / (1 - a)
    closedForm = Pullback (\dy -> b * starA * (c * dy))
    downstream = Pullback (* 2)
    net :: Net (,) Pullback Double Double
    net = unit downstream . unit closedForm

pullbackTopic :: Verbosity -> IO [Bool]
pullbackTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Pullback oracles"
  sequence
    [ checkV verbosity "evalPullback: cotangent of a composite is the composite of cotangents" $
        approx (evalPullback chainNet 1.0) 5.0,
      checkV verbosity "yank (Pullback): zero channel self-coupling solves the affine cotangent equation" $
        approx (runPullback (yank convergentBody) 1.0) 6.0,
      checkV verbosity "evalPullback: closed-form feedback gradient composes with downstream stages" $
        approx (divergentGradient 1.0) 16.0,
      checkIOV verbosity "yank (Pullback): nonzero channel self-coupling diverges on strict Double" $ do
        result <- timeout 1000000 (evaluate (runPullback (yank divergentBody) 1.0))
        pure (isNothing result)
    ]
