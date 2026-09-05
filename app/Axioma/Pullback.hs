-- | Pullback oracles — the chain-rule-under-feedback claim of
-- 'Circuit.Pullback.evalPullback' and the affine-feedback claim of the
-- @Yank (,) Pullback@ instance.
--
-- Each clause is the named creditor of the haddock claim it guards:
-- 'evalPullback' claims the cotangent of a composite is the composite of
-- the cotangents, and the @Yank (,) Pullback@ instance claims the lazy
-- knot solves the affine cotangent equation, diverging on strict carriers
-- exactly when the channel self-coupling is nonzero.
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
import Circuit.Tensor (Tensor (..))
import Circuit.Traced (Yank (..))
import Control.Exception (evaluate)
import Control.Monad (when)
import Data.Maybe (isNothing)
import System.Timeout (timeout)
import Prelude hiding (id, (.))

-- | Cotangent net for the acyclic chain-rule clause: the cotangent flow of
-- the primal map @u ↦ 2u + 3u@, built from copy, parallel scale, and merge
-- rows.  Guards the 'evalPullback' chain-rule claim.
chainNet :: Net (,) Pullback Double Double
chainNet = plusN . parN . copyN
  where
    copyN :: Net (,) Pullback Double (Double, Double)
    copyN = unit (copy :: Pullback Double (Double, Double))
    parN :: Net (,) Pullback (Double, Double) (Double, Double)
    parN = widen (tensor (Lift (Pullback (* 2))) (Lift (Pullback (* 3))))
    plusN :: Net (,) Pullback (Double, Double) Double
    plusN = unit (plus :: Pullback (Double, Double) Double)

-- | Convergent feedback body: the channel-out cotangent @dx = 3 dy@ has no
-- self-coupling, so the lazy 'yank' knot terminates.  Primal story:
-- @x' = 2u@, @y = 3x@, composite gradient @dy/du = 6@.  Guards the
-- @Yank (,) Pullback@ zero-coupling half of the affine-feedback claim.
convergentBody :: Pullback (Double, Double) (Double, Double)
convergentBody = Pullback (\(dx', dy) -> (3.0 * dy, 2.0 * dx'))

-- | Divergent feedback body: channel self-coupling @a = 0.5@ sends the lazy
-- 'yank' knot into a strict 'Double' loop.  Primal story: @x' = 0.5x + 2u@,
-- @y = 2x@, fixpoint @x = 4u@, composite gradient @8@.  The gradient is
-- read in closed form @b ⋅ star a ⋅ c@ with @star a = 1/(1-a)@ — the
-- star-elimination route the @Yank (,) Pullback@ haddock points at.
divergentBody :: Pullback (Double, Double) (Double, Double)
divergentBody = Pullback (\(dx', dy) -> (a * dx' + c * dy, b * dx'))
  where
    a = 0.5
    b = 2.0
    c = 2.0

-- | Closed-form gradient of the divergent body, composed with a downstream
-- stage @z = 2y@ through 'evalPullback': the cotangent of the composite is
-- the composite of the cotangents, even when the feedback contribution
-- arrived as a closed-form star rather than a lazy knot.  Guards the
-- 'evalPullback' claim at @16@.
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
