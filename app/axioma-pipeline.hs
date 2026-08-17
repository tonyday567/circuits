{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Pipeline oracle for Markov-category separator tests.
--
-- This executable holds the research-stage checks that grew out of the
-- affine/linear excavation: finite-separator oracles for 'Prob', the
-- 'FinRel'/'Prob' contrast case, and the 'squareKBool' premonoidal witness.
-- Split off from 'axioma.hs' because that file had become unwieldy.
module Main where

import Circuit.Category (id, (.), (.>))
import Circuit.Dagger (Copy (..), Discard (..))
import Circuit.FinRel
import Circuit.Markov (copyNatural, deterministic, discardNatural)
import Circuit.Prob (Prob (..), choiceBy, copyP, discardP, embed, fromWeighted, parFG, parGF, score)
import Circuit.Tensor (Tensor (..))
import Control.Monad (replicateM)
import Data.Kind (Type)
import GHC.TypeNats (KnownNat, natVal)
import Prelude hiding (curry, id, uncurry, (.))
import Prelude qualified as Pre

type F = Bool

type N1 = FinObj 1

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

check :: String -> Bool -> IO Bool
check name ok = do
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok

-- | Approximate equality for floating-point oracles.
approx :: Double -> Double -> Bool
approx x y = abs (x - y) < 1e-9

-- ---------------------------------------------------------------------------
-- Markov separator oracles for Prob
-- ---------------------------------------------------------------------------
--
-- 'Prob' morphisms are rank-2, so decidable equality is unavailable in
-- general.  We instead test against a finite /separator/: a set of
-- continuations and inputs that is large enough to catch the laws we care
-- about here.  The unit context is enough for these examples because the
-- morphisms are measure kernels.

-- | All functions from a finite bounded enumerable type to 'Bool'.
allBoolFns :: forall a. (Bounded a, Enum a) => [a -> Bool]
allBoolFns = map (\bits a -> bits !! fromEnum a) (replicateM (fromEnum (maxBound :: a) + 1) [False, True])

-- | All functions from a pair of finite bounded enumerable values to 'Bool'.
--
-- Pairs do not have an 'Enum' instance in current GHC, so we enumerate the
-- underlying values explicitly and index into the truth table.
pairBoolFns :: forall b. (Enum b) => [b] -> [(b, b) -> Bool]
pairBoolFns bs = map (\bits (b1, b2) -> bits !! (fromEnum b1 * n + fromEnum b2)) (replicateM (n * n) [False, True])
  where
    n = length bs

-- | Equality oracle for @Prob (->) r a b@ using a supplied input set and
-- continuation set.
probEqOver ::
  forall a b r.
  (Bounded a, Enum a, Eq r) =>
  [b -> r] ->
  Prob (->) r a b ->
  Prob (->) r a b ->
  Bool
probEqOver ks (Prob p) (Prob q) =
  and
    [ p (\((), b) -> k b) ((), a) == q (\((), b) -> k b) ((), a)
    | k <- ks,
      a <- [minBound .. maxBound :: a]
    ]

-- | Equality oracle for @Prob (->) Double a b@ using a supplied input set and
-- {0,1}-valued continuation set.
probEqDoubleOver ::
  forall a b.
  (Bounded a, Enum a) =>
  [b -> Double] ->
  Prob (->) Double a b ->
  Prob (->) Double a b ->
  Bool
probEqDoubleOver ks (Prob p) (Prob q) =
  and
    [ approx (p (\((), b) -> k b) ((), a)) (q (\((), b) -> k b) ((), a))
    | k <- ks,
      a <- [minBound .. maxBound :: a]
    ]

-- | Separator predicate for copy-naturality with a 'Bool' scalar.
probCopySep ::
  forall a b.
  (Bounded a, Enum a, Bounded b, Enum b) =>
  Prob (->) Bool a (b, b) ->
  Prob (->) Bool a (b, b) ->
  Bool
probCopySep p q =
  probEqOver (pairBoolFns bs) p q
  where
    bs = [minBound .. maxBound :: b]

-- | Separator predicate for copy-naturality with a 'Double' scalar.
probCopySepDouble ::
  forall a b.
  (Bounded a, Enum a, Bounded b, Enum b) =>
  Prob (->) Double a (b, b) ->
  Prob (->) Double a (b, b) ->
  Bool
probCopySepDouble p q =
  probEqDoubleOver (map toDoubleFn (pairBoolFns bs)) p q
  where
    bs = [minBound .. maxBound :: b]
    toDoubleFn k (b1, b2) = if k (b1, b2) then 1 else 0 :: Double

-- | Separator predicate for discard-naturality with a 'Double' scalar.
probDiscardSep ::
  forall a.
  (Bounded a, Enum a) =>
  Prob (->) Double a () ->
  Prob (->) Double a () ->
  Bool
probDiscardSep p q =
  probEqDoubleOver [const 0, const 1] p q

-- | Copy-naturality check for the premonoidal 'Prob' base, which has no
-- canonical 'Tensor' instance.  The caller supplies the nesting ('parFG' or
-- 'parGF') to test.
copyNaturalP ::
  (Prob (->) r a (b, b) -> Prob (->) r a (b, b) -> Bool) ->
  (forall c d. Prob (->) r c d -> Prob (->) r c d -> Prob (->) r (c, c) (d, d)) ->
  Prob (->) r a b ->
  Bool
copyNaturalP eq parF f = eq (copyP . f) (parF f f . copyP)

-- | Discard-naturality check for the premonoidal 'Prob' base.
discardNaturalP ::
  (Prob (->) r a () -> Prob (->) r a () -> Bool) ->
  Prob (->) r a b ->
  Bool
discardNaturalP eq f = eq (discardP . f) discardP

-- | A non-deterministic Bool kernel analogous to 'squareK' over 'Double'.
--
-- 'squareK' squares the continuation with scalar multiplication; over 'Bool'
-- that multiplication is '(/=)' (XOR) on the Boolean ring.  The kernel
-- queries the continuation at both truth values, so it is non-linear and
-- lives outside the deterministic centre.
squareKBool :: Prob (->) Bool Bool Bool
squareKBool = choiceBy (/=) (embed id) (embed not)

-- ---------------------------------------------------------------------------
-- Markov-category examples over FinRel Bool (GF(2))
-- ---------------------------------------------------------------------------

-- | Identity relation on N1 — deterministic.
finRelId :: FinRel F N1 N1
finRelId = FinRel 1 1 [[True, True]]

-- | Zero map on N1 — deterministic.
finRelZeroMap :: FinRel F N1 N1
finRelZeroMap = FinRel 1 1 [[True, False]]

-- | Total relation on N1 — total but not a function.
finRelTotal :: FinRel F N1 N1
finRelTotal = FinRel 1 1 [[True, False], [False, True]]

-- | Neither total nor functional: relates 0 to both 0 and 1.
finRelNeither :: FinRel F N1 N1
finRelNeither = FinRel 1 1 [[False, True]]

-- ---------------------------------------------------------------------------
-- Prob examples
-- ---------------------------------------------------------------------------

-- | Fair coin with total mass 1.
coin :: Prob (->) Double () Bool
coin = fromWeighted [(True, 0.25), (False, 0.75)]

-- ---------------------------------------------------------------------------
-- Pipeline
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  results <-
    sequence
      [ -- Markov-category oracles (Ex9): copy/discard naturality is morphism-level
        check "FinRel finRelId is deterministic" $
          deterministic (==) (==) finRelId,
        check "FinRel finRelZeroMap is deterministic" $
          deterministic (==) (==) finRelZeroMap,
        check "FinRel finRelTotal is discard-natural but not copy-natural" $
          discardNatural (==) finRelTotal && not (copyNatural (==) finRelTotal),
        check "FinRel finRelNeither is neither copy- nor discard-natural" $
          not (copyNatural (==) finRelNeither) && not (discardNatural (==) finRelNeither),
        -- Copy/discards naturality via finite separators
        check "Prob copy natural for embed (deterministic fragment, FG nesting)" $
          copyNaturalP probCopySep parFG (embed not :: Prob (->) Bool Bool Bool),
        check "Prob copy natural for embed (deterministic fragment, GF nesting)" $
          copyNaturalP probCopySep parGF (embed not :: Prob (->) Bool Bool Bool),
        check "Prob copy NOT natural for coin (correlation vs independence, FG)" $
          not (copyNaturalP probCopySepDouble parFG coin),
        check "Prob copy NOT natural for coin (correlation vs independence, GF)" $
          not (copyNaturalP probCopySepDouble parGF coin),
        check "Prob squareKBool is copy-natural with neither nesting" $
          not (copyNaturalP probCopySep parFG squareKBool)
            && not (copyNaturalP probCopySep parGF squareKBool),
        -- Discard on the mass-1 fragment
        check "Prob discard natural for coin (mass-1 fragment)" $
          discardNaturalP probDiscardSep coin,
        check "Prob discard fails for unnormalised score (*2) . coin" $
          not (discardNaturalP probDiscardSep (score (* 2) . coin))
      ]
  if and results
    then putStrLn "\nAll pipeline tests passed."
    else error "Some pipeline tests failed."
