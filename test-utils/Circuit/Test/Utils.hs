{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Shared oracle helpers for the @circuits-axioma*@ executables.
--
-- This internal library holds test machinery that is useful across multiple
-- executables: assertion printers, finite enumeration, and separator oracles
-- for 'Prob'.  Nothing here is part of the public library API.
module Circuit.Test.Utils
  ( -- * Assertions
    check,
    approx,

    -- * Finite enumeration
    enumFunctions,
    enumCartesian,
    allBoolFns,
    pairBoolFns,
    pairDoubleFns,

    -- * Prob separator oracles
    probEqOver,
    probEqDoubleOver,
    probCopySep,
    probCopySepDouble,
    probDiscardSep,
  )
where

import Circuit.Prob (Prob (..))
import Control.Monad (replicateM)
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat, natVal)
import Prelude hiding (curry, id, uncurry, (.))

-- | Print PASS/FAIL for a named boolean assertion and return the result.
check :: String -> Bool -> IO Bool
check name ok = do
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok

-- | Approximate equality for floating-point oracles.
approx :: Double -> Double -> Bool
approx x y = abs (x - y) < 1e-9

-- | Enumerate all functions from a finite domain to a finite codomain.
enumFunctions :: (Eq a) => [a] -> [b] -> [a -> b]
enumFunctions [] _ = [const (error "enumFunctions: empty domain")]
enumFunctions domain codomain = map (listToFunction domain) (sequenceA (replicate (length domain) codomain))
  where
    listToFunction dom vals x = fromMaybe (error "listToFunction: input not in domain") (lookup x (zip dom vals))

-- | Cartesian product of two lists.
enumCartesian :: [a] -> [b] -> [(a, b)]
enumCartesian xs ys = [(x, y) | x <- xs, y <- ys]

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

-- | Boolean-valued pair functions rendered as {0,1}-valued 'Double' functions.
pairDoubleFns :: (Enum b) => [b] -> [(b, b) -> Double]
pairDoubleFns bs = map (\k p -> if k p then 1 else 0) (pairBoolFns bs)

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
