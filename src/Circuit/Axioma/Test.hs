{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Shared oracle helpers for the @circuits-axioma*@ executables.
--
-- These are small assertion printers, finite enumeration helpers, and
-- truth-table utilities used by the verification topics.  They live in the
-- @circuits@ library because every axioma executable already depends on
-- @circuits@; they are not part of the public circuit-building API.
module Circuit.Axioma.Test
  ( -- * Assertions
    check,
    approx,

    -- * Finite enumeration
    enumFunctions,
    enumCartesian,
    allBoolFns,
    pairBoolFns,
    pairDoubleFns,
  )
where

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
enumFunctions domain codomain = map (listToFunction domain) (replicateM (length domain) codomain)
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
