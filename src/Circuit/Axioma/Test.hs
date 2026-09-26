{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Circuit.Axioma.Test
  ( check,
    approx,
    enumFunctions,
    enumCartesian,
    allBoolFns,
    pairBoolFns,
    pairDoubleFns,
  )
where

import Control.Monad (replicateM)
import Data.Maybe (fromMaybe)
import Prelude hiding (curry, id, uncurry, (.))

check :: String -> Bool -> IO Bool
check name ok = do
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok

approx :: Double -> Double -> Bool
approx x y = abs (x - y) < 1e-9

enumFunctions :: (Eq a) => [a] -> [b] -> [a -> b]
enumFunctions [] _ = []
enumFunctions _ [] = []
enumFunctions domain codomain@(defaultVal : _) =
  map
    (\vals x -> fromMaybe defaultVal (lookup x (zip domain vals)))
    (replicateM (length domain) codomain)

enumCartesian :: [a] -> [b] -> [(a, b)]
enumCartesian xs ys = [(x, y) | x <- xs, y <- ys]

allBoolFns :: forall a. (Bounded a, Enum a) => [a -> Bool]
allBoolFns = map (\bits a -> bits !! fromEnum a) (replicateM (fromEnum (maxBound :: a) + 1) [False, True])

pairBoolFns :: forall b. (Enum b) => [b] -> [(b, b) -> Bool]
pairBoolFns bs = map (\bits (b1, b2) -> bits !! (fromEnum b1 * n + fromEnum b2)) (replicateM (n * n) [False, True])
  where
    n = length bs

pairDoubleFns :: (Enum b) => [b] -> [(b, b) -> Double]
pairDoubleFns bs = map (\k p -> if k p then 1 else 0) (pairBoolFns bs)
