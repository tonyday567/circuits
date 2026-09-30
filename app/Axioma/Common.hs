{-# LANGUAGE DataKinds #-}

module Axioma.Common
  ( Verbosity (..),
    checkV,
    checkIOV,
    sumP,
    swapPairP,
    swapEitherP,
    ewmaBody,
    ewma,
    sharedAddP,
    sharedDoubleP,
  )
where

import Circuit.Axioma.Test (check)
import Circuit.Category (id)
import Circuit.GMachine (Moore, moore, register)
import Prelude hiding (curry, id, uncurry, (.))
import Prelude qualified as Pre

data Verbosity
  = Package
  | Topic
  | Axioms
  deriving (Show, Eq)

checkV :: Verbosity -> String -> Bool -> IO Bool
checkV Axioms name ok = check name ok
checkV _ _ ok = pure ok

checkIOV :: Verbosity -> String -> IO Bool -> IO Bool
checkIOV Axioms name act = do
  ok <- act
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok
checkIOV _ _ act = act

sumP :: Moore Int Int
sumP = moore id (+) id

swapPairP :: Moore (Int, Int) (Int, Int)
swapPairP = moore id (\_ x -> x) (\(a, b) -> (b, a))

swapEitherP :: Moore (Either Int Int) (Either Int Int)
swapEitherP = moore id (\_ x -> x) swapEither
  where
    swapEither (Left a) = Right a
    swapEither (Right b) = Left b

ewmaBody :: Double -> Moore (Double, Double) (Double, Double)
ewmaBody alpha =
  moore
    (\(x, prev) -> alpha * x + (1 - alpha) * prev)
    (\s (x, _) -> alpha * x + (1 - alpha) * s)
    (\s -> (s, s))

ewma :: Double -> Double -> Moore Double Double
ewma alpha s0 = register s0 (ewmaBody alpha)

sharedAddP :: Moore (Int, Int) (Int, Int)
sharedAddP = moore (Pre.uncurry (+)) (\s (_, a) -> s + a) (\s -> (s, s))

sharedDoubleP :: Moore (Int, Int) (Int, Int)
sharedDoubleP = moore (\(s, _) -> s * 2) (\s (_, _) -> s * 2) (\s -> (s, s))
