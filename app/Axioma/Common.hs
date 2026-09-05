{-# LANGUAGE DataKinds #-}

-- | Shared helpers for the circuits axioma topic modules.
--
-- These are small process bodies and assertion utilities that are used by
-- more than one topic.  Topic-specific helpers live in their own module.
module Axioma.Common
  ( -- * Verbosity
    Verbosity (..),
    checkV,
    checkIOV,

    -- * Simple additive processes
    sumP,
    swapPairP,
    swapEitherP,

    -- * EWMA process
    ewmaBody,
    ewma,

    -- * Shared-medium process bodies
    sharedAddP,
    sharedDoubleP,
  )
where

import Circuit.Axioma.Test (check)
import Circuit.Category (id)
import Circuit.Process (Mealy (..), delay, register)
import Data.Tuple qualified as Tuple
import GHC.TypeNats (KnownNat, natVal)
import Prelude hiding (curry, id, uncurry, (.))
import Prelude qualified as Pre

-- | Output granularity for the axioma runner.
data Verbosity
  = -- | One symbol for the whole run.
    Package
  | -- | One symbol per topic.
    Topic
  | -- | One symbol per axiom (the default).
    Axioms
  deriving (Show, Eq)

-- | Print a PASS/FAIL line only when verbosity is 'Axioms'.
checkV :: Verbosity -> String -> Bool -> IO Bool
checkV Axioms name ok = check name ok
checkV _ _ ok = pure ok

-- | Print a PASS/FAIL line for an IO assertion only when verbosity is 'Axioms'.
checkIOV :: Verbosity -> String -> IO Bool -> IO Bool
checkIOV Axioms name act = do
  ok <- act
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok
checkIOV _ _ act = act

-- | Simple additive process for oracles.
sumP :: Mealy Int Int
sumP = Mealy id (+) id

-- | Pair braid for the (,) trace yanking oracle.
swapPairP :: Mealy (Int, Int) (Int, Int)
swapPairP = Mealy id (\_ x -> x) (\(a, b) -> (b, a))

-- | Either braid for the Either trace yanking oracle.
swapEitherP :: Mealy (Either Int Int) (Either Int Int)
swapEitherP = Mealy id (\_ x -> x) swapEither
  where
    swapEither (Left a) = Right a
    swapEither (Right b) = Left b

-- | EWMA body: stateless affine box with feedback.
ewmaBody :: Double -> Mealy (Double, Double) (Double, Double)
ewmaBody alpha =
  Mealy
    (\(x, prev) -> alpha * x + (1 - alpha) * prev)
    (\s (x, _) -> alpha * x + (1 - alpha) * s)
    (\s -> (s, s))

-- | Exponentially weighted moving average with initial feedback.
ewma :: Double -> Double -> Mealy Double Double
ewma alpha s0 = register s0 (ewmaBody alpha)

-- | Shared-medium body: adds the input to the shared state and echoes it.
sharedAddP :: Mealy (Int, Int) (Int, Int)
sharedAddP = Mealy (Pre.uncurry (+)) (\s (_, a) -> s + a) (\s -> (s, s))

-- | Shared-medium body: doubles the shared state and echoes the input.
sharedDoubleP :: Mealy (Int, Int) (Int, Int)
sharedDoubleP = Mealy (\(s, _) -> s * 2) (\s (_, _) -> s * 2) (\s -> (s, s))
