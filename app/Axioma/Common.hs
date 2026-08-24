{-# LANGUAGE DataKinds #-}

-- | Shared helpers for the circuits axioma topic modules.
--
-- These are small process bodies and assertion utilities that are used by
-- more than one topic.  Topic-specific helpers live in their own module.
module Axioma.Common
  ( -- * IO assertions
    checkIO,

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

import Circuit.Category (id)
import Circuit.Process (Process (..), delay, register)
import Data.Tuple qualified as Tuple
import Data.Void (Void, absurd)
import GHC.TypeNats (KnownNat, natVal)
import Prelude hiding (curry, id, uncurry, (.))
import Prelude qualified as Pre

-- | 'check' for assertions that live in 'IO'.
checkIO :: String -> IO Bool -> IO Bool
checkIO name act = do
  ok <- act
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok

-- | Simple additive process for oracles.
sumP :: Process Int Int
sumP = Process id (+) id

-- | Pair braid for the (,) trace yanking oracle.
swapPairP :: Process (Int, Int) (Int, Int)
swapPairP = Process id (\_ x -> x) (\(a, b) -> (b, a))

-- | Either braid for the Either trace yanking oracle.
swapEitherP :: Process (Either Int Int) (Either Int Int)
swapEitherP = Process id (\_ x -> x) swapEither
  where
    swapEither (Left a) = Right a
    swapEither (Right b) = Left b

-- | EWMA body: stateless affine box with feedback.
ewmaBody :: Double -> Process (Double, Double) (Double, Double)
ewmaBody alpha =
  Process
    (\(x, prev) -> alpha * x + (1 - alpha) * prev)
    (\s (x, _) -> alpha * x + (1 - alpha) * s)
    (\s -> (s, s))

-- | Exponentially weighted moving average with initial feedback.
ewma :: Double -> Double -> Process Double Double
ewma alpha s0 = register s0 (ewmaBody alpha)

-- | Shared-medium body: adds the input to the shared state and echoes it.
sharedAddP :: Process (Int, Int) (Int, Int)
sharedAddP = Process (Pre.uncurry (+)) (\s (_, a) -> s + a) (\s -> (s, s))

-- | Shared-medium body: doubles the shared state and echoes the input.
sharedDoubleP :: Process (Int, Int) (Int, Int)
sharedDoubleP = Process (\(s, _) -> s * 2) (\s (_, _) -> s * 2) (\s -> (s, s))
