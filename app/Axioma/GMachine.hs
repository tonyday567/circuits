-- | GMachine oracles.
module Axioma.GMachine
  ( gMachineTopic,
  )
where

import Axioma.Common (Verbosity (..))
import Control.Monad (when)

-- The check list is intentionally empty until the first GMachine laws land.
gMachineTopic :: Verbosity -> IO [Bool]
gMachineTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "GMachine oracles"
  sequence []
