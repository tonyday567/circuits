{-# LANGUAGE RankNTypes #-}

-- | Fresh interpreter: Traced Mealy -> Mealy
-- No MealyM anywhere. Pure Mealy only.

module RunMealyFresh
  ( runMealy
  ) where

import Data.Mealy (Mealy (..))
import Traced (Traced (..))

-- | Interpret Traced Mealy as Mealy
runMealy :: Traced Mealy a b -> Mealy a b

runMealy Pure = undefined

runMealy (Lift m) = undefined

runMealy (Compose g h) = undefined

runMealy (Loop p) = undefined
