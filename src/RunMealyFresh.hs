{-# LANGUAGE RankNTypes #-}

-- | Fresh interpreter: Traced Mealy -> Mealy
-- No MealyM anywhere. Pure Mealy only.

module RunMealyFresh
  ( runMealy
  ) where

import Prelude hiding (id)
import qualified Prelude

import Data.Mealy (Mealy (..))
import Traced (Traced (..))

-- | Interpret Traced Mealy as Mealy
runMealy :: Traced Mealy a b -> Mealy a b

runMealy Pure = Mealy Prelude.id (\_ a -> a) Prelude.id

runMealy (Lift m) = m

runMealy (Compose g h) = undefined

runMealy (Loop p) = undefined
