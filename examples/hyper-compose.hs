{-# LANGUAGE LambdaCase #-}
module HyperCompose where

import Circuit.Circuit (Circuit(..), toHyper, reify)
import Circuit.Hyper (lower)
import Control.Category ((.))
import Prelude hiding ((.), id)

-- qList via Either — walk list one element at a time
qList :: [Int] -> Circuit (->) Either () (Maybe Int)
qList xs = Knot $ \case
  Right () -> case xs of
    []     -> Right Nothing
    (x:xs') -> Left (xs', Just x)
  Left (xs', _) -> case xs' of
    []     -> Right Nothing
    (y:ys) -> Left (ys, Just y)

-- takeE via Either
takeE :: Int -> Circuit (->) Either (Maybe Int) (Maybe Int)  
takeE n = Knot $ \case
  Right mx -> Left (n, mx)
  Left (k, mx) -> if k <= 0 then Right Nothing else Left (k-1, mx)

demo :: IO ()
demo = do
  putStrLn "=== reify (no composition) ==="
  print $ reify (qList [1,2,3]) ()
  print $ reify (takeE 2) (Just 5)

  putStrLn "=== toHyper compose ==="
  let pipeline = toHyper (takeE 2) . toHyper (qList [1,2,3])
  print $ lower pipeline ()
