{-# LANGUAGE LambdaCase #-}
module HyperStream where

import Circuit.Hyper (Hyper(..))

-- qList: each invoke returns (remaining, current)
qList :: [Int] -> Hyper () (Maybe ([Int], Int))
qList xs = Hyper $ \_ -> case xs of
  []     -> Nothing
  (x:xs') -> Just (xs', x)

-- Step a producer, collecting elements
collect :: Hyper () (Maybe ([Int], Int)) -> [Int]
collect h = case invoke h undefined of
  Nothing     -> []
  Just (xs', x) -> x : collect (qList xs')

-- takeE as a consumer: given a producer, take n elements
takeE :: Int -> Hyper () (Maybe ([Int], Int)) -> [Int]
takeE 0 _ = []
takeE n p = case invoke p undefined of
  Nothing     -> []
  Just (xs', x) -> x : takeE (n-1) (qList xs')

demo :: IO ()
demo = do
  putStrLn "=== collect ==="
  print $ collect (qList [1,2,3])
  putStrLn "=== takeE 2 ==="
  print $ takeE 2 (qList [1,2,3,4,5])
