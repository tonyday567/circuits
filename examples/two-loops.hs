{-# LANGUAGE LambdaCase #-}
module TwoLoops where

import Circuit.Circuit (Circuit(..), reify)

-- qList: walk list, emit one element at a time
qList :: [Int] -> Circuit (->) Either () (Maybe Int)
qList xs = Loop $ \case
  Right () -> case xs of
    []     -> Right Nothing
    (x:xs') -> Left (xs', Just x)
  Left (xs', _) -> case xs' of
    []     -> Right Nothing
    (y:ys) -> Left (ys, Just y)

-- takeE: count down, pass through, stop at 0
takeE :: Int -> Circuit (->) Either (Maybe Int) (Maybe Int)
takeE n = Loop $ \case
  Right mx -> if n <= 0 then Right Nothing else Left (n, mx)
  Left (k, _) -> if k <= 0 then Right Nothing else Left (k-1, Nothing)

-- Fused: both in one loop
fused :: Int -> [Int] -> Circuit (->) Either () (Maybe [Int])
fused n xs = Loop $ \case
  Right () -> collect xs n []
  Left (xs', k, acc) -> collect xs' k acc
  where
    collect [] _ acc     = Right (Just (reverse acc))
    collect _  0  acc    = Right (Just (reverse acc))
    collect (x:xs') k acc = Left (xs', k-1, x:acc)

demo :: IO ()
demo = do
  putStrLn "=== separate (reify each) ==="
  print $ reify (qList [1,2,3]) ()
  print $ reify (takeE 2) (Just 5)

  putStrLn "=== fused ==="
  print $ reify (fused 3 [1,2,3,4,5]) ()
