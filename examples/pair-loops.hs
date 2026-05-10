{-# LANGUAGE LambdaCase #-}
module PairLoops where

import Circuit.Circuit (Circuit(..), reify)

-- qList [1,2,3,4,5] + takeE 2 → first 2 elements
-- Feedback hidden inside Knot: ([Int], Int, [Int])
paired :: Circuit (->) Either () (Maybe [Int])
paired = Knot body
  where
    body (Right ()) = emit ([1,2,3,4,5], 2, [])
    body (Left (xs, k, acc)) = emit (xs, k, acc)
    emit ([], _, acc)     = Right (Just (reverse acc))
    emit (_,  0, acc)     = Right (Just (reverse acc))
    emit (x:xs', k, acc)  = Left (xs', k-1, x:acc)

demo :: IO ()
demo = do
  print $ reify paired ()
