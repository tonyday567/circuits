{-# LANGUAGE LambdaCase #-}
module HyperLoop where

import Circuit.Hyper (Hyper(..))

-- Stepwise loop: each invoke = one iteration. State in closures.
stepLoop :: (Either a b -> Either a c) -> a -> Hyper b c
stepLoop f a = Hyper $ \k ->
  let b = invoke k (stepLoop f a)
  in case f (Right b) of
       Right c -> c
       Left a' -> invoke (stepLoop f a') k

-- Countdown: emit decrementing count, stop at 0
countdown :: Int -> Hyper () (Maybe Int)
countdown n = stepLoop body n
  where
    body (Right ()) = if n <= 0 then Right Nothing else Left (n-1)
    body (Left k)   = if k <= 0 then Right (Just k) else Left (k-1)

demo :: IO ()
demo = do
  let dummyK :: Hyper (Maybe Int) ()
      dummyK = Hyper $ \_ -> ()
  let h = countdown 3
  print $ invoke h dummyK
