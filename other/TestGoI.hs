{-# LANGUAGE MagicHash #-}
module Main where

import GoIRTS

main :: IO ()
main = do
  result <- simpleTest
  putStrLn $ "Test result: " ++ show result
