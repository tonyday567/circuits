{-# LANGUAGE BlockArguments #-}
module Main where
import GoIRTS

main :: IO ()
main = do
  putStrLn "=== callCC ==="
  exampleCallCC
  putStrLn ""
  putStrLn "=== multi-shot ==="
  exampleMultiShot
  putStrLn ""
  putStrLn "=== throw ==="
  exampleThrow
  putStrLn ""
  putStrLn "=== principal cut ==="
  examplePrincipalCut
