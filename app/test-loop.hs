{-# LANGUAGE OverloadedStrings #-}

-- Minimal reproducer for lazy knot deadlock
-- Tests runMealyBS directly without compiledMarkupLexer

import qualified Data.ByteString as B
import Lexer (runMarkupMealyBS)

main :: IO ()
main = do
  let input = "<test>"
  putStrLn "Testing runMarkupMealyBS with minimal input..."
  let result = runMarkupMealyBS (B.pack $ map fromEnum input)
  putStrLn $ "Result: " ++ show (length result) ++ " tokens"
  putStrLn "Success!"
