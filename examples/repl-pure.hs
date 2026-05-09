{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Lock-step REPL as Circuit (->) Either String String.
--   Pure, no IO, no queues.

module ReplPure where

import Circuit.Circuit (Circuit(..), reify)
import Prelude hiding (id, (.))

type Repl = Circuit (->) Either String String

-- Simplest: just lift a pure function. One step, no loop.
trivial :: Repl
trivial = Lift $ \case
  "quit" -> "bye!"
  s      -> "echo: " <> s

-- Loop with one internal iteration (feedback a = String).
--   Right cmd = external input
--   Left resp = fed-back internal state
oneShot :: Repl
oneShot = Loop $ \case
  Right cmd ->
    if cmd == "quit"
    then Right "bye!"
    else Left ("echo: " <> cmd)
  Left resp -> Right resp

-- Loop with accumulated history (feedback a = [String]).
-- The internal state type [String] isn't visible in the Repl signature.
historyRepl :: Repl
historyRepl = Loop (body :: Either [String] String -> Either [String] String)
  where
    body = \case
      Right cmd
        | cmd == ":quit"   -> Right "bye!"
        | cmd == ":history" -> Left [cmd]
        | otherwise         -> Left [cmd]
      Left hist -> Right (show (length hist) <> " commands")

-- Composition: two Repl steps chained.
-- Output of first becomes input of second.
compose2 :: Repl -> Repl -> Repl
compose2 = Compose

demo :: IO ()
demo = do
  putStrLn "=== trivial ==="
  print $ reify trivial "hello"
  print $ reify trivial "quit"

  putStrLn "=== oneShot ==="
  print $ reify oneShot "hello"
  print $ reify oneShot "quit"

  putStrLn "=== historyRepl ==="
  print $ reify historyRepl ":history"
  print $ reify historyRepl "any"

  putStrLn "=== composition: two oneShots ==="
  print $ reify (compose2 oneShot oneShot) "hello"
