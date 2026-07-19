---
name: two-files
description: Two independent file opens; par; swap; unitors; Trace () ()
tags: ['ends', 'io', 'par']
---

# two files

Swap two files as one program:

```haskell
Trace (,) (Kleisli IO) () ()
```

Independence is **`par`**. Wiring is **`emit` / `commit`**. Unit is **`open ()`** + **unitors**.

---

## program

```haskell
unitl'
  >>> par (emit outA inU1) (emit outB inU2)   -- independent reads
  >>> swap
  >>> par (commit inA outU1) (commit inB outU2) -- cross writes
  >>> unitl
```

Two **`openFileEnds`**, two **`open ()`**. Not a sequential copy.

---

## implementation

```haskell
{-# LANGUAGE OverloadedStrings #-}

import Circuit
import Circuit.Classes ((>>>))
import Control.Arrow (Kleisli (..), runKleisli)
import System.IO (IOMode (..), hClose, hGetContents, openFile)

-- Strict read: lazy handle + later writeFile deadlocks.
readFileStrict :: FilePath -> IO String
readFileStrict path = do
  h <- openFile path ReadMode
  s <- hGetContents h
  length s `seq` hClose h
  pure s

-- Extrinsic free ends for one file path.
-- Out reads the whole file; In writes the whole file then continues.
openFileEnds :: FilePath -> IO (Out (,) (Kleisli IO) String, In (,) (Kleisli IO) String)
openFileEnds path = pure (outH, inH)
  where
    outH = Out $ \_ -> Arr (Kleisli $ \_ -> readFileStrict path)
    inH =
      In $ \o ->
        Arr
          ( Kleisli $ \bs -> do
              writeFile path bs
              runKleisli (run (emit o inH)) bs
          )

-- Swap contents of two files as one monoidal program.
exchangeFiles :: FilePath -> FilePath -> IO (Trace (,) (Kleisli IO) () ())
exchangeFiles pathA pathB = do
  (outA, inA) <- openFileEnds pathA
  (outB, inB) <- openFileEnds pathB
  let endsU1 = open
      endsU2 = open
      intro  = unitl' :: Trace (,) (Kleisli IO) () ((), ())
      harvest = par (emit outA (conjoint endsU1)) (emit outB (conjoint endsU2))
      feed    = par (commit inA (companion endsU1)) (commit inB (companion endsU2))
      elim    = unitl :: Trace (,) (Kleisli IO) ((), ()) ()
  pure $ intro >>> harvest >>> swap >>> feed >>> elim

-- Open, build, run once.
runExchange :: FilePath -> FilePath -> IO ()
runExchange pathA pathB = do
  prog <- exchangeFiles pathA pathB
  runKleisli (run prog) ()
```

Also: `Tensor` / `Action` for `(,) (Kleisli m)` so `par` works on effectful Trace.

---

## check

```text
a="alpha" b="beta"  →  runExchange  →  a="beta" b="alpha"
```
