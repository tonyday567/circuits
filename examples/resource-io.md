# Resource IO

Safe I/O and resource handling with `Circuit (Kleisli IO) Either`.
The pattern: acquire, loop, release — all enforced by the feedback
channel.

```haskell
-- $setup
-- >>> import Control.Arrow (Kleisli (..), runKleisli)
-- >>> import Circuit
-- >>> import Prelude hiding (id, (.))
```

---

## loopIO

A convenience wrapper that routes both initial input and feedback
through the same step function.  `Left = continue`, `Right = done`
— the Trace-native convention.

```haskell
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

loopIO :: (a -> IO (Either a b)) -> Circuit (Kleisli IO) Either a b
loopIO step = Knot (Kleisli \case
  Right x -> step x
  Left  x -> step x)
```

---

## Tier 1 — simple loop

A numeric countdown with an IO effect.

```haskell
countdown :: Circuit (Kleisli IO) Either Int ()
countdown = loopIO \n ->
  if n <= 0
  then pure (Right ())
  else do
    putStrLn $ "tick " <> show n
    pure (Left (n - 1))

-- >>> runKleisli (reify countdown) 3
-- tick 3
-- tick 2
-- tick 1
```

---

## Tier 2 — interactive loop

Same structure, state is `String`, exit triggered by input.

```haskell
echo :: Circuit (Kleisli IO) Either String ()
echo = loopIO \line ->
  if line `elem` ["quit", "exit", ":q"]
  then pure (Right ())
  else do
    putStrLn $ "echo: " <> line
    pure (Left "next>")

-- >>> runKleisli (reify echo) "hello"
-- echo: hello
```

---

## Tier 3 — resource lifecycle

The canonical case.  The feedback channel carries an open `Handle`.
The `Right` exit path is the single place where `hClose` is called —
cleanup guaranteed without try/finally boilerplate.

```haskell
import System.IO (Handle, IOMode (..), hClose, hGetLine, hIsEOF, openFile)

fileReader :: FilePath -> Circuit (Kleisli IO) Either Handle ()
fileReader path = loopIO \case
  () -> do                                       -- acquire
    h <- openFile path ReadMode
    pure (Left h)
  h -> do                                        -- use + decide
    eof <- hIsEOF h
    if eof
      then hClose h >> pure (Right ())           -- release + exit
      else do
        line <- hGetLine h
        putStrLn line
        pure (Left h)                            -- continue

-- >>> runKleisli (reify (fileReader "examples/resource-io.md")) ()
```

The state machine:

```
  () → openFile → Left h ──┐
                            │
  ┌─────────────────────────┘
  │
  ▼
  h → hIsEOF? ─── yes → hClose h → Right ()
         │
         no → hGetLine → print → Left h ──┘
```

The handle lives on the feedback channel.  The only way to exit is
through the branch that calls `hClose`.  The type guarantees you cannot
reach `Right ()` without releasing the resource.

---

## pattern

| tier | state type | exit trigger | resource? |
|------|-----------|-------------|-----------|
| countdown | `Int` | `n <= 0` | none |
| echo | `String` | `"quit"` in input | none |
| file reader | `Handle` | EOF reached | yes |

The guarantee: **the `Right` exit path is the single place where cleanup
happens**.  For file handles this means `hClose` is always called.  For
sockets, databases, or any other resource, the same structure applies:
acquire on first call, carry the resource through `Left` feedback,
release before returning `Right`.

---

## mechanism

Under the hood, `loopIO` creates a `Knot (Kleisli body)` executed by
the `Trace (Kleisli IO) Either` instance using GHC's delimited
continuation primops (`prompt` / `control0`).  Constant stack usage —
the loop body is re-entered at the `prompt` boundary every iteration.
