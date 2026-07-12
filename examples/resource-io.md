---
name: resource-io
description: Resource lifecycles as a Trace over Kleisli IO
tags: ['io', 'resources', 'either']
---
# Resource IO

Safe I/O and resource handling with `Trace Either (Kleisli IO)`.
The pattern: acquire, loop, release — all enforced by the feedback
channel.  Surface is `Arr` / `Knot` / `run` (normal-form Trace).

```haskell
-- $setup
-- >>> :set -XBlockArguments -XLambdaCase
-- >>> import Control.Arrow (Kleisli (..), runKleisli)
-- >>> import Circuit (Trace, run)
-- >>> import qualified Circuit.Trace as T
-- >>> import System.IO (Handle, IOMode (..), hClose, hGetLine, hIsEOF, openFile)
```

Qualify `T.Knot` in `cabal repl` (interpreted mode also loads
`Circuit.Mon`, which exports its own constructors).

---

## loopIO

A convenience wrapper that routes both initial input and feedback
through the same step function.  `Left = continue`, `Right = done`
— the Trace-native convention.

```haskell
loopIO :: (a -> IO (Either a b)) -> Trace Either (Kleisli IO) a b
loopIO step = T.Knot (Kleisli \case
  Right x -> step x
  Left  x -> step x)
```

No free-category `Lift` / `Compose` here — just `Knot` over a base
`Kleisli` body.  `run` folds it via `trace`.

---

## Tier 1 — simple loop

A numeric countdown with an IO effect.

```haskell
countdown :: Trace Either (Kleisli IO) Int ()
countdown = loopIO \n ->
  if n <= 0
  then pure (Right ())
  else do
    putStrLn $ "tick " <> show n
    pure (Left (n - 1))

-- >>> runKleisli (run countdown) 3
-- tick 3
-- tick 2
-- tick 1
```

---

## Tier 2 — interactive loop

Same structure, state is `String`, exit triggered by input.

```haskell
echo :: Trace Either (Kleisli IO) String ()
echo = loopIO \line ->
  if line `elem` ["quit", "exit", ":q"]
  then pure (Right ())
  else do
    putStrLn $ "echo: " <> line
    pure (Left "next>")

-- >>> runKleisli (run echo) "hello"
-- echo: hello
```

---

## Tier 3 — resource lifecycle

The canonical case.  The feedback channel carries an open `Handle`.
The `Right` exit path is the single place where `hClose` is called —
cleanup guaranteed without try/finally boilerplate.

```haskell
fileReader :: FilePath -> Trace Either (Kleisli IO) (Maybe Handle) ()
fileReader path = loopIO \case
  Nothing -> do                                  -- acquire
    h <- openFile path ReadMode
    pure (Left (Just h))
  Just h -> do                                   -- use + decide
    eof <- hIsEOF h
    if eof
      then hClose h >> pure (Right ())           -- release + exit
      else do
        line <- hGetLine h
        putStrLn line
        pure (Left (Just h))                     -- continue

-- >>> runKleisli (run (fileReader "examples/resource-io.md")) Nothing
```

The state machine:

```
  Nothing → openFile → Left (Just h) ──┐
                                       │
  ┌────────────────────────────────────┘
  │
  ▼
  Just h → hIsEOF? ─── yes → hClose h → Right ()
                │
                no → hGetLine → print → Left (Just h) ──┘
```

The handle lives on the feedback channel.  The only way to exit is
through the branch that calls `hClose`.  The type guarantees you cannot
reach `Right ()` without releasing the resource.

---

## Tier 4 — typed resource lifecycle with state

The `Maybe Handle` pattern makes the resource lifecycle explicit in the
type.  `Nothing` means not yet acquired; `Just h` means live.  The state
carries an accumulator so the circuit returns a value on exit and can be
bracketed with a meter.

```haskell
fileReaderState :: FilePath -> Trace Either (Kleisli IO) (Maybe Handle, [String]) [String]
fileReaderState path = loopIO \case
  (Nothing, _) -> do                               -- acquire
    h <- openFile path ReadMode
    pure (Left (Just h, []))
  (Just h, acc) -> do                              -- use + decide
    eof <- hIsEOF h
    if eof
      then hClose h >> pure (Right (reverse acc))  -- release + exit
      else do
        line <- hGetLine h
        pure (Left (Just h, line : acc))           -- continue

-- >>> runKleisli (run (fileReaderState "examples/resource-io.md")) (Nothing, [])
```

The state machine:

```
  (Nothing, _) → openFile → Left (Just h, []) ──┐
                                                 │
  ┌──────────────────────────────────────────────┘
  │
  ▼
  (Just h, acc) → hIsEOF? ─── yes → hClose h → Right (reverse acc)
            │
            no → hGetLine → Left (Just h, line:acc) ──┘
```

The `Maybe` wrapper prevents use-before-acquire at the type level.  The
accumulator turns the circuit into a producer of results, open for
post-composition — bracket with `meterIO`, transform the output, or
feed it into another circuit.

---

## pattern

| tier | state type | exit trigger | resource? |
|------|-----------|-------------|-----------|
| countdown | `Int` | `n <= 0` | none |
| echo | `String` | `"quit"` in input | none |
| file reader | `Maybe Handle` | EOF reached | yes |
| file reader (typed) | `(Maybe Handle, [String])` | EOF reached | yes, typed lifecycle + accumulator |

The guarantee: **the `Right` exit path is the single place where cleanup
happens**.  For file handles this means `hClose` is always called.  For
sockets, databases, or any other resource, the same structure applies:
acquire on first call, carry the resource through `Left` feedback,
release before returning `Right`.

The `Maybe Handle` variant strengthens this: `Nothing` is unacquired,
`Just h` is live.  The type prevents use-before-acquire.  The state
slot makes the circuit composable — bracket with `meterIO`, map the
output, or wire it downstream.

🚩 **Prompt finalization on exception** is an open question.  The
structural guarantee holds for normal exit through `Right`.  If an
async exception strikes the `Kleisli IO` body mid-iteration, the handle
may leak.  See `circuits-io` for Bluefin/effectful comparison and the
bracketing gap on effectful channel ends.

---

## mechanism

Under the hood, `loopIO` builds `T.Knot (Kleisli body)`.  `run` folds
via the `Traced Either (Kleisli IO)` instance using GHC's delimited
continuation primops (`prompt` / `control0`).  Constant stack usage —
the loop body is re-entered at the `prompt` boundary every iteration.
