# repl-pure ⟜ a pure REPL as Circuit

Three ways to build a `Circuit (->) Either String String`:
lift a pure function, loop with `Knot`, and compose two loops.
No IO, no queues — just the three constructors in action.

Paste each block into `cabal repl`.

## setup

```haskell
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Circuit.Circuit (Circuit(..), reify)
import Prelude hiding (id, (.))

type Repl = Circuit (->) Either String String
```

## Lift — a single-step function

```haskell
-- | One step, no loop. Input goes in, output comes out.
trivial :: Repl
trivial = Lift $ \case
  "quit" -> "bye!"
  s      -> "echo: " <> s

-- >>> reify trivial "hello"
-- Right "echo: hello"
-- >>> reify trivial "quit"
-- Right "bye!"
```

## Knot — one internal iteration

`Right cmd` = external input. `Left resp` = fed-back internal state.

```haskell
oneShot :: Repl
oneShot = Knot $ \case
  Right cmd ->
    if cmd == "quit"
    then Right "bye!"
    else Left ("echo: " <> cmd)
  Left resp -> Right resp

-- >>> reify oneShot "hello"
-- Right "echo: hello"
-- >>> reify oneShot "quit"
-- Right "bye!"
```

## Knot with accumulated history

The feedback type `[String]` is hidden — the `Repl` signature only shows
`String`. The Knot hides its internal state.

```haskell
historyRepl :: Repl
historyRepl = Knot (body :: Either [String] String -> Either [String] String)
  where
    body = \case
      Right cmd
        | cmd == ":quit"   -> Right "bye!"
        | cmd == ":history" -> Left [cmd]
        | otherwise         -> Left [cmd]
      Left hist -> Right (show (length hist) <> " commands")

-- >>> reify historyRepl "hello"
-- Right "1 commands"
-- >>> reify historyRepl ":quit"
-- Right "bye!"
```

## Compose — chain two Repls

Output of the first becomes input of the second.

```haskell
compose2 :: Repl -> Repl -> Repl
compose2 = Compose

-- echo then echo again
-- >>> reify (compose2 oneShot oneShot) "hello"
-- Right "echo: echo: hello"
```

## the full API, in one place

| constructor | meaning |
|-------------|---------|
| `Lift f`    | embed a function |
| `Knot f`    | feedback loop (Left=continue, Right=stop) |
| `Compose f g` | sequential composition |
| `reify`      | run a Circuit, collapsing Knots |

## reference

- `Circuit.Circuit` — the GADT module
- `other/03-circuit.md` — free traced monoidal category
- `examples/while.md` — while loop: Hyper vs Circuit
