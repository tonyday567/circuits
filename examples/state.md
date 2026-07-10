---
name: state
description: Visible, ambient, and hidden state in circuits
tags: ['state', 'ambient', 'hidden-state']
---
# State in Circuits

Circuits offer three mechanisms for managing state, corresponding to three
different relationships between the state and the computation.

```haskell
import Circuit (Trace, run, ambient)
import qualified Circuit.Trace as T
import Control.Category ((>>>))
```

(`T.Arr` and `T.Knot` are qualified because `cabal repl circuits` also loads
`Circuit.Mon`, which exports its own `Arr` constructor.)

## 1. Visible state — threaded by composition

The state appears explicitly in the type. Composition threads it through.

```haskell
-- StateC s a b = Trace (,) (->) (s, a) (s, b)
-- This is the state monad in arrow form.

push :: Trace (,) (->) ([a], a) ([a], ())
push = T.Arr $ \(buf, a) -> (buf ++ [a], ())

pop :: Trace (,) (->) ([a], ()) ([a], a)
pop = T.Arr $ \(buf, ()) -> case buf of
  x : xs -> (xs, x)
  []     -> (buf, error "Queue.pop: empty buffer")

-- Composition threads state
queue :: Trace (,) (->) ([a], a) ([a], a)
queue = push >>> pop
```

State is **visible**, **mutable**, and **persistent across composition**.
You can inspect it, meter it, branch on it. Composition merges state
wires automatically.

This is the everyday mechanism. It corresponds to `StateT s m a` in
monadic code — but in arrow form, the state is the first component of
the `(,)` tensor.

Trade: the state type appears in the interface. Callers see `[a]`.

## 2. Ambient state — threaded by `ambient`

State rides alongside the computation, invisible to the circuit itself.

```haskell
-- A circuit that operates on the payload only
increment :: Trace (,) (->) Int Int
increment = T.Arr (+1)

-- Thread a log through ambiently
metered :: Trace (,) (->) ([String], Int) ([String], Int)
metered = ambient increment
-- run metered (["start"], 5) = (["start"], 6)
```

The ambient state `s` passes through **unchanged**. The circuit can't
read or write it. This is for metering, logging, carrying context that
the computation shouldn't touch.

The `meteredAmbient` combinator in `circuits-meter` extends this: the
circuit CAN read and write the state, using it as an accumulator.

```haskell
-- In circuits-meter this looks roughly like:
-- meteredAmbient :: (s -> t -> s) -> Meter s t -> Kleisli IO a b
--                -> Trace (,) (Kleisli IO) (s, a) (s, b)
```

Trade: state is threaded automatically, but the circuit is unaware
of it (unless using `meteredAmbient`).

## 3. Hidden state — threaded by `Knot`

State is the feedback channel of a trace, invisible in the visible
interface. Two sub-mechanisms:

### 3a. `(,)` trace — lazy knot (coinductive)

```
trace f b = let (a, c) = f (a, b) in c
```

The feedback value `a` is recursively bound. The body executes once with
a self-referential channel.

```haskell
-- powers = [1, 2, 4, 8, 16, ...] via lazy knot
powers :: Trace (,) (->) () [Integer]
powers = T.Knot $ \(ns, ()) -> (1 : map (*2) ns, take 5 ns)
```

Constraint: the feedback channel must be **lazy** — you can reference
it without forcing. Pattern-matching on the channel diverges (black hole).
Write-only for the feedback direction.

### 3b. `Either` trace — iteration (inductive)

```
trace f b = go (Right b)
  where go x = case f x of Right c -> c; Left a -> go (Left a)
```

`Left a` continues with updated state, `Right c` exits with result.

```haskell
fac :: Trace Either (->) (Int, Int) Int  -- input: (n, acc)
fac = T.Knot $ either step step
  where step (n, acc) | n <= 1    = Right acc
                      | otherwise = Left (n - 1, n * acc)
```

Constraint: each `run` call starts a fresh trace. State doesn't
persist across calls. You get one iteration's worth of mutation per
invocation.

## Decision table

| Need | Mechanism |
|------|-----------|
| State modified by computation, persists across composition | Visible state (composition, e.g. `(.)`/`(>>>)`) |
| Read-only context (logging, metrics) | Ambient state (`ambient`) |
| Accumulator updated by computation (metering) | `meteredAmbient` |
| Self-referential lazy structure (powers, fibs) | `Knot` + `(,)` trace |
| Iterative computation with exit condition (fac) | `Knot` + `Either` trace |
| Persistent mutable state across operations | Visible state — there is no hidden persistent mutable state in pure circuits |

## No `StateT`

Circuits don't need a separate `StateT` because `Trace (,) (->) (s, a) (s, b)`
already IS the state monad in arrow form. Composition binds. The `(,)` tensor
carries the state. There's nothing to add.
