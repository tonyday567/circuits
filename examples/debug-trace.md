---
title: "Pure tracing via feedback wires"
category: state
status: stable
tags: ["debug", "history"]
---

# Pure tracing via feedback wires

`Debug.Trace.trace` is the standard way to observe intermediate values while debugging. It is convenient precisely because it lets you reach inside a computation from the outside.

This library offers a different tool for a similar desire: making the history of a computation *explicit* and available as ordinary data.

## The feedback wire carries history

Consider the Fibonacci example using the library's `trace` operator (the traced monoidal one, not `Debug.Trace`):

```haskell
-- $setup
-- >>> import Circuit
-- >>> import Prelude hiding (id, (.))
-- >>> import Control.Category ((.))
```

```haskell
-- >>> take 5 (trace (\(fibs, ()) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs)) () :: [Integer])
-- [0,1,1,2,3]
```

The variable `fibs` in the feedback position *is* the trace of previous results. Because of the lazy knot, each step can see everything that has been computed so far. The entire history is just a normal value being threaded through the wire.

This is tracing, but the trace is first-class data rather than a side effect.

## Explicit logging with ambient state

You can thread a log alongside a computation or loop without the main logic having to mention it, using `ambient`.

```haskell
{-# LANGUAGE BlockArguments #-}

import Circuit
import Control.Category (id, (.))
import Prelude hiding (id, (.))
```

A loop that counts and accumulates a log in the state wire:

```haskell
step :: (Int, [Int]) -> Either (Int, [Int]) (Int, [Int])
step (n, log) =
  if n < 3
    then Left  (n + 1, n : log)
    else Right (n,     n : log)

counter :: Trace Either (->) () (Int, [Int])
counter = Knot step
```

Thread an extra label through the loop using `ambient`:

```haskell
braidE (Left (s, a))  = (s, Left a)
braidE (Right (s, c)) = (s, Right c)

-- >>> run (ambientBy braidE counter) ("run-1", ())
-- ("run-1",(3,[2,1,0]))
```

The label rides along "ambiently". The log is ordinary data in the state wire.

## Relationship to Debug.Trace

## Relationship to Debug.Trace

`Debug.Trace.trace` punches a hole through purity so you can observe execution. It is pragmatic and has very low friction.

The feedback approach makes the observation *part of the structure* being computed. What you would have printed becomes data flowing through wires. This data can participate in further computation, be branched, or be the primary output of the circuit.

When the thing you want to "debug" is the history or accumulation across recursive steps, the lazy knot + `trace` (or direct `Knot`) often gives you exactly that observation — explicitly and compositionally.

## See also

- The Fibonacci and powers examples in the main `readme.md`
- `examples/while.md` for iteration patterns with the `Either` tensor
- `examples/knot-recovers-fix.md` for the underlying reason this structure appears
- `Circuit.Trace` for the two tensor disciplines and their different looping behaviours
