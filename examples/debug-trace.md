---
name: debug-trace
description: Pure tracing via feedback wires
tags: ['debug', 'history', 'trace']
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

## Explicit logging in the state wire

You can also accumulate a log as data inside the feedback wire of a terminating loop. The `Either` tensor distinguishes continuing (`Left`) from exiting (`Right`), so the final state can include the full history.

```haskell
import Circuit
import Control.Category ((.))
import Prelude hiding (id, (.))
```

A loop that counts and accumulates a log in its state wire:

```haskell
step :: Either (Int, [Int]) () -> Either (Int, [Int]) (Int, [Int])
step (Right ())         = Left (0, [])
step (Left (n, history))
  | n < 3               = Left (n + 1, n : history)
  | otherwise           = Right (n, n : history)

counter :: Trace Either (->) () (Int, [Int])
counter = Knot step

-- >>> run counter ()
-- (3,[3,2,1,0])
```

The tuple `(Int, [Int])` is the loop's state wire; the list is the accumulated history. It is ordinary data flowing through the wire.

To thread an extra label *alongside* a payload, use the `ambient` combinator with the `(,)` tensor. See `examples/ambient.md`.

## Relationship to Debug.Trace

`Debug.Trace.trace` punches a hole through purity so you can observe execution. It is pragmatic and has very low friction.

The feedback approach makes the observation *part of the structure* being computed. What you would have printed becomes data flowing through wires. This data can participate in further computation, be branched, or be the primary output of the circuit.

When the thing you want to "debug" is the history or accumulation across recursive steps, the lazy knot + `trace` (or direct `Knot`) often gives you exactly that observation — explicitly and compositionally.

## See also

- The powers example in the main `readme.md`; the Fibonacci snippet above
- `examples/while.md` for iteration patterns with the `Either` tensor
- `examples/knot-and-fix.md` for the underlying reason this structure appears
- `Circuit.Trace` for the two tensor disciplines and their different looping behaviours
