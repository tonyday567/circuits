---
name: ambient
description: Threading a state wire through a Trace
tags: ['ambient', 'state-threading']
---
# Ambient State

> Threading a state wire through a `Trace`.

## The Idea

`ambient` slides a state component past a circuit unchanged. The circuit
operates on the payload; the state rides alongside via the tensor —
ambient, unnoticed.

```haskell
import Circuit
import Data.Profunctor (Profunctor, dimap)
import qualified Circuit.Trace as T

ambientBy :: (Profunctor arr, T.Traced t arr)
          => (forall x y z. t x (t y z) -> t y (t x z))
          -> T.Trace t arr a b
          -> T.Trace t arr (t s a) (t s b)
```

The braid argument swaps the state wire past the feedback channel:
`\(x, (s, a)) -> (s, (x, a))` for `(,)`. This is the sliding axiom made
explicit.

## Cartesian: `(,)`

```haskell
import Circuit (Trace, run, ambient)
import Circuit.Tensor (ambientBy)
import qualified Circuit.Trace as T

-- A simple increment circuit
inc :: Trace (,) (->) Int Int
inc = T.Arr (+1)

-- Thread a String label through
slide (x, (s, a)) = (s, (x, a))

-- >>> run (ambientBy slide inc) ("count", 5)
-- ("count",6)
```

The label `"count"` is preserved while `inc` operates on the payload.

## Iteration: `Either`

For the `Either` tensor, `ambientBy` uses the coproduct braid. The
ambient wire is part of the nested sum, not a tuple riding alongside the
payload, so the input and output are nested `Either` values.

```haskell
import Circuit (Trace, run, ambient)
import Circuit.Tensor (ambientBy, braid)
import qualified Circuit.Trace as T

-- A counting loop that also accumulates a log
step :: Either (Int, [Int]) () -> Either (Int, [Int]) (Int, [Int])
step (Right ()) = Left (0, [])
step (Left (n, history))
  | n < 3     = Left (n + 1, n : history)
  | otherwise = Right (n, history)

counter :: Trace Either (->) () (Int, [Int])
counter = T.Knot step

-- >>> run (ambientBy braid counter) (Right ())
-- Right (3,[2,1,0])

-- A value in the outer-Left position bypasses the circuit unchanged.
-- >>> run (ambientBy braid counter) (Left "run-1")
-- Left "run-1"
```

Because `Either` uses `Left`/`Right` for both control flow and the
ambient wire, a `Left`-carrying input exits immediately with the ambient
value; only a `Right`-carrying input enters the loop.

## The Two Cases

`ambient` recurses over the `Trace` constructors:

```haskell
import Circuit
import qualified Circuit.Trace as T

ambientBy _braid (T.Arr f) = T.Arr (untrace f)
ambientBy braid (T.Knot k) = T.Knot (dimap braid braid (untrace k))
```

| Constructor | What happens |
|-------------|-------------|
| `Arr` | State tags along via `untrace` |
| `Knot` | State slides past feedback via braiding |

The `Knot` case is the interesting one. Without braiding, the state
would collide with the feedback channel. The braid `t x (t s a) -> t s (t x a)`
swaps the two wires so the state can pass through unscathed.

## See Also

- `src/Circuit.hs` — `ambient` definition and doctests
- `examples/marks-and-stacks.md` — `∥` as the sixth mark
- `examples/state.md` — visible, ambient, and hidden state compared
