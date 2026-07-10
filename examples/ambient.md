# Ambient State

> Threading a state wire through a `Trace`.

## The Idea

`ambient` slides a state component past a circuit unchanged. The circuit
operates on the payload; the state rides alongside via the tensor —
ambient, unnoticed.

```haskell
ambientBy :: (Profunctor arr, Traced arr t)
          => (forall x y z. t x (t y z) -> t y (t x z))
          -> Trace t arr a b
          -> Trace t arr (t s a) (t s b)
```

The braid argument swaps the state wire past the feedback channel:
`\(x, (s, a)) -> (s, (x, a))` for `(,)`. This is the sliding axiom made
explicit.

## Cartesian: `(,)`

```haskell
{-# LANGUAGE BlockArguments #-}

import Circuit (Trace(..), run, ambient)

-- A simple increment circuit
inc :: Trace (,) (->) Int Int
inc = Arr (+1)

-- Thread a String label through
braid (x, (s, a)) = (s, (x, a))

-- >>> run (ambientBy braid inc) ("count", 5)
-- ("count",6)
```

The label `"count"` is preserved while `inc` operates on the payload.

## Iteration: `Either`

```haskell
import Circuit (Trace(..), run, ambient)

-- A counting loop that also accumulates a log
step (n, log) = if n < 3
  then Left (n + 1, n : log)
  else Right (n, log)

counter :: Trace Either (->) () (Int, [Int])
counter = Knot step

-- Thread an extra label through the Either loop
braidE (Left (s, a))  = (s, Left a)
braidE (Right (s, c)) = (s, Right c)

-- >>> run (ambientBy braidE counter) ("run-1", ())
-- ("run-1",(3,[2,1,0]))
```

The label `"run-1"` slides past every iteration.

## The Three Cases

`ambient` recurses over the `Trace` constructors:

```haskell
ambientBy _braid (Arr f) = Arr (untrace f)
ambientBy braid (Knot k) = Knot (dimap braid braid (untrace k))
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
- `circuits-perf` — `ambientPair` specializes `ambient` to `(,)`
