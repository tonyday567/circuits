# Ambient State

> Threading a state wire through a Circuit.

## The Idea

`ambient` slides a state component past a circuit unchanged. The circuit
operates on the payload; the state rides alongside via the tensor —
ambient, unnoticed.

```haskell
ambient :: (Profunctor arr, Trace arr t)
        => (forall x y z. t x (t y z) -> t y (t x z))
        -> Circuit arr t a b
        -> Circuit arr t (t s a) (t s b)
```

The braid argument swaps the state wire past the feedback channel:
`\(x, (s, a)) -> (s, (x, a))` for `(,)`. This is the sliding axiom made
explicit.

## Cartesian: `(,)`

```haskell
{-# LANGUAGE BlockArguments #-}

import Circuit
import Circuit.Circuit (ambient)

-- A simple increment circuit
inc :: Circuit (->) (,) Int Int
inc = Lift (+1)

-- Thread a String label through
braid (x, (s, a)) = (s, (x, a))

-- >>> reify (ambient braid inc) ("count", 5)
-- ("count",6)
```

The label `"count"` is preserved while `inc` operates on the payload.

## Iteration: `Either`

```haskell
import Circuit.Traced (Trace(..))

-- A counting loop that also accumulates a log
step (n, log) = if n < 3
  then Left (n + 1, n : log)
  else Right (n, log)

counter :: Circuit (->) Either () (Int, [Int])
counter = Knot step

-- Thread an extra label through the Either loop
braidE (Left (s, a))  = (s, Left a)
braidE (Right (s, c)) = (s, Right c)

-- >>> reify (ambient braidE counter) ("run-1", ())
-- ("run-1",(3,[2,1,0]))
```

The label `"run-1"` slides past every iteration.

## The Three Cases

`ambient` recurses over the Circuit constructors:

```haskell
ambient _braid (Lift f) = Lift (untrace f)
ambient braid (Compose f g) = Compose (ambient braid f) (ambient braid g)
ambient braid (Knot k) = Knot (dimap braid braid (untrace k))
```

| Constructor | What happens |
|-------------|-------------|
| `Lift` | State tags along via `untrace` |
| `Compose` | State threads through both stages |
| `Knot` | State slides past feedback via braiding |

The `Knot` case is the interesting one. Without braiding, the state
would collide with the feedback channel. The braid `t x (t s a) -> t s (t x a)`
swaps the two wires so the state can pass through unscathed.

## See Also

- `src/Circuit/Circuit.hs` — `ambient` definition and doctests
- `other/01-marks-and-stacks.md` — `∥` as the sixth mark
- `circuits-perf` — `ambientPair` specializes `ambient` to `(,)`
