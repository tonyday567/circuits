# pair-loops ⟜ fused qList + takeE in one Knot

Fuse a list walker and a count limiter into a single `Knot`. The state
is a 3-tuple `([Int], Int, [Int])` — remaining list, remaining count,
accumulated output. One loop, no composition.

Paste each block into `cabal repl`.

```haskell
{-# LANGUAGE LambdaCase #-}
import Circuit.Circuit (Circuit(..), reify)

-- | qList [1,2,3,4,5] + takeE 2, fused.
--   Feedback is a 3-tuple: (remaining, count, accumulator).
paired :: Circuit (->) Either () (Maybe [Int])
paired = Knot body
  where
    body (Right ())              = emit ([1,2,3,4,5], 2, [])
    body (Left  (xs, k, acc))    = emit (xs, k, acc)
    emit ([], _, acc)            = Right (Just (reverse acc))
    emit (_,  0, acc)            = Right (Just (reverse acc))
    emit (x:xs', k, acc)         = Left  (xs', k-1, x:acc)

-- >>> reify paired ()
-- Just [1,2]
```

## what's happening

The Knot's feedback type is `([Int], Int, [Int])` — three values
coupled into one loop. Each iteration either:
- stops when list is empty or count hits 0 (`Right`)
- continues, consuming one element and decrementing count (`Left`)

This is the Circuit equivalent of `examples/hyper-stream.md` but using
the GADT's `Knot` constructor with `Either` tensor (`Left` = continue,
`Right` = stop).

## separate vs fused

See `examples/two-loops.md` for the same task done as two separate
Circuits, plus a fused version. The separate version shows the
decomposition; this card shows the fused monolith.

## reference

- `Circuit.Circuit` — Lift, Compose, Knot constructors
- `examples/hyper-stream.md` — same pattern via Hyper directly
- `examples/two-loops.md` — separate Knots + fused comparison
