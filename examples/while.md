---
title: "While, Until, For — Trace loops"
category: core
status: stable
tags: ["either", "iteration", "loops"]
---

# While, Until, For — Trace loops

The three canonical loop patterns using `Trace`'s `Knot` constructor
and the `Traced (->) Either` instance.  One fundamental pattern, three
specialisations.

```haskell
-- $setup
-- >>> import Circuit (Trace (..), run)
-- >>> import Control.Category (id, (.))
-- >>> import Prelude hiding (id, (.))
```

---

## The convention

`Traced (->) Either` uses `Left = feedback` (iterate) and `Right = exit`
(done).  We adopt the same convention for user-facing step functions:

```haskell
type Step s r = s -> Either s r   -- Left s = continue, Right r = done
```

No bridge needed — the step function speaks the same language as `Trace`.

---

## loop

The fundamental form.  A `Trace` wraps the step function directly.

```haskell
loop :: Step s r -> s -> r
loop step s0 = run (Knot step') s0
  where
    step' (Left s) = step s
    step' (Right s) = step s
```

```haskell
-- >>> let countdown n | n <= 0 = Right 0 | otherwise = Left (n - 1)
-- >>> loop countdown 5
-- 0

-- >>> loop countdown 0
-- 0
```

---

## while — condition, then step

Check `cond` before each step.  When `cond` fails, exit with `done s`.

```haskell
whileC :: (s -> Bool) -> (s -> r) -> Step s r -> s -> r
whileC cond done step s0 = run (Knot step') s0
  where
    step' (Left s)  = if cond s then step s else Right (done s)
    step' (Right s) = step' (Left s)
```

```haskell
-- >>> let pos n = n > 0; countdown n | n <= 0 = Right 0 | otherwise = Left (n - 1)
-- >>> whileC pos id countdown 5
-- 0

-- >>> whileC pos id countdown 0
-- 0
```

---

## until — step, then condition

Step first (always runs at least once), then check `cond` on the new
state.  When `cond` becomes true, exit with `done`.

```haskell
untilC :: (s -> Bool) -> (s -> r) -> Step s r -> s -> r
untilC cond done step s0 = run (Knot step') s0
  where
    step' (Left s)  = case step s of
                        Right r -> Right r
                        Left s' -> if cond s' then Right (done s') else Left s'
    step' (Right s) = step' (Left s)
```

```haskell
-- >>> let countup target n | n >= target = Right n | otherwise = Left (n + 1)
-- >>> untilC (>= 3) id (countup 5) 0
-- 3

-- >>> untilC (>= 3) id (countup 5) 5
-- 5
```

---

## for — counted loop

Index `i` runs from `0` to `n-1`.  The body receives `i` and the current
state; it must produce a result within `n` iterations.

```haskell
forC :: Int -> (Int -> Step s r) -> s -> r
forC n body s0 = loop step' (0, s0)
  where
    step' (i, s)
      | i >= n    = error "forC: body did not produce result"
      | otherwise = case body i s of
                      Right r -> Right r
                      Left s' -> Left (i + 1, s')
```

```haskell
-- >>> forC 5 (\i (_, acc) -> if i == 4 then Right (acc + i + 1) else Left ((), acc + i + 1)) ((), 0 :: Int)
-- 15
```

---

## Convention

All loops use the same convention as `Traced (->) Either`:

| branch | meaning |
|--------|---------|
| `Left s`  | **feedback** — continue with new state `s` |
| `Right r` | **exit** — done, produce result `r` |

No bridge, no swap.  The step function speaks the same language as `Trace`.
