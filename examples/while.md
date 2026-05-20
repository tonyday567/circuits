# While, Until, For — Circuit loops

The three canonical loop patterns using Circuit's `Knot` constructor
and the `Trace (->) Either` instance.  One fundamental pattern, three
specialisations.

```haskell
-- $setup
-- >>> import Circuit (Circuit (..), Trace (..), reify)
-- >>> import Control.Category (id, (.))
-- >>> import Prelude hiding (id, (.))
```

---

## The pattern

A `Step` either produces a result (`Left r`, done) or a next state
(`Right s`, continue).  `Knot` ties the feedback loop via the `Either`
channel: `Left` feeds back, `Right` exits.  The step function and the
trace use opposite conventions — bridge with a swap.

```haskell
type Step s r = s -> Either r s
```

---

## loop

The fundamental form.  Apply `step` on each iteration; swap conventions
so that `Left r` (done) becomes `Right r` (exit) and `Right s` (continue)
becomes `Left s` (feedback).

```haskell
loop :: Step s r -> s -> r
loop step s0 = reify (Knot step') s0
  where
    step' (Left s)  = case step s of Left r -> Right r; Right s' -> Left s'
    step' (Right s) = case step s of Left r -> Right r; Right s' -> Left s'
```

```haskell
-- >>> let countdown n | n <= 0 = Left 0 | otherwise = Right (n - 1)
-- >>> loop countdown 5
-- 0

-- >>> loop countdown 0
-- 0
```

---

## while — condition, then step

Check `cond` before each step.  When `cond` fails, convert the state to
a result with `done` and exit.

```haskell
whileC :: (s -> Bool) -> (s -> r) -> Step s r -> s -> r
whileC cond done step s0 = reify (Knot step') s0
  where
    step' (Left s)  = if cond s then case step s of Left r -> Right r; Right s' -> Left s'
                                else Right (done s)
    step' (Right s) = step' (Left s)
```

```haskell
-- >>> let pos n = n > 0; countdown n | n <= 0 = Left 0 | otherwise = Right (n - 1)
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
untilC cond done step s0 = reify (Knot step') s0
  where
    step' (Left s)  = case step s of
                        Left r  -> Right r
                        Right s' -> if cond s' then Right (done s') else Left s'
    step' (Right s) = step' (Left s)
```

```haskell
-- >>> let countup target n | n >= target = Left n | otherwise = Right (n + 1)
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
                      Left r  -> Left r
                      Right s' -> Right (i + 1, s')
```

```haskell
-- >>> forC 5 (\i (_, acc) -> if i == 4 then Left (acc + i + 1) else Right ((), acc + i + 1)) ((), 0 :: Int)
-- 15
```

---

## Convention

| branch | `Step s r` (user code) | `Trace (->) Either` (Knot) |
|--------|------------------------|----------------------------|
| `Left` | **done** — return `r`  | **feedback** — iterate     |
| `Right`| **continue** — new `s` | **exit** — return `c`      |

The `step'` function bridges the two.  The swap is mechanical: wherever
the user's `step` returns `Left r`, `step'` returns `Right r`; wherever
`step` returns `Right s`, `step'` returns `Left s`.
