---
name: reader-monad
description: When you need monadic composition
tags: ['monad', 'escape-hatch']
---
# reader-monad ⟜ when you need monadic composition

`Trace` and `Hyper` do not provide `Applicative` or `Monad` instances.
These would collapse feedback structure on every step, reducing circuits
to plain functions. If you need monadic composition, the path is explicit:
observe, work in `Reader`, re-encode.

---

## The pattern

`observe` extracts a plain function. `lift` embeds one. Between them sits
the full power of Haskell's function arrow:

```haskell
import Circuit

-- Two hyperfunctions
inc :: Hyper Int Int
inc = lift (+ 1)

double :: Hyper Int Int
double = lift (* 2)

-- Monadic-style sequencing via explicit observation
step :: Hyper Int Int
step = lift $ \n ->
  let n'  = observe inc n
      n'' = observe double n'
  in n''

-- >>> observe step 5
-- 12
```

The same pattern works for `Trace` via `run`:

```haskell
import Circuit

incC :: Trace (,) (->) Int Int
incC = Arr (+ 1)

doubleC :: Trace (,) (->) Int Int
doubleC = Arr (* 2)

stepC :: Trace (,) (->) Int Int
stepC = Arr $ \n ->
  let n'  = run incC n
      n'' = run doubleC n'
  in n''

-- >>> run stepC 5
-- 12
```

---

## Why not an instance?

A `Monad` instance would hide the `observe`/`lift` pairs:

```haskell
-- Hypothetical (removed) instance:
-- m >>= k = lift $ \a -> observe (k (observe m a)) a
```

This discards continuation structure. Two hyperfunctions that differ
internally can map to the same observed behavior, and `>>=` would
erase the distinction silently. The explicit version keeps the
collapse visible.

---

## When you genuinely need a monad

Build a newtype with its own semantics. `circuits-parser` does exactly
this:

```haskell
-- Local copy so the example stays self-contained.
data These a b = This a | That b | These a b deriving (Show, Eq)

newtype Parser f s a = Parser
  { unParser :: Trace Either (->) f (These a f) }
```

`Parser` defines its own `Applicative`, `Monad`, and `Alternative`
instances that thread stream state through `These` results. The monad
is real — but it lives at the application layer, not in the substrate.

---

## Reference

- [circuits-parser](https://github.com/tonyday567/circuits-parser) — parser library using circuits
- `src/Circuit/Hyper.hs` — `observe`, `lift`
- `src/Circuit.hs` — `run`, `Arr`
