# reader-monad ⟜ when you need monadic composition

`Circuit` and `Hyper` do not provide `Applicative` or `Monad` instances.
These would collapse feedback structure on every step, reducing circuits
to plain functions. If you need monadic composition, the path is explicit:
observe, work in `Reader`, re-encode.

---

## The pattern

`lower` extracts a plain function. `lift` embeds one. Between them sits
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
  let n'  = lower inc n
      n'' = lower double n'
  in n''

-- >>> step ↓ 5
-- 12
```

The same pattern works for `Circuit` via `reify`:

```haskell
import Circuit.Circuit

incC :: Circuit (->) (,) Int Int
incC = Lift (+ 1)

doubleC :: Circuit (->) (,) Int Int
doubleC = Lift (* 2)

stepC :: Circuit (->) (,) Int Int
stepC = Lift $ \n ->
  let n'  = reify incC n
      n'' = reify doubleC n'
  in n''

-- >>> stepC ↘ 5
-- 12
```

---

## Why not an instance?

A `Monad` instance would hide the `lower`/`lift` pairs:

```haskell
-- Hypothetical (removed) instance:
-- m >>= k = lift $ \a -> lower (k (lower m a)) a
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
newtype Parser f s a = Parser
  { unParser :: Circuit (->) Either f (These a f) }
```

`Parser` defines its own `Applicative`, `Monad`, and `Alternative`
instances that thread stream state through `These` results. The monad
is real — but it lives at the application layer, not in the substrate.

---

## Reference

- `examples/parser.md` — `Parser` newtype with lawful `Applicative`/`Monad`
- `src/Circuit/Hyper.hs` — `lower`, `lift`
- `src/Circuit/Circuit.hs` — `reify`, `Lift`
