# encode-either ⟜ why Traced Hyper Either does not exist

`Hyper` has `Traced Hyper (,)` but no `Traced Hyper Either`. This card explains
why — and why `encodeEither` is the correct workaround, not a missing
instance waiting to be written.

---

## The gap

The two tensors give fundamentally different loop mechanics:

| tensor | loop mechanism | fits Hyper? |
|--------|---------------|-------------|
| `(,)` | lazy knot — output and feedback co-occur | yes — one `invoke` exchanges both |
| `Either` | iteration — `Left` re-enters, `Right` exits | no — needs stateful multiple re-entry |

`trace` for `(,)` ties a single lazy knot:

```haskell
instance Traced Hyper (,) where
  trace body = Hyper $ \k ->
    let pair = invoke body cont
        cont = Hyper $ \_ ->
          let a_val = invoke k (Hyper (const (snd pair)))
          in (fst pair, a_val)
    in snd pair
```

`body` calls `cont` once. `cont` returns `(a, b)` — both channels
simultaneously. The feedback value `a` and the input `b` are present in the
same tuple. One `let-rec` ties them.

## Why Either fails

`Traced (->) Either` is a while-loop:

```haskell
trace f b = go (Right b)
  where
    go x = case f x of
      Right c -> c
      Left a  -> go (Left a)
```

Each iteration potentially produces a *different* `Left a`. The next input
depends on the previous output. That is state threading.

`Hyper` is stateless. A continuation `Hyper b a` is a function: given a
hyperfunction, it produces a value. It has no memory of previous calls.

### The broken attempt

```haskell
-- DOES NOT COMPILE / DOES NOT WORK
trace body = Hyper $ \k ->
  let loop = Hyper $ \next ->
        case invoke body loop of
          Right c -> invoke k (Hyper (const c))
          Left a  -> invoke next loop
  in invoke body loop
```

Two fatal problems:

1. **If `body` calls `loop` before returning:** `loop` evaluates
   `invoke body loop` again — infinite recursion before `body` ever
   finishes.

2. **If `body` returns `Left a` without calling `loop`:** `case invoke body
   loop of Left a -> ...` matches, but `next` is unbound because `body`
   never invoked `loop`.

The asymmetry is structural. `Either` needs the trace to *react* to what
`body` returned and re-enter with modified state. `Hyper` only exposes
`body`'s final return — the continuation channel cannot be retroactively
changed.

## What works: encodeEither

`encodeEither` keeps the Either loop *inside* Hyper's function argument.
The state `Either a b` is explicit:

```haskell
encodeEither :: (Either a b -> Either a c)
             -> Hyper (Either a b -> c) (Either a b -> c)
encodeEither f = h
  where
    h = Hyper (\k s ->
      case f s of
        Right c -> c
        Left a  -> invoke k h (Left a))
```

`runEither` ties the knot and injects the initial state:

```haskell
runEither :: (Either a b -> Either a c) -> b -> c
runEither f b = run (encodeEither f) (Right b)
```

The iteration is not hidden behind a typeclass. It is explicit in the
function body. The state machine is first-class.

```haskell
-- | A simple while-loop: count up to 3.
-- >>> runEither (\case Right n | n < 3 -> Left (n + 1); _ -> Right n) (0 :: Int)
-- 3
```

## The deeper reason

`Hyper a b = Hyper b a -> b` is a **single exchange** model. One `invoke`,
one continuation, one result. `(,)` fits because both directions of the
channel travel together in a single tuple. `Either` fits only when the
iteration is reified as an explicit state machine — which is exactly what
`encodeEither` does.

To get `Traced Hyper Either` natively would require one of:

- Stateful `Hyper` (e.g. `Hyper s a b` with an explicit state parameter)
- Delimited continuations (the `Kleisli IO Either` approach)
- A different base type entirely

## Reference

- `src/Circuit/Hyper.hs` — `encodeEither`, `runEither`
- `examples/hyper.md` — the Either gap, final encoding limitations
- `holding-hands-or-taking-turns.md` — `(,)` vs `Either` semantics
