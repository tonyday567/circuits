# Pipes — Proxy decomposition

The `Proxy` type from Gabriel Gonzalez's `pipes` library decomposes into
Circuit tensors. The key is the repeated elimination pattern — every
instance follows the same Mendler fold.

## The Proxy type (simplified)

```haskell
data Proxy a' a b' b m r
    = Request a' (a  -> Proxy a' a b' b m r)  -- send a' downstream, await a
    | Respond b  (b' -> Proxy a' a b' b m r)  -- send b upstream,  await b'
    | M          (m    (Proxy a' a b' b m r)) -- monadic interleaving
    | Pure    r                               -- done
```

Four type parameters encode two bidirectional channels:

| parameter | direction  | role                              |
|----------|-----------|-----------------------------------|
| `a'`     | downstream| what we request                   |
| `a`      | upstream  | what we receive in response       |
| `b`      | upstream  | what we respond with              |
| `b'`     | downstream| what we receive as next request   |

## The universal eliminator

Every Proxy instance follows the same structural recursion — 13 times
through `fmap`, `<*>`, `>>=`, `<>`, `hoist`, `embed`, `local`, `listen`,
`pass`, `catchError`, `catch`:

```haskell
go p = case p of
    Request a' fa  -> Request a' (\a  -> go (fa  a ))  -- thread through cont
    Respond b  fb' -> Respond b  (\b' -> go (fb' b'))  -- thread through cont
    M          m   -> M (go <$> m)                      -- map through monad
    Pure    r      -> <instance-specific base case>
```

This is `cata` for the Proxy pattern functor. The `go . fa` is
hyperfunction `push` — threading the fold through the continuation slot.

## Decomposition into tensors

Strip the monad and look at the structure:

```
ProxyF a' a b' b r
    = Either (a', a → r) (b, b' → r)
```

Each branch is a `(,)` of `(payload, continuation_slot)`. The outer
`Either` chooses direction. In Circuit:

```haskell
-- the Proxy pattern as a Circuit tensor structure
type ProxyCircuit a' a b' b r =
    Circuit (->) Either (a', a → r) (b, b' → r)
```

Where:
- `Either` tensor chooses Request vs Respond (direction)
- `(,)` in each branch carries payload + continuation slot
- `Knot` ties the fixed point (the recursion over the continuation)

With monadic effects:

```haskell
type ProxyCircuitM m a' a b' b r =
    Circuit (Kleisli m) Either (a', a) (b, b')
```

The `r` parameter is the exit type — what `Pure` returns. The `M`
constructor is `Lift` in the `Kleisli m` arrow.
