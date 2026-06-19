# Hyper Buries the Knot

<div align="center">

✦ · ✧ · ✦

*In which Hyper is re-examined; the triangle identity is decomposed; and a lemma that held the proof together gets a name.*

**[⟵ Prev: A Knot Recovers Fix](02-a-knot-recovers-fix.md)** · **[Next: Holding Hands or Taking Turns ⟶](04-holding-hands-or-taking-turns.md)**

</div>

---

`Circuit` is the initial encoding — a syntax tree with `Lift`, `Compose`,
`Knot`. `Hyper` is the final encoding — a coinductive type where feedback
is structural.

The early narrative said "`encode` maps `Circuit` to `Hyper`, and `Knot`
dissolves into the type." That was true of the code at the time:
`encode (Knot k) = trace (encode k)` used Hyper's own `Trace` instance.
But it was misleading about *where* the dissolution happens.

With the discovery of `Free`, the picture sharpens. `Knot` dissolves in
`freeze` — a `Circuit → Free` map that calls `trace` on the base arrow.
`Hyper` never sees a `Knot`. `encode` factors:

```haskell
encode :: Circuit (->) (,) a b -> Hyper a b
encode = encodeFree . freeze
```

where `encodeFree :: Free (->) a b -> Hyper a b` is the unique
functor from the free category to the final encoding. It handles only
`Lift` and `Compose`.

---

## The Type

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

The self-referential duality is built in: to produce a `b`, you invoke
the dual `Hyper b a`. This captures the essential pattern of
continuations that communicate with their own continuations.

The key operations:

```haskell
lift  :: (a -> b) -> Hyper a b        -- embed a plain function (coinductive)
lower :: Hyper a b -> (a -> b)        -- observe by severing the feedback
run   :: Hyper a a -> a               -- tie the self-referential knot
push  :: (a -> b) -> Hyper a b -> Hyper a b  -- prepend to continuation
```

---

## The Triangle, Factorized

The triangle identity connects initial and final encodings:

```
lower . encode = reify
```

With `Free`, this decomposes into two claims:

```
encode = encodeFree . freeze
lower . encodeFree = runFree
```

`encodeFree` is the canonical fold:

```haskell
encodeFree :: Free (->) a b -> Hyper a b
encodeFree (Lift f)       = lift f
encodeFree (Compose f g)  = encodeFree f . encodeFree g
```

`runFree` is the same fold into `(->)`:

```haskell
runFree :: Free arr a b -> arr a b
runFree (Lift f)       = f
runFree (Compose f g)  = runFree f . runFree g
```

That `lower . encodeFree = runFree` is immediate from the definitions
of `lower` and `lift`. Both are folds of the free category — one into
`Hyper`, one into `(->)` — and `lower` is the natural transformation
between the two targets.

---

## The Lemma: `lift . trace = trace . lift`

The factorization `encode = encodeFree . freeze` is sound only if the
old `encode (Knot k) = trace_Hyper (encode k)` and the new
`encodeFree (freeze (Knot k)) = lift (trace_arr (reify k))` produce
the same `Hyper`.

That equality is the statement:

```haskell
lift . trace_arr = trace_Hyper . lift
```

Where `trace_arr` is the `Trace (->) (,)` instance (lazy knot) and
`trace_Hyper` is the `Trace Hyper (,)` instance (invoke/cont).

This is the **traced functor** condition: a functor between traced
monoidal categories that preserves the trace structure. It's not an
axiom of a single traced category — it's a homomorphism between two
of them.

Proof: both sides reduce to the same lazy knot under `lower`.

```
lower (lift (trace f)) x
  = trace f x
  = let (a, c) = f (a, x) in c

lower (trace (lift f)) x
  -- expand trace_Hyper, substitute k = Hyper (const x)
  = let pair = invoke (lift f) cont
        cont = Hyper $ \_ -> (fst pair, x)
     in snd pair
  -- invoke (lift f) cont = f (fst pair, x)
  = let pair = f (fst pair, x) in snd pair
  = let (a, c) = f (a, x) in c
```

For `Hyper`, behavioral equality (under `lower`) IS equality — that's
what "final encoding" means. So `lift . trace = trace . lift` holds
in `Hyper`.

This lemma is the load-bearing step in the triangle proof for the
`Knot` case. It was proven in chapter 03's triangle proof — the
expansion of `trace (encode k)` implicitly relied on it — but it was
never extracted and named. It now has a home in
`examples/lift-trace-commute.md`.

---

## The Trace Hyper (,) Instance

The `Trace Hyper (,)` instance implements `trace_Hyper`:

```haskell
instance Trace Hyper (,) where
  trace body = Hyper $ \k ->
    let pair = invoke body cont
        cont = Hyper $ \_ ->
          let a_val = invoke k (Hyper (const (snd pair)))
           in (fst pair, a_val)
     in snd pair
```

This is a hand-rolled implementation of `lift . trace_arr . lower` — the
conjugation of the base arrow's trace by the adjunction. It exists to
satisfy the typechecker and to prove the lemma above. It has no
operational callers: `encode` no longer calls `trace_Hyper` directly,
and no other code path uses `Trace Hyper (,)`.

The instance is load-bearing for the categorical guarantee — without
it, `lower . trace_Hyper = trace_arr . lower` doesn't hold, and the
triangle can't be proved for the `Knot` case. It is a proof object,
not dead code.

---

## encodeEither

For the `Either` tensor, Hyper encodes loops directly through its
continuation structure:

```haskell
encodeEither :: (Either a b -> Either a c) -> Hyper (Either a b -> c) (Either a b -> c)
encodeEither f = h where
  h = Hyper $ \k s -> case f s of
    Right c -> c
    Left a -> invoke k h (Left a)
```

This is a hand-rolled Either loop inside Hyper's continuation
structure. `runEither f b = run (encodeEither f) (Right b)` ties the
knot. No `Trace` instance needed — the loop lives in `invoke`.

---

## When to Use Each

**Build in `Circuit`** when you need inspectable structure — static
analysis, staged metering, transposition via `Net`.

**Eliminate via `freeze >>> runFree`** when you want a plain function.
This is the operational path.

**Build in `Hyper`** using Kidney-Wu's pattern: compose with `(.)`,
thread with `push`, eliminate once with `run`. Don't `encode` a
`Circuit` — build the `Hyper` directly. The performance holds for
single-elimination patterns.

**Use `Queue`** (from `free-category`) when you need O(1) cons, O(1)
`viewl`, and O(n) elimination with no closure overhead. `Queue` is
the inspectable, efficient alternative to both `Free` and `Hyper`.

---

## Summary

`Hyper` is the final encoding of the *free category*, not of `Circuit`.
`encodeFree :: Free → Hyper` is the unique functor. `encode = encodeFree . freeze`
factors through `Free`. `lift . trace = trace . lift` is the lemma that
makes it work — the traced functor condition, proven in the Knot case
of the triangle. `Trace Hyper (,)` exists to prove the lemma;
operationally, it has no callers.

**Next:** [04-holding-hands-or-taking-turns.md](04-holding-hands-or-taking-turns.md) — the tensor parameter;
`(,)` vs `Either`; holding hands vs taking turns.

---

## References

- [Kidney & Wu (2026)](https://doi.org/10.1145/3776649) — hyperfunctions
- [Joyal, Street & Verity (1996)](https://doi.org/10.1017/s0305004100074338) — traced monoidal categories
- `src/Circuit/Hyper.hs` — the five marks and Trace instance
- `examples/lift-trace-commute.md` — full proof of the traced functor lemma
- `src/Circuit/Free.hs` — the free category GADT
