# Hyper Buries the Knot

<div align="center">

✦ · ✧ · ✦

*In which Hyper is re-examined; the triangle identity is decomposed; and a lemma that held the proof together gets a name.*

**[⟵ Prev: A Knot Recovers Fix](02-a-knot-recovers-fix.md)** · **[Next: Holding Hands or Taking Turns ⟶](04-holding-hands-or-taking-turns.md)**

</div>

---

`Trace` is the initial encoding — a syntax tree with `Arr` and `Knot`.
Sequential composition is `(.)` or `(>>>)`; there is no `Compose`
constructor. `Hyper` is the final encoding — a coinductive type where
feedback is structural.

The early narrative said "`encode` maps `Trace` to `Hyper`, and `Knot`
dissolves into the type." That is still true in spirit:
`encode (Knot f) = trace (lift f)` uses `Hyper`'s own `Traced` instance.
But `Trace` is now already in normal form; the dissolution happens
directly in `encode`, not in a separate pass.

For the `Free` fragment — `Trace` without `Knot` — the picture sharpens.
`Arr` maps to `Free`'s `Lift`, and sequential composition maps to
`Compose`. The unique functor from the free category to `Hyper` is
`encodeFree`. The full `encode` from `Trace` is just the universal fold
with `lift`:

```haskell
encode :: Trace (,) (->) a b -> Hyper a b
encode = foldTrace lift
```

or, equivalently,

```haskell
encode (Arr f)  = lift f
encode (Knot f) = trace (lift f)
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
lift     :: (a -> b) -> Hyper a b        -- embed a plain function (coinductive)
lower    :: Hyper a b -> (a -> b)        -- observe by severing the feedback
runHyper :: Hyper a a -> a               -- tie the self-referential knot
push     :: (a -> b) -> Hyper a b -> Hyper a b  -- prepend to continuation
```

---

## The Triangle, Factorized

The triangle identity connects the initial and final encodings:

```
lower . encode = run
```

where `run :: Trace (,) (->) a b -> a -> b` is the canonical fold out
of `Trace`.

Because `encode = foldTrace lift` and `run = foldTrace id`, the triangle
is an instance of the universal fold: `lower` is the natural
transformation from `Hyper` back to `(->)` that makes the two target
categories agree.

For the `Free` fragment, the corresponding triangle is:

```
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

The definition `encode = foldTrace lift` is sound only if the direct
`Knot` case, `encode (Knot f) = trace (lift f)`, and the base-arrow
interpretation, `run (Knot f) = trace f`, produce behaviours that match
under `lower`.

That equality is the statement:

```haskell
lift . trace = trace . lift
```

where the left-hand `trace` is `Traced (->) (,)` (lazy knot) and the
right-hand `trace` is `Traced Hyper (,)` (invoke/cont).

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
  -- expand Traced Hyper (,), substitute k = Hyper (const x)
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
expansion of `trace (lift f)` implicitly relied on it — but it was
never extracted and named. It now has a home in
`examples/lift-trace-commute.md`.

---

## The Traced Hyper (,) Instance

The `Traced Hyper (,)` instance implements the `trace` method for
`Hyper`:

```haskell
instance Traced Hyper (,) where
  trace body = Hyper $ \k ->
    let pair = invoke body cont
        cont = Hyper $ \_ ->
          let a_val = invoke k (Hyper (const (snd pair)))
           in (fst pair, a_val)
     in snd pair
```

This is a hand-rolled implementation of `lift . trace . lower` — the
conjugation of the base arrow's trace by the adjunction. It is used
operationally by `encode` in the `Knot` case (`trace (lift f)`), and it
exists to satisfy the typechecker and to prove the lemma above.

The instance is load-bearing for the categorical guarantee — without
it, `lower . trace = trace . lower` doesn't hold, and the triangle
can't be proved for the `Knot` case. It is a proof object, but it is
also exercised by `encode`.

---

## encodeEither

For the `Either` tensor, Hyper encodes loops directly through its
continuation structure:

```haskell
encodeEither :: (Either a b -> Either a c) -> Hyper (Either a b -> c) (Either a b -> c)
encodeEither f = h where
  h = Hyper $ \k s -> case f s of
    Right c -> c
    Left a  -> invoke k h (Left a)
```

This is a hand-rolled Either loop inside Hyper's continuation
structure. `runEither f b = runHyper (encodeEither f) (Right b)` ties the
knot. No `Traced` instance needed — the loop lives in `invoke`.

---

## When to Use Each

**Build in `Trace`** when you need inspectable structure — static
analysis, staged metering, transposition via `Net`.

**Eliminate via `run`** (for `Trace`) or `runFree` (for `Free`) when you
want a plain function. This is the operational path.

**Build in `Hyper`** using Kidney-Wu's pattern: compose with `(.)`,
thread with `push`, eliminate once with `runHyper`. Don't `encode` a
`Trace` — build the `Hyper` directly. The performance holds for
single-elimination patterns.

**Use `Queue`** (from `free-category`) when you need O(1) cons, O(1)
`viewl`, and O(n) elimination with no closure overhead. `Queue` is
the inspectable, efficient alternative to both `Free` and `Hyper`.

---

## Summary

`Hyper` is the final encoding of the free traced monoidal category,
dual to `Trace`. `encode = foldTrace lift` is the unique traced functor.
`lower . encode = run` is the triangle identity. `lift . trace = trace . lift`
is the lemma that makes it work — the traced functor condition, proven
in the `Knot` case of the triangle. `Traced Hyper (,)` is used by
`encode` for loops and proves the lemma.

**Next:** [04-holding-hands-or-taking-turns.md](04-holding-hands-or-taking-turns.md) — the tensor parameter;
`(,)` vs `Either`; holding hands vs taking turns.

---

## References

- [Kidney & Wu (2026)](https://doi.org/10.1145/3776649) — hyperfunctions
- [Joyal, Street & Verity (1996)](https://doi.org/10.1017/s0305004100074338) — traced monoidal categories
- `src/Circuit/Hyper.hs` — the five marks and `Traced` instance
- `src/Circuit/Trace.hs` — the `Trace` GADT and its interpreters
- `src/Circuit/Traced.hs` — the `Traced` class
- `examples/lift-trace-commute.md` — full proof of the traced functor lemma
- `src/Circuit/Free.hs` — the free category GADT
