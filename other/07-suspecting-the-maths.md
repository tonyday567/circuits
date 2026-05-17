# Suspecting the Maths

**Summary:** In which we look closely at what we built, find six suspicious
spots, and discover that the free traced monoidal category has teeth.
**Prev:** [06-follow-the-knots.md](06-follow-the-knots.md)

---

The arc so far has been constructive: five marks, six axioms, two encodings,
two tensors, a hierarchy, a frontier. Now we audit. Every free structure
looks perfect until you try to use it.

---

## The Six Suspicions

### 1. Axioms without tests

The entire edifice rests on six axioms. There are no QuickCheck properties
verifying them for either tensor. This is the highest-value gap — laws
without exercise.

### 2. Profunctor instance for Hyper

```haskell
dimap f g h = Hyper $ g . invoke h . dimap g f
```

Recursive definition of `dimap` in terms of itself. Coinductive reasoning
might save it, but the composition law is suspect. The comment even admits
`rmap` is "not a composition of push."

### 3. Missing Trace Hyper Either

`Hyper` has `Trace Hyper (,)` but no `Trace Hyper Either`. `encodeEither` is
a workaround with a mangled type that does not compose with `encode` or
`flatten`. The narrative claims both tensors work, but `Hyper` only really
hosts `(,)`.

### 4. Monad (Hyper a) is the degenerate model

```haskell
m >>= k = lift $ \a -> lower (k (lower m a)) a
```

Every bind collapses both sides with `lower`. The monad instance is morally
`Reader a` — the free traced monoidal category collapses to reader semantics
under bind.

### 5. O(1) needs qualification

Composition in `Hyper` is O(1) to *construct*, but observation (`lower`,
`run`) still traverses the closure chain. The narrative should distinguish
construction cost from observation cost.

### 6. Compact closed frontier is hand-wavy

No `Dual` constructor, no cup, no cap, no zig-zag check. The self-duality
of `Hyper` makes the question natural, but natural is not proven.

---

## Insights from the Audit

**Hyper eats its own dual.** The type `Hyper a b = Hyper b a -> b` is
self-dual by construction. The dual of `A → B` is `B → A`, and `Hyper`
internalises this. The compact closed question is not speculation — it is
the natural next step, because the duality is already baked in.

**The Mendler case is `viewl` for feedback channels.** In RwR, `viewl`
inspects the head of a type-aligned queue before recursing. In `reify`, the
Mendler case inspects whether the head of a left-nested composition is a
`Knot`. If it is, `untrace` threads the trailing morphism into the channel
*before* `trace` closes it. The pattern match is the operational price of
intensionality.

**`(,)` and `Either` are two notions of time.** `(,)` says feedback and
output coexist in the same tick. `Either` says they alternate. This is why
`Circuit (Kleisli IO) Either` is isomorphic to `Pipe` — a pipe is exactly a
process that alternates between awaiting and yielding.

**The triangle `lower . encode = reify` is not an isomorphism.**
`flatten . encode ≠ id` in general. `Circuit` is intensional, `Hyper` is
extensional. The map from syntax to semantics loses information that cannot
be recovered. Feature, not bug — but it should be stated explicitly.

---

## Priorities

1. **Axiom tests** — highest value, lowest risk. Grounds everything else.
2. **Profunctor law check** — quick property test, validates or kills the
   instance.
3. **Trace Hyper Either feasibility** — decide whether it is impossible or
   just hard.
4. **Compact closed probe** — research direction, not urgent.
5. **Performance benchmark** — validate or qualify the O(1) claim.

---

## References

- `other/axioms.md` — the axioms to test
- `src/Circuit/Traced.hs` — `Trace` instances under suspicion
- `src/Circuit/Hyper.hs` — `Profunctor`, `Monad`, `Trace Hyper (,)`
- `~/mg/loom/suspect-maths.md` — working audit log
