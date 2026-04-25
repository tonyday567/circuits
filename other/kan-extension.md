# Kan Extensions and Hyperfunctions

## The Hyperfunction Type

A hyperfunction (Kidney & Wu 2026, building on Launchbury et al. 2000) is defined recursively as:

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a → b }
```

When you unfold the recursion, the type expands to an infinitely-nested structure:

```
Hyper a b = (((...  → a) → b) → a) → b
```

The self-referential duality is built in: to produce a `b`, you invoke the dual `Hyper b a`. This captures the essential pattern of continuations that communicate with their own continuations.

## The Ran Characterization (Icelandjack)

There is an equivalent formulation via right Kan extensions. For constant functors `Const a` and `Const b`, the right Kan extension is:

```
Ran (Const a) (Const b) x  ≅  ∀c. (a → x) → b
```

The universal quantifier over `c` vanishes because constant functors don't depend on `c`, leaving a continuation-like type.

Applying `Fix` to collapse this into a single type:

```
Fix (Ran (Const a) (Const b))
  ≅ Ran (Const a) (Const b) (Fix (Ran (Const a) (Const b)))
  ≅ (a → Fix (Ran (Const a) (Const b))) → b
```

The inner argument must satisfy the type constraint of the self-referential definition. By coinduction, this matches:

```
Hyper a b  ≅  Fix (Ran (Const a) (Const b))
```

## Coinductive Equivalence

Both formulations are **final coalgebras**. They describe the same observable behavior when used as continuations:

- **Direct definition:** `Hyper a b = Hyper { invoke :: Hyper b a → b }` — operational form
- **Ran characterization:** `Fix (Ran (Const a) (Const b))` — categorical form

Since they are final coalgebras with observably identical behavior, they are coinductively equivalent. We treat them as the same type up to observation.

The Ran formulation explains *why* the self-duality emerges (from the continuation structure locked into the Ran form + the fixpoint), while the direct definition shows the *computational form*.

## Circuit and the Kan Extension Hierarchy

Just as `Hyper` is the final encoding for hyperfunctions, `Circuit` is the **initial encoding** — the free traced monoidal category:

```haskell
data Circuit arr t a b where
  Lift    :: arr a b → Circuit arr t a b
  Compose :: Circuit arr t b c → Circuit arr t a b → Circuit arr t a c
  Loop    :: arr (t a b) (t a c) → Circuit arr t b c
```

The unique traced functor from initial to final is:

```haskell
toHyper :: Circuit (->) t a b → Hyper a b
```

And the elimination functor is `lower`:

```haskell
lower :: (Category arr, Trace arr t) => Circuit arr t x y → arr x y
```

The triangle identity holds:

```
lower . toHyper = lower (on Circuit)
```

This is the unit-counit identity of the adjunction between initial and final encodings.

## The Hierarchy

Before the fixpoint, `Circuit a b` is related to the Ran of the free category:

```
Circuit a b ~ Ran (Const a) (Const b)  (before Fix)
```

Adding the trace (Loop) requires tying the knot with a fixpoint:

```
Hyper a b = Fix (Ran (Const a) (Const b))
```

This mirrors the progression in van der Ploeg & Kiselyov "Reflection without Remorse":

| Structure       | Initial (syntax)  | Final (semantics)     | Mechanism          |
|-----------------|-------------------|-----------------------|--------------------|
| Monoid          | list              | difference list       | CPS / Codensity    |
| Monad           | free monad        | codensity monad       | Ran                |
| Category        | Cat (lists)       | Queue                 | Ran (Yoneda)       |
| Traced category | Circuit (GADT)    | Hyper                 | Fix . Ran          |

The key insight: **composition in the final encoding is O(1) amortised** because continuations are threaded naturally, exactly as RwR achieves O(1) amortisation through explicit sequence representation. The Mendler case in `lower` (inspection before recursion) is the analogue of `viewl` on type-aligned queues.

## Implications

1. **Hyper is the codensity representation** of Circuit: it encodes the feedback channel structurally rather than as an explicit constructor.

2. **Sliding is free:** The axiom that traces slide across compositions holds automatically in Hyper because the continuation threads through every layer.

3. **The Mendler case enforces naturality:** Without the pattern match `lower (Compose (Loop f) g) = trace (f . untrace (lower g))`, the universal property is violated and Loop collapses into the degenerate model.

4. **Coinductive semantics:** The recursive Hyper definition is coinductively sound. We don't need strict proof that Fix (Ran ...) is isomorphic to Hyper — only that they observe the same.

## lower

lower is a left Kan extension — it's the universal traced functor extending the embedding arr → Circuit arr t along the trace structure.



