# Optics and Circuits

An optic is a pair of morphisms with a hidden residual:

```haskell
data LensC arr t s t' a b = forall c. LensC
  { getC :: arr s (t c a)      -- e.g. s -> (c, a)   or   s -> Either c a
  , setC :: arr (t c b) t'     -- e.g. (c, b) -> t   or   Either c b -> t
  }
```

`Circuit arr t` is the free traced monoidal category. `Knot` hides the
residual; `untrace` introduces it.

For `(,)` the residual is a product:

```haskell
untrace :: (b -> c) -> (s, b) -> (s, c)
untrace = second
```

`untrace` for `(,)` is the `_2` lens. For `Either` it is the `_Right` prism:

```haskell
untrace :: (b -> c) -> Either a b -> Either a c
untrace = fmap
```

`trace` is the dual: from a stateful morphism to a plain morphism by tying the
feedback loop. For `(,)` it is a lazy knot; for `Either` it is iteration until
`Right`.

---

## Hiding the residual

```haskell
-- | Hide the residual with Knot.
-- >>> reify (Knot biased) 5
-- 20
biased :: (Int, Int) -> (Int, Int)
biased (s, x) = (x + 10, s + x)
```

The `Trace` instance for `(->)` and `(,)`:

```haskell
trace biased 5 = let (s, c) = (5 + 10, s + 5) in c
               = let s = 15 in 15 + 5
               = 20
```

Laziness resolves the feedback because the new state `x + 10` does not depend
on the old state `s`.

---

## Composition: merging residuals

When you compose two circuits built from `Knot`, their residuals merge
compositionally. The sliding and vanishing axioms guarantee that the combined
circuit is equivalent to a single `Knot` over a merged residual.

```haskell
-- | Compose two knotted circuits.
-- >>> let c1 = Knot (\(s, x) -> (x + 10, s + x))
-- >>>     c2 = Knot (\(t, y) -> (y * 2, t + y))
-- >>> in reify (c2 ⊙ c1) 5
-- 60
```

By the vanishing axiom, the composite residual is the product (or sum) of the
individual residuals. The trace handles the wiring; you never thread state
manually.

---

## The trace axioms

The trace axioms (vanishing, yanking, tightening, sliding, superposition) are
the optic laws written for feedback loops. Yanking (`trace swap = id`) is
the identity law; tightening is naturality; sliding is the put-put law.

---

## The coend gap

The standard categorical formulation of optics (Riley) is a coend:

```
Optic ⟨s, t⟩ ⟨a, b⟩ = ∫^m C(s, m ⊗ a) × C(m ⊗ b, t)
```

The residual `m` is the hidden state. The coend quantifies over *all*
possible residuals — a universal type saying "there exists some `m` such that."

In a traced monoidal category, `trace` and `untrace` give primitives to
introduce and eliminate a *specific* residual. `Knot` hides it; composition of
knotted circuits merges residuals via vanishing and sliding. The trace handles
the wiring for any *chosen* residual — but it does not quantify over the family
of all possible residuals. That universal quantification is what the coend adds.

In a compact closed category the coend collapses because the residual can be
constructed explicitly (it is an internal hom). The `Trace` class is strictly
weaker: it eliminates residuals but does not construct new ones. The gap between
trace and coend is precisely the gap between traced monoidal and compact closed.

What the circuits setting gives you is the *practical* side: pick a residual,
`Knot` it, compose with others, let the axioms handle the wiring. The coend
remains the *semantic* type that captures "any possible wiring" — a different
structure at a different level.
