# Hasegawa (1997): Recursion from Cyclic Sharing

## The Core Question

What is recursion really doing? Not the mathematical fixed-point abstraction, but the *operational reality*: Real implementations use cyclic data structures — self-referential environments, cyclic graphs — to achieve recursion efficiently. This is semantically different from applying a fixed-point combinator, even though both produce recursion.

Hasegawa's move: Use **traced monoidal categories** (from Joyal, Street, Verity) to model cyclic sharing formally. Then prove:

**Theorem 3.1 (the capstone):** In a cartesian traced category, traces and fixed-point operators are in bijection. The trace IS the fixed point.

---

## The Intersection: Circuit as Free Traced Structure

**Theorem 3.1 is why this axiom holds:**

```
lower . lift = id    [the adjunction unit]
```

Hasegawa proves traces are fixed points in cartesian structure. The adjunction forces `run (lift f) = fix f` as a derived consequence, not a primitive requirement.

**The Mendler case enforces the sliding axiom** (see `axioms-traced.md` for detailed proof with nlab reference):

```
Sliding (naturality in X):
  tr^X_R((id_B ⊗ g) ∘ f) = tr^Y_R(f ∘ (id_A ⊗ g))
  where f : A ⊗ X → B ⊗ Y, g : Y → X
```

In circuits, this becomes:

```haskell
lower (Compose (Loop f) g) = trace (f . untrace (lower g))
```

**Why this pattern match isn't obvious:** The nlab axiom is stated in terms of tensor and composition in the category. The circuits Mendler case rewires this operationally: when a loop appears on the left of composition, you must reinjure the arrow through `untrace`, allowing the trace to slide across the boundary. This is the sliding axiom *reified as a GADT pattern match*. See `axioms-traced.md` (Section: Axiom 6) for the detailed proof mapping the categorical statement to the operational form.

---

## Circuit as Free Object

Hasegawa's entire framework assumes traced monoidal categories exist and have nice properties. The circuits narrative *constructs* the free one via a GADT:

- **Lift** = strict monoidal functor (embedding base arrows)
- **Compose** = category laws (associativity, identity)
- **Loop** = the trace constructor (feedback channel)
- **Mendler case in lower** = naturality in X (sliding)

This is not just an instance of Hasegawa's framework. This is the free object that his framework presupposes.

---

## Where They Diverge

**Hasegawa:** Uses `letrec x = M in N` syntax. Defines semantic models (domain-theoretic, non-deterministic, etc.) and proves soundness/completeness.

**Circuits:** Uses a GADT constructor `Loop`. Provides two interpretations (Circuit and Hyper) connected by an adjunction.

**Hasegawa:** Distinguishes `letrec`-calculus (unrestricted) from `vletrec`-calculus (value-restricted), modeling different sharing semantics.

**Circuits:** Makes the same distinction through the notion that the feedbacking element is a `Trace` instance—costrong functors that preserve structure in parallel `(,)` vs taking turns `Either`.

---

## Why Hasegawa Matters for Circuits

**1. The adjunction justifies the axioms**

The fundamental axiom `lower . lift = id` forces `run (lift f) = fix f` to hold [see: other/narrative-arc.md]. Hasegawa's fixed-point machinery is a side-quest—interesting mathematically but not constitutive.

**2. The sliding axiom is structural, not ad-hoc**

The Mendler case isn't a clever workaround. Hasegawa shows it's the operational interpretation of a fundamental trace axiom. When someone asks "why that pattern match?", you point to the sliding axiom and say "this enforces naturality in X."

**3. Traces are more general than feedback loops**

Hasegawa shows traces arise whenever you have:
- Cyclic sharing in implementations
- Fixed-point operators in domain theory
- Non-deterministic semantics over relations
- Higher-order reflexive action calculi

Circuit becomes a lingua franca for all these cases because it's the free traced structure.

**4. The Hyper adjunction is the final encoding**

Hasegawa doesn't explicitly construct final coalgebras, but his framework predicts them. Your Church encoding `Hyper` is exactly what his abstract machinery allows. The triangle identity `lower . toHyper = lower` is the unique map property of free objects.

**5. Cartesian vs cochoice is operationally consequential**

Hasegawa's distinction between cartesian traces (fixed points directly) and computational traces (via adjunction) explains why `Costrong (,)` and `Cochoice Either` are fundamentally different:

- **Costrong:** Both sides progress in lock-step. Hasegawa's traces.
- **Cochoice:** Sequential handoff. Hasegawa's computational traces with asymmetric sharing.

---

## What Hasegawa Would Say About the Arc

"You've built the constructive proof that the free traced monoidal category exists."

He assumes it. You construct it. He proves theorems about it. Your code *is* his theorem.

The arc should note: *"Theorem 3.1 (Hasegawa 1997) proves why the adjunction `lower . lift = id` forces traces and fixed points to coincide in cartesian structure. The sliding axiom is operationalized as a pattern match in `lower`."*
