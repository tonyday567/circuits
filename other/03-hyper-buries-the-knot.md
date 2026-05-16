# Hyper Buries the Knot

**Summary:** In which the knot dissolves into the type itself, sliding
becomes structural, and we discover that Hyper was a Kan extension all along.
**Prev:** [02-a-knot-recovers-fix.md](02-a-knot-recovers-fix.md) | **Next:** [04-holding-hands-or-taking-turns.md](04-holding-hands-or-taking-turns.md)

---

`Circuit` is the initial encoding — a syntax tree. `Hyper` is the final encoding — a coinductive type. They represent the same mathematical object via different encodings. The triangle identity connects them.

---

## The Type

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

Unfolding the recursion, the type expands to an infinitely-nested structure:

```
Hyper a b = (((...  → a) → b) → a) → b
```

The self-referential duality is built in: to produce a `b`, you invoke the dual `Hyper b a`. This captures the essential pattern of continuations that communicate with their own continuations.

---

## Composition

```haskell
instance Category Hyper where
  id    = lift id
  f . g = Hyper $ \h -> invoke f (g . h)
```

The backwards channel `h :: Hyper b a` is where the feedback lives. In `Circuit`, a `Knot` explicitly opens a feedback channel. In `Hyper`, every morphism already has one — the continuation argument `Hyper b a` is structurally present in every value. **`Knot` does not go anywhere; it dissolves into the type.**

---

## The Key Operations

```haskell
lift  :: (a -> b) -> Hyper a b
lower :: Hyper a b -> (a -> b)
run   :: Hyper a a -> a
push  :: (a -> b) -> Hyper a b -> Hyper a b
```

- **lift** embeds a plain function: `lift f = push f (lift f)` — coinductive unrolling
- **lower** observes a hyperfunction by supplying a constant continuation
- **run** ties the knot on the diagonal: `run = fix . lower`
- **push** prepends a function to the continuation stack: `push f h = lift f . h`

---

## The Triangle Identity

The map from initial to final:

```haskell
encode :: Circuit (->) (,) a b -> Hyper a b
encode (Lift f)      = lift f
encode (Compose f g) = encode f . encode g
encode (Knot f)      = trace (lift f)            -- Hyper's Trace instance
```

The `Knot` case uses `Hyper`'s own `Trace (,)` instance — a coinductive lazy knot
that preserves the feedback structure inside `Hyper`. This is *not* flattening:
the knot lives on in `Hyper`'s continuation structure rather than being
eliminated to a plain function.

`encode` does not need a Mendler case. The `Compose (Knot f) g` pattern reduces
through the general `Compose` case — `Hyper`'s `Category` instance threads the
continuation on every composition step, so the feedback channel is always at the
head of the structure.

Compare to `reify` on `Circuit`, which applies `↩` explicitly:

```
↘ (Compose (Knot f) g) = ↪ (f . ↩ (↘ g))
```

The two agree through the sliding axiom. Expanding `lower . encode` on the same term:

```
↓ (encode (Compose (Knot f) g))
  = ↓ (encode (Knot f) . encode g)
  = ↓ (↪ (↑ f) . encode g)                      -- Hyper's trace
  = ↓ (↪ (↑ f)) . ↓ (encode g)                  -- lower is a functor
  = ↪ f . ↓ g                                    -- unit law + induction
  = ↪ (f . ↩ (↓ g))                              -- sliding axiom
  = ↘ (Compose (Knot f) g)
```

**Triangle:** `↓ . encode = ↘` (on `Circuit`).

Mapping `Circuit` into `Hyper` and then observing gives the same result as
running `Circuit` directly. The sliding axiom closes the triangle. `Hyper`'s
own `Trace` instance is the bridge — it ties the coinductive knot that `Knot`
represents, so the feedback structure survives the mapping.

---

## Sliding is Structural in Hyper

In `Circuit`, the sliding axiom must be enforced by the Mendler case — an explicit pattern match. In `Hyper` it is inherent in composition:

```haskell
f . g = Hyper $ \h -> invoke f (g . h)
```

The continuation `h` is threaded through `g . h` before `invoke f` sees it, on every unfolding. This is exactly the work `untrace = fmap` does in `Circuit` — but structural rather than operational. **There is no degenerate model to fall into because the type itself encodes the feedback structure.**

---

## The Kan Extension Characterization

There is an equivalent formulation via right Kan extensions (Icelandjack). For constant functors `Const a` and `Const b`:

```
Ran (Const a) (Const b) x  ≅  ∀c. (x → a) → b
```

Applying `Fix` to collapse this:

```
Fix (Ran (Const a) (Const b))
  ≅ (x → Fix (Ran (Const a) (Const b))) → b
  ≅ Hyper a b
```

So: **`Hyper a b  ≅  Fix (Ran (Const a) (Const b))`**

This characterization explains *why* the self-duality emerges (from the continuation structure locked into the Ran form plus the fixpoint), while the direct definition shows the computational form. Both are final coalgebras with observably identical behaviour; they are coinductively equivalent.

Before the fixpoint, `Circuit a b` is related to the Ran of the free category:

```
Circuit a b  ~  Ran (Const a) (Const b)    (before Fix)
```

Adding the trace (`Knot`) requires tying the knot with `Fix`:

```
Hyper a b  =  Fix (Ran (Const a) (Const b))
```

`reify` is then a left Kan extension — the universal traced functor extending the embedding `arr → Circuit arr t` along the trace structure.

Four consequences fall out of this characterization:

- **Hyper is the codensity representation of Circuit** — it encodes the feedback channel structurally rather than as an explicit constructor.
- **Sliding is free** — the axiom that traces slide across compositions holds automatically in Hyper because the continuation threads through every layer.
- **The Mendler case enforces naturality** — without the pattern match `reify (Compose (Knot f) g) = ↪ (f . ↩ (reify g))`, the universal property is violated and Knot collapses to the degenerate model.
- **Coinductive semantics** — the recursive Hyper definition is coinductively sound. We don't need strict proof that `Fix (Ran ...)` is isomorphic to Hyper — only that they observe the same.

---

## Initial vs Final: A Comparison

|                | `Circuit`                         | `Hyper`                       |
|----------------|-----------------------------------|-------------------------------|
| Encoding       | Initial (syntax)                  | Final (semantics)             |
| Sliding        | Enforced by Mendler case          | Inherent in `(.)`             |
| Feedback       | Explicit `Knot` constructor       | Structural in `Hyper` type    |
| Degenerate model | Possible without Mendler case   | Not possible                  |
| Elimination    | `reify` / `↘`                     | `lower` / `↓`                |
| Map to other   | `encode` / `⇨` (Circuit → Hyper) | `flatten` / `⇦` (Hyper → Circuit) |
| Inspection     | Constructors visible              | Opaque; only observable       |
| Composition    | O(n²) left-nested                 | O(1) amortised                |

---

## The Forgetful Map

The reverse direction:

```haskell
flatten :: Hyper a b -> Circuit (->) (,) a b
flatten h = Lift (lower h)
```

`lower` observes the hyperfunction against a constant continuation, collapsing it to a plain function. All feedback structure is lost. `flatten` is not an inverse to `encode` — it is the observation that `Hyper` can only be seen from the outside.

This asymmetry is real: Circuit is intensional (constructors are inspectable), Hyper is extensional (only behaviour is accessible). The two encodings are not isomorphic on the nose. The triangle `↓ . encode = ↘` holds, but `⇨ . ⇦ ≠ id` in general.

---

## When to Use Each

**Use Circuit when:**
- Building and inspecting structure
- Static analysis of feedback topology
- Composing sub-circuits before running
- You need the constructors to be visible

**Use Hyper when:**
- Running / eliminating the circuit
- Performance matters (left-nested composition)
- The sliding axiom needs to be guaranteed structurally
- You want the semantics without the syntax

The typical pattern: **build in Circuit, run via Hyper**.

---

## Summary

`Hyper` is `Circuit` with the syntax erased. The feedback channel that `Knot` makes explicit in `Circuit` dissolves into the type of `Hyper`. The sliding axiom that the Mendler case enforces in `Circuit` holds structurally in `Hyper`. The triangle `↓ . encode = ↘` connects them.

**Next:** [04-holding-hands-or-taking-turns.md](04-holding-hands-or-taking-turns.md) — the tensor parameter `t`; `(,)` vs `Either`; holding hands vs taking turns.

---

## References

- Launchbury, Krstic & Sauerwein (2013) — hyperfunction definitions and operations
- Kidney & Wu (2026) — modern treatment; producer-consumer insight
- Icelandjack — Ran characterization; `Fix (Ran (Const a) (Const b))`
- [axioms.md](../other/axioms.md) — axioms and triangle identity
