# Hyper Buries the Knot

<div align="center">

✦ · ✧ · ✦

*In which we dissolve knots into hyperfunctions; slide until yanked; and extend the Kan way.*

**[⟵ Prev: A Knot Recovers Fix](02-a-knot-recovers-fix.md)** · **[Next: Holding Hands or Taking Turns ⟶](04-holding-hands-or-taking-turns.md)**

</div>

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
- **run** ties the knot on the diagonal: `run h = invoke h (Hyper run)`. On the image of `lift`, this coincides with the classical fixed point: `run (lift f) = fix f`. For arbitrary elements of the final coalgebra, `run` is the primitive operation.
- **push** prepends a function to the continuation stack.

---

## The Triangle Identity

The map from initial to final:

```haskell
encode :: Circuit (->) (,) a b -> Hyper a b
encode (Lift f)      = lift f
encode (Compose f g) = encode f . encode g
encode (Knot f)      = trace (lift f)            -- Hyper's Trace instance
```

The `Knot` case uses `Hyper`'s own `Trace (,)` instance — a coinductive lazy
knot that preserves the feedback structure inside `Hyper`. This is *not*
flattening: the knot lives on in `Hyper`'s continuation structure rather than
being eliminated to a plain function.

**Triangle:** `↓ . encode = reify` (on `Circuit`).

We prove each case.

**`Lift`:**

```
↓ (encode (Lift f)) b
  = ↓ (lift f) b
  = invoke (lift f) (Hyper (const b))         -- definition of lower
  = invoke (push f (lift f)) (Hyper (const b))  -- lift f = push f (lift f)
  = f (invoke (Hyper (const b)) (lift f))       -- push f h = Hyper (\k -> f (invoke k h))
  = f b                                          -- Hyper (const b) ignores argument
  = reify (Lift f) b
```

**`Compose`:** By induction, `↓ (encode f) = reify f` and `↓ (encode g) = reify g`.

```
↓ (encode (Compose f g)) b
  = ↓ (encode f . encode g) b
  = invoke (encode f . encode g) (Hyper (const b))
  = invoke (Hyper $ \h -> invoke (encode f) (encode g . h)) (Hyper (const b))
  = invoke (encode f) (encode g . Hyper (const b))
  = ↓ (encode f) (↓ (encode g) b)              -- lower threads through composition
  = reify f (reify g b)
  = reify (Compose f g) b
```

**`Knot`:** This is the case the previous version skipped. Expand
`trace (lift f)` using the `Trace Hyper (,)` instance:

```haskell
trace body = Hyper $ \k ->
  let pair = invoke body cont
      cont = Hyper $ \_ ->
        let a_val = invoke k (Hyper (const (snd pair)))
         in (fst pair, a_val)
   in snd pair
```

Substituting `body = lift f = push f (lift f)`:

```
pair = invoke (push f (lift f)) cont
  = f (invoke cont (lift f))            -- push f h = Hyper (\k -> f (invoke k h))
  = f (fst pair, a_val)                 -- cont ignores its argument (_ -> ...)
```

where `a_val = invoke k (Hyper (const (snd pair)))`.

Now apply `lower` — i.e. supply `k = Hyper (const b)`:

```
a_val = invoke (Hyper (const b)) (Hyper (const (snd pair)))
  = b                                   -- Hyper (const b) ignores its argument
```

So `pair = f (fst pair, b)`. Writing `(a, c) = pair`:

```
(a, c) = f (a, b)                       -- the lazy knot: a feeds back
```

And `snd pair = c`, so:

```
↓ (encode (Knot f)) b
  = ↓ (trace (lift f)) b
  = let (a, c) = f (a, b) in c
  = trace f b                           -- Trace (->) (,) instance
  = reify (Knot f) b
```

The `Trace Hyper (,)` instance ties a coinductive knot through `pair` and
`cont`. When `lower` supplies `Hyper (const b)` as the outer continuation,
`a_val` collapses to `b`, the `Hyper`-level self-reference dissolves, and
what remains is exactly the lazy knot of `Trace (->) (,)`.

**`Compose (Knot f) g`:** Follows from the `Compose` case by induction,
using the `Knot` base case just proved. The Mendler case in `reify` and
the `Compose` case in `encode` reach the same result via different paths —
`reify` enforces sliding explicitly via the pattern match; `encode` gets
it structurally from `Hyper`'s `Category` instance threading the continuation.

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

This characterization explains *why* the self-duality emerges (from the continuation structure locked into the Ran form plus the fixpoint), while the direct definition shows the computational form. Both are final coalgebras with observably identical behaviour; they are observationally equivalent.

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
- **The Mendler case enforces naturality** — without the pattern match `reify (Compose (Knot f) g) = trace (f . untrace (reify g))`, the universal property is violated and Knot collapses to the degenerate model.
- **Coinductive semantics** — the recursive Hyper definition is guarded. We don't need strict proof that `Fix (Ran ...)` is isomorphic to Hyper — only that they observe the same.

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

- [Launchbury, Krstic & Sauerwein (2013)](https://doi.org/10.4204/eptcs.129.9) — hyperfunction definitions and operations
- [Kidney & Wu (2026)](https://doi.org/10.1145/3776649) — modern treatment; producer-consumer insight
- Icelandjack — Ran characterization; `Fix (Ran (Const a) (Const b))`
- [axioms.md](../other/axioms.md) — axioms and the commuting triangle
