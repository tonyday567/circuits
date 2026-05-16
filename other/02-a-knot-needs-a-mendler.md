# A Knot Needs a Mendler

**Summary:** In which a sixth axiom forces a third constructor, a naive
interpreter nearly takes us in, and a single pattern match saves everything
from degeneracy.
**Prev:** [01-marks-and-stacks.md](01-marks-and-stacks.md) | **Next:** [03-hyper-buries-the-knot.md](03-hyper-buries-the-knot.md)

---

The six axioms from [Section 1](01-marks-and-stacks.md) determine a GADT exactly.
Three constructors, no more. `Circuit arr t a b` is the resulting **initial
object** in the category of traced monoidal categories over the base arrow
`arr` with tensor `t`. This section derives the construction, shows why
a naive interpreter fails, and explains what the universal property means.

---

## The GADT Falls Out of the Axioms

Axioms 1–3 (associativity, identity, functoriality of lift) require a free
category. That is just two constructors:

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
```

axiom 4 (`↘ . ↑ = id`) is a constraint on interpretation — it introduces
no new constructor.

Axiom 5 (centrality — lifted arrows slide past anything) holds automatically
when the tensor `t` is symmetric. No new constructor.

**Axiom 6 alone forces the third constructor.**

Substituting `f ⊲ p = ↑ f ⊙ p` and `⥁ = fix . ↓` into axiom 6:

```
↘ ((↑ f ⊙ p) ⊙ q) = f . ↘ (q ⊙ p)
```

The right-hand side swaps `p` and `q`. This is not reassociation — it is a
genuine swap. A free category built from `Lift` and `Compose` alone cannot
produce a swap; composition is directional. To model this swap, a new
constructor is needed that carries an explicit feedback channel — one that
can be slid across composition.

That constructor is `Knot`:

```haskell
Knot :: arr (t a b) (t a c) -> Circuit arr t b c
```

`Knot` wraps an arrow over a tensor `t`, making the channel type explicit.
The tensor `t` is what allows the swap. The `Trace` typeclass provides the
operations on `t`:

```haskell
class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c   -- close the channel
  untrace :: arr b c -> arr (t a b) (t a c)   -- inject into channel
```

The full GADT with its categorical roles:

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  Knot    :: arr (t a b) (t a c) -> Circuit arr t b c
```

| Constructor | Structure | Role |
|-------------|-----------|------|
| `Lift` | Strict monoidal functor | Embed base arrows; ↑ of the free/forgetful adjunction |
| `Compose` | Category laws | Sequential composition; associativity and identity |
| `Knot` | Trace | Open a feedback channel; the trace constructor |

The `Category` instance is immediate:

```haskell
instance (Category arr) => Category (Circuit arr t) where
  id  = Lift id
  (.) = Compose
```

### Why Three and No More

The three constructors cover exactly the three structural roles:

| Constructor | Axioms | Role |
|-------------|--------|------|
| `Lift` | 2, 3 | Embed base arrows; free category unit |
| `Compose` | 1 | Sequential composition |
| `Knot` | 6 | Feedback channel; traced structure |

Adding a `Push` constructor (`Compose . Lift`) would be redundant — it is
already a compound term. Adding a `Curry` constructor would give a closed
monoidal category, which is strictly more than traced. The GADT is minimal
for traced monoidal categories.

The `Trace` typeclass is separate from the GADT because the choice of tensor
`t` is not fixed by the axioms — it is a parameter. The GADT is generic over
`t`; the `Trace` instances for `(,)` and `Either` are concrete choices.
See [04-holding-hands-or-taking-turns.md](04-holding-hands-or-taking-turns.md).

---

## The Naive Interpreter

A first attempt at interpretation follows the GADT structure directly:

```haskell
lower (Lift f)      = f
lower (Compose f g) = lower f . lower g
lower (Knot k)      = trace k
```

This compiles. The Fibonacci example runs correctly. It is easy to believe
this is complete.

It is not. Substituting `f ⊲ p = ↑ f ⊙ p` into axiom 6, the LHS reduces to:

```
reify (Compose (↑ f) (Compose p q)) = f . reify p . reify q
```

The RHS:

```
f . reify (Compose q p) = f . reify q . reify p
```

These are equal only if `reify p` and `reify q` commute. In general they do not.

The naive interpreter fails axiom 6. The Fibonacci example did not catch this
because it has no `Compose` wrapping a `Knot` on the left. That structure only
surfaces when something is composed *after* a feedback loop.

---

## The Fault Line: Knot on the Left

When a `Knot` appears on the left of a `Compose`, the naive interpreter applies
`trace k` immediately and then composes. But axiom 6 requires the right-hand
morphism to participate *inside* the trace — to be threaded through `untrace`
before `trace` closes the loop.

The naive interpreter gives:

```
reify (Compose (Knot f) g) = ↪ f . reify g    -- WRONG
```

Axiom 6 requires:

```
reify (Compose (Knot f) g) = ↪ (f . ↩ (reify g))    -- CORRECT
```

The difference: in the correct version, `reify g` is threaded into the
feedback channel via `untrace` on every pass. In the naive version it is
applied once at entry.

For `(,)`, `untrace = second`. The two versions give the same answer when
the loop terminates in one step; they diverge when it iterates. For `Either`,
`untrace = fmap` on `Right`, and the two versions produce different results
even on the first iteration.

---

## The Mendler Case

The fix is one extra pattern match, inserted before the general `Compose` case:

```haskell
reify :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
reify (Lift f)             = f
reify (Compose (Knot f) g) = ↪ (f . ↩ (reify g))   -- Mendler case
reify (Compose f g)        = reify f . reify g
reify (Knot k)             = ↪ k
```

The order is load-bearing. Without the `Compose (Knot f) g` case appearing
before the general `Compose` case, the pattern falls through and produces the
naive — incorrect — behaviour.

Each case corresponds to one axiom:

| Case | Axiom | What it does |
|------|-------|--------------|
| `Lift f` | `↘ . ↑ = id` | Faithful embedding; returns the base arrow unchanged |
| `Compose f g` | Associativity | Composes the two interpretations |
| `Knot k` | `↘ (↮ k) = ↪ k` | Closes the feedback channel via `trace` |
| `Compose (Knot f) g` | **Sliding** | Threads `reify g` into the channel via `↩` before tracing |

This is the **Mendler algebra step**: inspecting one syntactic layer before
recursing. The Mendler case converts a structural observation into an
operational guarantee: when a `Knot` appears at the head of a composition,
the trailing morphism is wired into the feedback channel before the trace
closes.

Without this case, `Knot` becomes observationally equivalent to
`↑ (↪ k)` — the feedback channel closes immediately, the loop
structure is lost, and `Circuit` collapses to the free category with a
fixed-point operator. This is the **degenerate model** that the 2013 paper
warns about.

---

## The Traced Monoidal Axioms

`Circuit` satisfies all five traced monoidal axioms (Joyal, Street & Verity
1996). Detailed proofs for both tensors `(,)` and `Either` are in
[axioms.md](axioms.md). The key structural points:

**Naturality (sliding).** The Mendler case enforces:

```
↪ (f . ↩ g) = ↪ f . g
```

This is the sliding axiom: a morphism composed on the output of a trace can
be moved inside. The Mendler case reifies this as a pattern match — when a
`Knot` appears at the head of a `Compose`, the right morphism is injected
into the channel via `↩` before `↪` closes it.

**Vanishing I.** `Knot (id ⊗ id) = id`. The identity feedback channel is
trivial.

**Superposing.** Tensor distributes over trace as expected.

**Yanking.** In the cartesian case (`arr = (->)`, `t = (,)`), Hasegawa's
Theorem 3.1 gives `⥁ (↑ f) = fix f` as a derived consequence. The
trace and fixed-point operator coincide. See [the Hasegawa
section](#hasegawa-recursion-from-cyclic-sharing) below.

---

## The Universal Property (Initiality)

`Circuit arr t` is the **initial** (free) traced monoidal category over
`arr`. The universal property:

> For any traced monoidal category `C` and any (traced) functor
> `F : arr -> C`, there is a **unique** traced functor
> `F̂ : Circuit arr t -> C` making the triangle commute:
>
> ```
>     Lift
> arr -----> Circuit arr t
>  \               |
>   \          F̂  |
>    \             ↓
>     F ---------> C
> ```

`reify` is the instance of this universal property where `C = arr` and
`F = id`. It is the unique traced functor from the free object back to the
base.

Every traced functor out of `Circuit arr t` factors through `reify`. This
is why `Circuit` is useful: **you build in `Circuit`, and any target traced
category interprets it via `reify`**.

---

## Hasegawa: Recursion from Cyclic Sharing

Hasegawa (1997) asks what recursion is operationally: implementations use cyclic
data structures — self-referential environments, cyclic graphs — to achieve
recursion efficiently. This is semantically different from applying a fixed-point
combinator, even though both produce recursion. His framework uses traced
monoidal categories (Joyal, Street & Verity) to model cyclic sharing formally,
and proves **Theorem 3.1**: in a cartesian traced category, traces and
fixed-point operators are in bijection. The trace IS the fixed point.

Hasegawa's framework assumes traced monoidal categories exist and have nice
properties. Circuit *constructs* the free one: the GADT with `Lift`, `Compose`,
and `Knot` is exactly the object his framework presupposes. He proves theorems
about it; this library is a constructive proof that it exists.

**Where they meet.** Theorem 3.1 is why `⥁ (↑ f) = fix f` holds in the
cartesian case — not as an axiom, but as a consequence of the adjunction
`↘ . ↑ = id` plus the cartesian trace. What Hasegawa derives from
semantic models, circuits derives from the GADT construction.

**Where they diverge.** Hasegawa distinguishes `letrec` (unrestricted sharing)
from `vletrec` (value-restricted sharing) to model different operational
semantics. Circuits makes the same distinction through tensor choice:
`(,)` gives parallel, lock-step sharing (Costrong); `Either` gives sequential,
taking-turns handoff (Cochoice). Hasegawa states these as separate semantic
models; circuits captures both as `Trace` instances over the same GADT.

**The sliding axiom.** In Hasegawa's framework, sliding is a naturality
condition on the trace. In circuits, it is a pattern match — the Mendler case
in `reify`. A categorical requirement becomes an operational guarantee: the
pattern match enforces that a `Knot` on the left of `Compose` threads the
right morphism through `↩` before the trace closes. See `05-no-remorse-once-removed.md` for
the Reflection Without Remorse connection.

---

## The Two Adjunctions

The library's structure comes from two adjunctions and the sliding axiom:

### Adjunction 1: Free / Forgetful

```
↑     :: arr a b -> Circuit arr t a b     ← left adjoint (free)
reify :: Circuit arr t a b -> arr a b     ← right adjoint (forgetful)
↘ . ↑  =  id                              ← unit-counit triangle
```

Axioms derivable from this adjunction:

```
↑ (f . g) = ↑ f ⊙ ↑ g        (Lift is functorial)
↑ id = id                    (Lift preserves identity)
(f ⊙ g) ⊙ h = f ⊙ (g ⊙ h)   (Compose is associative)
```

### Adjunction 2: Initial / Final (Galois connection)

```
encode :: Circuit (->) (,) a b -> Hyper a b
flatten :: Hyper a b -> Circuit (->) (,) a b
↓ . encode = ↘                              -- triangle identity
```

This is a Galois connection, not a strict adjunction. The asymmetry is real:
Circuit is intensional (you can inspect the constructors), Hyper is extensional
(you can only observe behaviour). See [03-hyper-buries-the-knot.md](03-hyper-buries-the-knot.md).

### The Sliding Axiom: Not an Adjunction Property

The Mendler case is the one ingredient that is **not** a consequence of
adjunctions:

```haskell
reify (Compose (Knot f) g) = ↪ (f . ↩ (reify g))
```

This is a genuine strength/costrength operation on the profunctor, not
derivable from free or initial-final properties. It is what makes the trace
honest. Without it, both adjunctions are in place but the traced structure
collapses.

---

## Ruling Out the Degenerate Model

Without the Mendler case, `Circuit` is the **free category with a fixed-point
operator** — a weaker structure. The degenerate model is `a -> b`,
with `Compose` as function composition and `↑ = id`. In this model,
`↮ k = ↪ k` immediately — the feedback channel never iterates.

The Mendler case rules this out by ensuring that when a `Knot` appears on the
left of a `Compose`, the right morphism participates in every iteration of the
feedback. The loop structure is preserved through composition.

**One pattern match separates the free traced monoidal category from the
degenerate model.**

---

## The Historical Path

The abstraction came last. The actual path was:

1. Axiom 6 has a hidden channel implicit in how `⥁` ties the knot.
2. Costrength suggested naming the channel as an explicit tensor `t`.
3. `Knot :: arr (t a b) (t a c) -> Circuit arr t b c` was a guess.
4. The Mendler case was added to make the types line up.
5. What fell out was recognised as a free traced monoidal category.

"Free traced monoidal category", the sliding axiom, and the `Trace` typeclass
are the retrospective description of what the construction turned out to be —
not the design principle.

---

## Summary

```
↘ (↑ f)         =  f                           -- faithful embedding
↘ (↮ k)         =  ↪ k                         -- trace closes the channel
↘ (↮ f ⊙ g)    =  ↪ (f . ↩ (↘ g))             -- Mendler case (sliding)
↘ (f ⊙ g)      =  ↘ f . ↘ g                    -- functoriality of ↘
```

Circuit is the free object. `reify` is the unique elimination. The Mendler
case is the content. Everything else follows.

**Next:** [03-hyper-buries-the-knot.md](03-hyper-buries-the-knot.md) — Hyper as the final encoding; the
coinductive type; why sliding is structural there.

---

## References

- Launchbury, Krstic & Sauerwein (2013) — axioms and the degenerate model
- Joyal, Street & Verity (1996) — traced monoidal categories; axioms
- Hasegawa (1997) — fixed points from traces; cartesian case
- [axioms.md](axioms.md) — proofs for all five axioms; connection to LKS hyperfunction axioms
