# Hyp and TracedA: The Bridge

**Sources:** LKS (Launchbury, Krstic & Sauerwein 2013), Kidney-Wu 2026, JSV (Joyal, Street & Verity 1996), Hasegawa 1997

---

## The claim

`Hyp` and `TracedA` are the same structure arrived at from opposite directions.

- LKS started from streams and coroutines, derived seven axioms, and found a feedback constructor was needed.
- The categorical approach starts from traced monoidal category axioms and arrives at the same three GADT constructors.
- They meet at: **Axiom 7 = Sliding = Knot**.

---

## Operator dictionary

| LKS 2013       | Kidney-Wu 2026 | TracedA          | Role                        |
|----------------|----------------|------------------|-----------------------------|
| `f # g`        | `f ⊙ g`        | `Compose f g`    | Sequential composition      |
| `lift f`       | `rep f`        | `Lift f`         | Embed base arrow            |
| `f << h`       | `f ⊲ h`        | `Compose (Lift f) h` | Prepend function        |
| `run`          | `run`          | `run`            | Eliminate / tie knot        |
| _(implicit)_   | _(implicit)_   | `Knot k`         | Feedback constructor        |
| `lower`        | `lower`        | `run`            | Interpret to base arrow     |

`<<` is not primitive: `f << h = Compose (Lift f) h`. Axiom 6 (`lift f = f << lift f`) is then the coinductive unrolling of `Lift` under `Compose`.

---

## Axiom correspondence

JSV work in a balanced monoidal category (braids, twists). Hasegawa and LKS both specialise to symmetric monoidal categories. The narrative lives in the symmetric/cartesian case throughout; Hasegawa's specialisation is the right landing point.

| LKS Axiom | JSV / Hasegawa counterpart | TracedA location | Notes |
|-----------|---------------------------|------------------|-------|
| 1: `(f # g) # h = f # (g # h)` | Monoidal associativity | `Category` instance | Pre-condition, not a trace axiom |
| 2: `f # self = f = self # f` | Monoidal unit / Vanishing I | `Lift id` | `self = lift id` is identity |
| 3: `lift (f . g) = lift f # lift g` | Functor law for embedding | `Lift` | Strict monoidal functor |
| 4: `run (lift f) = fix f` | Yanking (cartesian specialisation) | `run (Knot ...)` | In cartesian case, trace induces `fix` |
| 5: `(f << p) # (g << q) = (f.g) << (p # q)` | Superposing | `Compose` + `Lift` | `<<` encodes feedback channel |
| 6: `lift f = f << lift f` | Vanishing II / coinductive unfolding | `Lift` under `Compose` | Loop unrolling as `Tr^{XxY} = Tr^X . Tr^Y` |
| 7: `run ((f << p) # q) = f (run (q # p))` | **Sliding** (Left Tightening) | `run (Compose (Knot f) g)` | The core axiom; demands `Knot` |

JSV derives naturality from the natural family structure. Hasegawa makes it explicit as Left and Right Tightening. nLab names all five: vanishing I, vanishing II, superposing, yanking, naturality. LKS Axiom 7 is the sliding/naturality axiom in the concrete hyperfunction setting.

**What the 2013 presentation omits:** Vanishing I is absorbed into Axiom 2 via `self`. Right Tightening is not stated separately. The 2013 presentation is more economical, trading categorical generality for a Haskell-friendly form.

---

## Axiom 7 is the sliding axiom is Knot

The restated Axiom 7 (factoring out `fix` via `run = fix . lower`):

```
lower ((f << p) # q) = f . lower (q # p)
```

Expanding with `f << p = Compose (Lift f) p` and `# = Compose`:

```
lower (Compose (Compose (Lift f) p) q) = f . lower (Compose q p)
```

LHS reduces to `f . lower p . lower q`.
RHS reduces to `f . lower q . lower p`.

These are equal only when the feedback channel is existentially hidden inside a knot — when `lower p` and `lower q` share a cyclic state `s` that routes through `unfirst`. This is exactly `Knot`:

```haskell
Knot :: arr (t a b) (t a c) -> TracedA arr t b c
run (Knot k) = trace k
run (Compose (Knot f) g) = trace (f . untrace (run g))   -- sliding rule
```

The sliding rule in `run` is Axiom 7 made computational. Without `Knot`, the free category built from `Lift` and `Compose` alone cannot satisfy Axiom 7 — it has no feedback, and `lower p . lower q` never commutes with `lower q . lower p` in general.

---

## toHyp is the homomorphism

```haskell
toHyp :: Traced a b -> Hyp a b
toHyp (Lift f)      = rep f
toHyp (Compose f g) = toHyp f ⊙ toHyp g
toHyp (Knot k)      = trace (rep k)
```

`Lift` and `Compose` map trivially. `Knot` maps to `trace . rep` — lift the base arrow into `Hyp` and apply the trace immediately. This is where the feedback is consumed. `toHyp` is a homomorphism because `Hyp` already satisfies all the traced axioms; the sliding rule does not need to be re-enforced.

`Hyp` is a model of `TracedA` where `trace` and `run` collapse into one operation. In `TracedA` they are distinct: `run` is the interpreter, `trace` is the categorical operation. In `Hyp`, the self-referential definition `run h = ι h (HypA run)` means they are the same.

---

## The tensor is a parameter

`TracedA arr t a b` abstracts over the tensor `t`. Both instances give valid traced categories and both support `toHyp`:

| Tensor `t` | `trace`    | Operational character        | Categorical name |
|------------|------------|------------------------------|------------------|
| `(,)`      | `unsecond` | Lazy product knot; simultaneous | Costrong / coinductive |
| `Either`   | `unright`  | While-loop; sequential handoff | Cochoice / inductive  |

`Hyp` is neutral to this choice — the feedback channel type does not appear in the `Hyp` newtype. `toHyp` works for both tensors.

---

## Hasegawa's cartesian specialisation

In a cartesian traced category, Hasegawa's Theorem 3.1 establishes that the trace is equivalent to a fixed-point operator satisfying the Conway axioms. This is why `run (lift f) = fix f` (LKS Axiom 4) is not an arbitrary choice — in the cartesian setting, any trace necessarily induces `fix`. The connection is a theorem, not a definition.

Hasegawa also separates cyclic sharing (the trace) from fixed-point combinators: they agree extensionally but differ operationally. The fixed-point combinator can cause resource duplication in sharing-based implementations; the trace does not. This maps onto the `Costrong` vs `Cochoice` distinction: not just a design preference but a semantic difference with operational consequences.

---

## Open questions

- The precise isomorphism between `Proxy`/`streaming` types and `TracedA` is not established.
- The Geometry of Interaction connection (Int(C) completion, `callCC`, shift/reset) is a conjecture not yet developed.
- The graded structure counting `Knot` depth and its implications for Okasaki queue methods are noted but not formalised.
- Kidney-Wu 2026: specific examples (breadth-first search via Hofmann, concurrency scheduler) mapping onto `TracedA`/`HypA` would strengthen "hyperfunctions are traced catamorphisms."
