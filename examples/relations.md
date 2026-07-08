# relations — circuits over Rel

> **Design-only / exploratory.** `Rel` is not an implemented base arrow in the
> current library; this card explores what a relational semantics would look
> like.

**Context:** What happens when `arr = Rel` instead of `(->)` or `Kleisli IO`?
The human disappears from the categorical diagram. Every agent — human,
language model, or otherwise — is just a relation that produces sensible
tokens on demand. Correctness becomes behavioral equivalence (bisimulation),
not containment in a human ground-truth path.

```haskell
-- $setup
-- >>> import Control.Category
-- >>> import Circuit (Trace(..), run)
-- >>> import Prelude hiding (id, (.))
```

---

## the shift

The categorical-analysis paper has two routes:

```
Human:  H --c--> C --g--> Pred(W)
AI:     H --p--> C' --i_g0--> G × C' --e--> O --r--> Pred(W)
```

The AI route must be *contained in* the human route:
`(r ∘ e ∘ i_g0 ∘ p)(h) ⊆ (g ∘ c)(h)`.

Drop the human. Both routes are just agents. The question is not "does
agent A match the human?" but "do agent A and agent B behave the same?"

In `Rel`, behavioral equivalence is **bisimulation**: two relations are
the same if they relate the same inputs to the same outputs, regardless of
internal structure.

---

## why Rel

`Rel` is the category of sets and relations.

- **Objects:** sets
- **Morphisms:** `R : A → B` is a subset `R ⊆ A × B`
- **Composition:** relational composition
- **Identity:** diagonal relation

`Rel` is **compact closed** (self-dual). Every relation has a converse.
The cap and cup are diagonal relations:

```haskell
-- Cap η_X : 1 → X × X
-- Cup ε_X : X × X → 1
-- Both are {(x, x) | x ∈ X} in appropriate direction
```

This means `Traced Rel (,)` is uniform — no `MonadFix`, no `prompt`/`control0`.
The trace of `R : X × A → X × B` is:

```
tr(R) = {(a, b) | ∃x. (x, a, x, b) ∈ R}
```

Feedback is: *find a self-consistent context `x` such that the relation holds.*

---

## Trace t Rel a b

`Trace` is parametric in `arr`. Instantiating to `Rel`:

```haskell
-- Arr embeds a relation
-- Sequential composition is (.) or (>>>)
-- Knot creates feedback over relations
```

**`Trace (,) Rel a b`** — non-deterministic feedback.
The `Knot` body is a relation `(X × A) → (X × B)`. `run` finds a
self-consistent `x`. The same input can relate to many outputs.

**`Trace Either Rel a b`** — iterative branching.
`Left` carries state forward, `Right` terminates. The agent iterates
until it finds a response it is satisfied with.

Both tensors work in `Rel` because `Rel` is a traced biproduct category
for `Either` and compact closed for `(,)`.

---

## the drift problem

> "What context makes the response self-consistent?"

Agents do this all the time. A language model iterates internally until
its output coheres with its own context. A human ruminates until their
position feels consistent. Both are `Knot` over `Rel` seeking self-consistent
fixed points.

The risk: **self-consistency is not truth**. An agent can converge to a
stable fixed point that is internally coherent but externally false.
Bisimulation guarantees behavioral equivalence *between agents*, not
veridicality *with respect to the world*.

In `Rel`, there is no morphism `ρ : Pred(W) → W` that resolves propositions
to actual worlds. The category of relations has no preferred grounding.
Drift is structural.

---

## what we do not know

- Does `run :: Trace t Rel a b -> Rel a b` have a clean Haskell
  implementation? The `Traced Rel (,)` instance is geometric, but the
  `Knot` GADT expects `arr (t s a) (t s b)` — a relation, not a function.

- How do `Producer`/`Consumer` behave when `arr = Rel`? The companion
  and conjoint in `Rel` are relation converse. The `forall x` quantification
  in `Producer`/`Consumer` may collapse differently.

- Is there a useful `Hyper` for `Rel`? `Hyper` is defined only for `(->)`.
  A `Hyper` over `Rel` would need to encode the self-dual continuation
  as a relation, not a function.

- Can we define a *metric* on `Trace t Rel a b` that measures distance
  from behavioral equivalence? This would give us a notion of "almost
  the same agent" rather than exact bisimulation.

---

## references

- `other/03-hyper-buries-the-knot.md` — Kan extension characterization
- `loom/ends-effectful.md` — effectful comparison, bracketing gap
- Floridi et al. (2025) — categorical analysis of LLMs in `Rel`
- Baltieri et al. (2025) — coalgebraic predictive processing, bisimulation
- Zhang et al. (2024) — Diagram of Thought, slice topos
