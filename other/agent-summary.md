# circuits — agent summary

A free traced monoidal category over any base arrow. Two representations:
**Circuit** (initial, inspectable GADT) and **Hyper** (final, coinductive newtype).
Plus a `Trace` typeclass for closing feedback loops over a tensor `t`.

For equational proofs see `axioms-traced.md`. This is the narrative sweep (01–07)
compressed to ~10k chars. Use it to find your place before writing examples.

## The Five Marks

Five operations. Everything else is a consequence:

```
η   lift      embed a plain arrow          (a -> b) -> H a b
ε   lower     observe / eliminate          H a b -> (a -> b)
⊙   compose   sequential composition       H b c -> H a b -> H a c
⊲   push      prepend a plain function     (a -> b) -> H a b -> H a b
⥁   run       tie the knot                 H a a -> a
```

Push and run are compound: `f ⊲ p = η f ⊙ p` and `⥁ = fix . ε`. The irreducible
core is lift, lower, compose.

## The Six Axioms

```
1. (f ⊙ g) ⊙ h  =  f ⊙ (g ⊙ h)           associativity
2. f ⊙ η id     =  f  =  η id ⊙ f          identity
3. η (f . g)    =  η f ⊙ η g                lift is a functor
4. ⥁ (η f)      =  fix f                    run is fixed-point
5. (f ⊲ p) ⊙ (g ⊲ q)  =  (f . g) ⊲ (p ⊙ q) push composition
6. ⥁ ((f ⊲ p) ⊙ q)    =  f (⥁ (q ⊙ p))    feedback / sliding
```

Axioms 4 and 5 introduce no new constructors. Only axiom 6 forces one: `Knot`.

## The GADT (axioms 1–6 → three constructors)

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  Knot    :: arr (t a b) (t a c) -> Circuit arr t b c
```

- **Lift + Compose**: axioms 1–3 → free category over `arr`
- **Knot**: axiom 6 alone → feedback channel with explicit tensor `t`
- Axiom 5 (centrality) holds automatically when `t` is symmetric.

```haskell
class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c   -- close the channel
  untrace :: arr b c -> arr (t a b) (t a c)   -- inject into channel
```

### The Mendler Case

A naive interpreter fails axiom 6. When `Knot` is on the left of `Compose`,
the right morphism must participate *inside* the trace:

```haskell
lower :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
lower (Lift f)             = f
lower (Compose (Knot f) g) = trace (f . untrace (lower g))   -- Mendler case
lower (Compose f g)        = lower f . lower g
lower (Knot k)             = trace k
```

The Mendler case MUST appear before the general `Compose` case. Without it,
`Knot` collapses to `Lift (trace k)` — the **degenerate model** where the
feedback channel never iterates. One pattern match separates a free traced
monoidal category from a free category with a fixpoint operator.

## Circuit: Free Traced Monoidal

`Circuit arr t` is the **initial object** in the category of traced monoidal
categories over `arr`. The universal property: for any traced monoidal `C` and
traced functor `F : arr → C`, there is a unique traced functor `F̂ : Circuit arr t → C`.
`lower` is the instance where `C = arr` and `F = id`.

**Adjunction 1 — Free / Forgetful:** `Lift ⊣ lower`. Gives category structure,
functoriality, most axioms.

**Adjunction 2 — Initial / Final:** `Circuit ↔ Hyper` via `encode` / `⇨` (encode) and `flatten`.
Triangle: `lower . encode = lower`. This is a Galois connection (Circuit is
intensional, Hyper is extensional), not a strict adjunction.

**The sliding axiom** (Mendler case) is the one ingredient not derivable from
adjunctions — a genuine strength/costrength operation on the profunctor.

## Hyper: Final Encoding

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

Self-referential duality built into the type. Key operations:

```haskell
lift  :: (a -> b) -> Hyper a b       -- coinductive unrolling
lower :: Hyper a b -> (a -> b)       -- supply constant continuation
run   :: Hyper a a -> a              -- tie the diagonal knot
push  :: (a -> b) -> Hyper a b -> Hyper a b  -- prepend to stack
```

### encode (encode / ⇨)

```haskell
encode :: Circuit (->) (,) a b -> Hyper a b
encode (Lift f)      = lift f
encode (Compose f g) = encode f . encode g
encode (Knot f)      = trace (lift f)            -- Hyper's Trace instance
```

Uses `Hyper`'s own `Trace (,)` instance — a coinductive lazy knot that preserves
the feedback structure. For `Either`, use `encodeEither` which encodes the loop state
in the function domain.

### Sliding is Structural

In `Circuit`, sliding is enforced by the Mendler case. In `Hyper`, it's inherent:

```haskell
f . g = Hyper $ \h -> invoke f (g . h)
```

The continuation `h` threads through `g . h` before `invoke f` sees it. No
degenerate model is possible — the type itself encodes the feedback.

`Hyper a b ≅ Fix (Ran (Const a) (Const b))`. See `04-hyper.md` for the full Kan characterization.

### Initial vs Final

|                | Circuit                     | Hyper                    |
|----------------|-----------------------------|--------------------------|
| Encoding       | Initial (syntax)            | Final (semantics)        |
| Sliding        | Enforced by Mendler case    | Inherent in `(.)`        |
| Feedback       | Explicit `Knot` constructor | Structural in type       |
| Inspection     | Constructors visible        | Opaque; only observable  |
| Composition    | O(n²) left-nested           | O(1) amortised           |

**Pattern:** build in Circuit, run via Hyper.

## Tensor Choice: (,) vs Either

|                | (,)                           | Either                    |
|----------------|-------------------------------|---------------------------|
| Character      | Simultaneous / holding hands  | Sequential / taking turns |
| `trace`        | Lazy knot (`unsecond`)        | While-loop (`unright`)    |
| `untrace`      | `second`                      | `fmap Right`              |
| Use case       | Streams, dataflow, zipping    | Coroutines, parsers, FSMs |
| Categorical    | Costrong                      | Cochoice                  |

**Hasegawa's Theorem 3.1:** In cartesian traced structure, traces and fixpoints
coincide — `run (lift f) = fix f` is a theorem. In cochoice (`Either`), the
trace is strictly more general.

**Kidney-Wu:** A simultaneous `(,)` process splits into two sequential `Either`
processes via message passing. Hyper unifies both through continuation duality.

The `Kleisli IO` instances use `prompt#`/`control0#` for constant-stack IO loops.

## Performance: Reflection Without Remorse

Van der Ploeg & Kiselyov (2014) — left-nested composition is O(n²). Same fix:

| Structure        | Naive      | Efficient        | Inspection           |
|------------------|------------|------------------|----------------------|
| Monoid           | list       | difference list  | head/tail            |
| Monad            | free monad | codensity monad  | `viewl`              |
| Category         | `Cat`      | `Queue` (Ran)    | `viewl` on queue     |
| Traced category  | `Circuit`  | `Hyper`          | Mendler case         |

The Mendler case IS `viewl` — inspect the head before recursing. `encode` is
the codensity equivalent — amortises left-nesting to O(1).

**Hasegawa's distinction:** `Knot k` is cyclic sharing (channel stays open).
`Lift (trace k)` is the fixpoint combinator (channel closed immediately).
The Mendler case preserves the distinction. Without it: remorse — the
interpreter produces a result, just the wrong one.

## Future

**Patterns:** bidirectional pipes, state machines, self-referential streams,
parsers, agents (`Circuit (Kleisli IO) (,) Observation Action`).

**Open:** Kan isomorphism proof, uniqueness of `encode`, `Fix(Circuit)` iso,
Mendler as counit naturality, Geometry of Interaction.

**Extensions:** graded circuits, more effects, profunctor optics, learner
integration (compact closed = traced + duals).

## Writing an Example

Examples in `~/haskell/circuits/examples/`. Markdown with fenced Haskell blocks,
validated via `cabal repl` pasting. Extra deps: `cabal repl -b <dep>`.

Reference: `channel-basics.md`, `stable-marriage.md`, `repl-pure.md`, `two-loops.md`.

## Where Everything Lives

| Concept                 | Doc                          | Source                    |
|-------------------------|------------------------------|---------------------------|
| Five marks, six axioms  | `01-stack-language.md`       | —                         |
| GADT, Mendler case      | `02-gadt.md`                 | `Circuit/Circuit.hs`      |
| Free object, universals | `03-circuit.md`              | `Circuit/Circuit.hs`      |
| Hyper, triangle, Kan    | `04-hyper.md`                | `Circuit/Hyper.hs`        |
| Tensor choice           | `05-tensor.md`               | `Circuit/Traced.hs`       |
| RwR, performance        | `06-rwr.md`                  | —                         |
| Future, open questions  | `07-future.md`               | —                         |
| Categorical shopping    | `circuit-categorical.md`     | —                         |
| Hasegawa's theorem      | `hasegawa.md`                | —                         |
| Equational proofs       | `axioms-traced.md`           | —                         |
| Concise axiom form      | `axioms-hyp.md`              | —                         |
