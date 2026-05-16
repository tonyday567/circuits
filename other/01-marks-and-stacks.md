# Marks and Stacks

**Summary:** In which five marks and a stack language turn out to be an
almost perfect description of functional programming, and we set out to
make it a bit better.
**Next:** [02-a-knot-needs-a-mendler.md](02-a-knot-needs-a-mendler.md)

---

Five marks and a stack language. That's an almost perfect description of
functional programming — data flows through pure functions arranged by
composition. We set out to make it a bit better: add feedback, make it
inspectable, prove the structure is free. Everything else in the library
is a consequence of making these five operations precise.

```
↑   lift      embed a plain arrow
↓   lower     observe hyperfunction
⊙   compose   sequential composition
⊲   push      prepend a plain function
⥁   run       tie the knot
```

The five marks live on `Hyper`, the final encoding of a traced monoidal
category:

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

To produce a `b`, you invoke the dual `Hyper b a` — a continuation that
can feed values back. The feedback channel is structural in the type.
Unfolding the recursion:

```
Hyper a b = (((...  → a) → b) → a) → b
```

Every `Hyper a b` already carries its own feedback. The five marks
operate on this self-referential structure.

---

## The Five Marks as a Language

```haskell
(⊙)  :: Hyper b c -> Hyper a b -> Hyper a c   -- compose
↑    :: (a -> b) -> Hyper a b                   -- lift
↓    :: Hyper a b -> (a -> b)                   -- lower
(⊲)  :: (b -> c) -> Hyper a b -> Hyper a c     -- push
⥁    :: Hyper a a -> a                           -- run
```

These are the semantics of Section 7 in Launchbury, Krstic & Sauerwein (2013), restated in library notation. The five marks are the generators of the free traced monoidal category — they just happen to have a particularly clean final encoding in `Hyper`.

See `src/Circuit/Hyper.hs` for the definitions.

---

## The Six Axioms

These five operations satisfy six axioms. The first three build a free
category. The last three add the feedback structure.

```
axiom 1  (f ⊙ g) ⊙ h  =  f ⊙ (g ⊙ h)           associativity
axiom 2  f ⊙ ↑ id      =  f  =  ↑ id ⊙ f         identity
axiom 3  ↑ (f . g)     =  ↑ f ⊙ ↑ g               lift is a functor
axiom 4  ⥁ (↑ f)        =  fix f                   run is fixed-point
axiom 5  (f ⊲ p) ⊙ (g ⊲ q)  =  (f . g) ⊲ (p ⊙ q)  push composition
axiom 6  ⥁ ((f ⊲ p) ⊙ q)     =  f (⥁ (q ⊙ p))     feedback / sliding
```

---

## Push and Run are Compound

Two of the five marks are not primitive — they decompose into simpler
terms:

**Push decomposes into lift and compose:**

```haskell
f ⊲ p  =  ↑ f ⊙ p
```

**Run decomposes into lower and fix:**

```haskell
⥁  =  fix . ↓
```

Substituting these into axioms 4, 5, 6 reduces the axiom set to three
structural roles:

| Axioms | Role | What holds |
|--------|------|------------|
| 1, 2, 3 | Free category | `↑`, `⊙` build a category |
| 4 | Faithful embedding: `↓ . ↑ = id` | Observation recovers the original arrow |
| 5 | Centrality: lifted arrows slide past anything | Free from tensor symmetry |
| 6 | Feedback / sliding | Self-reference preserves structure |

Axioms 4 and 5 introduce no new structure. Only axiom 6 does — it says
that when a pushed function meets a composed morphism, the two swap
places inside `⥁`. This swap is the trace. In `Hyper`, this holds
structurally: composition is defined as

```haskell
f . g = Hyper $ \h -> invoke f (g . h)
```

The continuation `h` threads through `g . h` before `f` sees it, on
every unfolding. Sliding is free. There is no degenerate model to fall
into because the type itself encodes the feedback.

---

## A Small Taste

The language is immediately executable:

```haskell
-- lift embeds a plain function
>>> ↓ (↑ (+ 1)) 5
6

-- run ties the self-referential knot
>>> ⥁ (Hyper $ \_ -> 42 :: Int)
42

-- push prepends a function to the output
>>> ↓ ((+ 1) ⊲ ↑ (* 2)) 5
6

-- ask: "how many layers deep is the continuation chain?"
>>> let ask = Hyper (\k -> invoke k (Hyper (\_ -> 0)) + 1) in ask ⇸ (○) 42
43
```

The real power surfaces when the feedback channel carries state — a
stream, a counter, a coroutine handoff. That requires an explicit
tensor to name the channel, which forces a third constructor. See
[02-a-knot-needs-a-mendler.md](02-a-knot-needs-a-mendler.md).

---

## The Conceptual Stack

The five marks sit at the top of a conceptual tower. Each layer below
adds one concept:

```
↑ ↓ ⊙ ⊲ ⥁              ← the five marks on Hyper
     ↓
Axioms 1–6             ← what the marks must satisfy
     ↓
Hyper a b               ← invoke :: Hyper b a -> b
     ↓
Sliding is structural   ← (.) threads the continuation, no degenerate model
     ↓
Tensor choice           ← (,) vs Either: dataflow vs coroutines
     ↓
Production use          ← agents, pipes, parsers, backprop
```

Each level adds exactly one concept. The five marks at the top already
imply everything below. The bridge to an initial encoding — a GADT with
explicit constructors — is where the Mendler case enters. That's the
next chapter.

---

## This Little Language Scales

Axiom 6 — the feedback axiom — is exactly the sliding axiom of a traced
monoidal category. The five marks, taken together, are the generators of
the free traced monoidal category over a base arrow. In `Hyper`, sliding
falls out of the type. In the initial encoding, it must be enforced by a
single pattern match.

**Next:** [02-a-knot-needs-a-mendler.md](02-a-knot-needs-a-mendler.md) — how
the axioms force a three-constructor GADT, and one pattern match saves
everything from degeneracy.

---

## References

- Launchbury, Krstic & Sauerwein, "Hyperfunctions" (2013) — original axiom system
- Kidney & Wu, "Hyperfunctions and the monad of streams" (2026) — modern notation
- Joyal, Street & Verity, "Traced monoidal categories" (1996) — categorical foundations
- `src/Circuit/Hyper.hs` — the five marks in code
