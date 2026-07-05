# Marks and Stacks

<div align="center">

✦ · ✧ · ✦

*In which we discover a little stack language turn out to be an almost perfect description of functional programming; the five marks arrive first, the GADT follows.*

**[Next: A Knot Recovers Fix ⟶](02-a-knot-recovers-fix.md)**

</div>

---

circuits didn't start with a GADT. It started with `Hyper` — a coinductive type from
Kidney & Wu (2026) that encodes feedback in the type itself. The five marks (↓ ↑ ⊙ ⊲ ⥁)
were the API. They satisfied six axioms. They worked.

Only later did we build the initial encoding — a GADT with explicit constructors —
and prove the two encodings were the same traced monoidal category. Still later
we discovered that between `Trace` and `arr` sits `Free` — the free category
without feedback — and that much of what we'd attributed to `Hyper` was actually
`Free`'s work.

This chapter presents the five marks as they were discovered: on `Hyper`, with
no GADT in sight. The marks are the permanent interface. What lies beneath them
has changed, and will likely change again.

---

## The Five Marks

`Hyper` is the coinductive encoding of a traced monoidal category:

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

To produce a `b`, you invoke the dual `Hyper b a` — a continuation that
can feed values back. The feedback channel is structural in the type.

On this single type, five operations suffice:

```haskell
(⊙)  :: Hyper b c -> Hyper a b -> Hyper a c   -- compose
↑    :: (a -> b) -> Hyper a b                   -- lift a plain function
↓    :: Hyper a b -> (a -> b)                   -- observe by severing feedback
(⊲)  :: (b -> c) -> Hyper a b -> Hyper a c     -- push onto the input side
⥁    :: Hyper a a -> a                           -- tie the self-referential knot
```

These are the semantics of Section 7 in Launchbury, Krstic & Sauerwein (2013),
restated in our notation. `↑` embeds a plain function. `↓` observes a Hyper
against a constant continuation. `⊙` composes. `⊲` pre-composes on the feedback
channel. `⥁` closes the loop.

See `src/Circuit/Hyper.hs` for the definitions.

---

## The Six Axioms

The marks satisfy six axioms. The first three build a free category. The
last three add feedback.

```
axiom 1  (f ⊙ g) ⊙ h  =  f ⊙ (g ⊙ h)           associativity
axiom 2  f ⊙ ↑ id      =  f  =  ↑ id ⊙ f         identity
axiom 3  ↑ (f . g)     =  ↑ f ⊙ ↑ g               lift is a functor
axiom 4  ⥁ (↑ f)        =  fix f                   run recovers fix
axiom 5  ⊲ f ⊙ ⊲ g    =  ⊲ (f . g)                push is a homomorphism
axiom 6  ⥁ ((f ⊲ p) ⊙ q)  =  f (⥁ (q ⊙ p))        feedback / sliding
```

Axioms 1–3 are the free category — the moves of functional programming.
Axiom 4 says `run` on a lifted arrow is the classical fixed point.
Axiom 5 says push distributes over composition.
Axiom 6 is the one that isn't free: sliding. In `Hyper`, axiom 6 holds
structurally — composition threads the continuation through every layer,
so sliding is inherent in `(.)` itself.

---

## Where Are We?

These five marks were our starting point. They came from Kidney-Wu. They
worked — you could write programs with them. The next chapters build outward:
an initial encoding (a GADT) that makes the structure inspectable, a tensor
parameter that chooses between lazy sharing and iteration, and the discovery
that `Trace` minus `Knot` is the free category.

But the marks remain. Every construct in the library — `Trace`, `Free`,
`Net`, `Queue` — must eventually answer to them.

---

## References

- [Kidney & Wu (2026)](https://doi.org/10.1145/3776649) — hyperfunctions: communicating continuations
- [Launchbury, Krstic & Sauerwein (2013)](https://doi.org/10.4204/eptcs.129.9) — original axiom system
- `src/Circuit/Hyper.hs` — the five marks in code
