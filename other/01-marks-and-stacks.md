# Marks and Stacks

**Summary:** In which five marks and a stack language turn out to be an
almost perfect description of functional programming, and we set out to
make it a bit better.
**Next:** [02-a-knot-recovers-fix.md](02-a-knot-recovers-fix.md)

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

The five marks first appear on `Hyper`, the final encoding. We meet them
here because the interface is simpler — no constructors, no pattern
matching, just five operations on one coinductive type. The next chapter
builds the initial encoding (a GADT) and discovers what structure forces
these marks to exist.

`Hyper` is the final encoding of a traced monoidal category:

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

Two of the marks are compound — `⊲` is `↑` then `⊙`, `run` is `fix` then `↓` —
but the axioms don't care. They constrain the interface, not the implementation.

## Reading the Axioms

### 1–3: The Free Category

```
(f ⊙ g) ⊙ h  =  f ⊙ (g ⊙ h)       associativity
f ⊙ ↑ id      =  f  =  ↑ id ⊙ f     identity
↑ (f . g)     =  ↑ f ⊙ ↑ g           lift is a functor
```

These three say: composition is associative, `↑ id` is the identity
morphism, and `↑` respects composition of plain functions. Together they
make `Hyper` a category with `↑` as a functor from `(->)`.

If you stop here, you have the free category over Haskell functions.
This is the core of functional programming: function application and
composition. GHC itself is a function stack interpreter built on these
moves.

### 4: Faithful Embedding

```
⥁ (↑ f)  =  fix f
```

Substituting `⥁ = fix . ↓` gives the cleaner form: `↓ . ↑ = id`.
Observation recovers the original arrow. What you embed is what you
observe. This is the sanity check — `Hyper` doesn't add or remove
behaviour, it only adds structure (the continuation channel).

### 5: Centrality

```
(f ⊲ p) ⊙ (g ⊲ q)  =  (f . g) ⊲ (p ⊙ q)
```

Substitute `⊲ = ↑ then ⊙`:

```
(↑ f ⊙ p) ⊙ (↑ g ⊙ q)  =  ↑ (f . g) ⊙ (p ⊙ q)
```

Apply associativity (axiom 1) and functoriality (axiom 3):

```
↑ f ⊙ p ⊙ ↑ g ⊙ q  =  ↑ f ⊙ ↑ g ⊙ p ⊙ q
```

Cancel `↑ f` on the left and `q` on the right:

```
p ⊙ ↑ g  =  ↑ g ⊙ p
```

Centrality is commutativity of lifted arrows via `⊙`. A plain function
pushed onto the stack can always be re-associated to the outermost
position, no matter what hyperfunction it was pushed onto. It's the move
that makes function stacks work — `(g . f) x` is `f x` then `g`. So
natural we barely notice it.

### 6: Feedback / Sliding

```
⥁ ((f ⊲ p) ⊙ q)  =  f (⥁ (q ⊙ p))
```

Substituting the compounds:

```
fix (↓ ((↑ f ⊙ p) ⊙ q))  =  f (fix (↓ (q ⊙ p)))
```

A pushed function `f` on the left of a composition `q` swaps places
with `q` inside the fixed point. `p` and `q` exchange positions. This
is not reassociation — it is a genuine swap. A plain category cannot
produce it. This is the one axiom that is not a move in ordinary
functional programming.

It is the sliding axiom of a traced monoidal category. It is what makes
feedback honest — what keeps the loop from collapsing to a single
application. In `Hyper`, sliding holds structurally: every `Category`
composition threads the continuation through `g . h` before `f` sees
it. The type itself enforces the axiom.

Axioms 1–3 are the moves of FP. Axiom 4 is the sanity check. Axiom 5
is centrality — the move we use without noticing. Axiom 6 is the new
move.

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

When the feedback channel carries state — a stream, a counter, a
coroutine handoff — the five marks need an explicit tensor to name
the channel. That forces a third constructor. See
[02-a-knot-recovers-fix.md](02-a-knot-recovers-fix.md).

---

## The Conceptual Stack

The five marks depend on the following structure:

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

The five marks already imply everything below. The bridge to an initial
encoding — a GADT with explicit constructors — is where the Mendler case
enters. That's the next chapter.

---

## This Little Language Scales

Axioms 1–3 are the free category — the moves of FP. Axiom 4 is the
sanity check. Axiom 5 is centrality. Axiom 6 is the one that isn't
free. In `Hyper` it is inherent in the type. In an initial encoding, it
must be enforced by a single pattern match.

**Next:** [02-a-knot-recovers-fix.md](02-a-knot-recovers-fix.md) — how
axiom 4 forces a type change, the lazy knot GHC can tie, and one pattern
match keeps the trace honest.

---

## References

- [Launchbury, Krstic & Sauerwein (2013)](https://doi.org/10.4204/eptcs.129.9) — original axiom system; coroutining folds with hyperfunctions
- [Kidney & Wu (2026)](https://doi.org/10.1145/3776649) — hyperfunctions: communicating continuations
- [Joyal, Street & Verity (1996)](https://doi.org/10.1017/s0305004100074338) — traced monoidal categories
- `src/Circuit/Hyper.hs` — the five marks in code
