# Hyperfunctions as Streams (Kidney–Wu 2.3)

**Source:** Kidney–Wu 2026, Section 2.3  
**Key insight:** Stream model is a high-level mental model of hyperfunctions; the continuation model (Eq. 1) is the implementation. The interface (⊳, ⊙, run) is indistinguishable between them.

---

## The Stream Model

A hyperfunction `a ↬ b` can be visualized as a stream of functions of type `a → b`:

```haskell
data Stream a = a ⊳ Stream a

-- Isomorphism (approximation):
(a ↬ b) ≈ Stream (a → b)
```

**Caveat:** This is a mental model, not a one-to-one representation. Many hyperfunctions are not streams, and the correspondence breaks down outside the interface. But within the interface (Eqs. 2–4), the behavior is indistinguishable.

---

## The Interface: Three Combinators

See [hyp-formulae.md](hyp-formulae.md) for the full axioms.

**Stream operators:**
```haskell
(⊳)  :: (a → b) → (a ↬ b) → (a ↬ b)    -- cons: push function onto stream
(⊙)  :: (b ↬ c) → (a ↬ b) → (a ↬ c)    -- zip: compose streams
run  :: a ↬ a → a                        -- collapse to value
```

**Composition law:**
```
(f ⊳ fs) ⊙ (g ⊳ gs) = (f ◦ g) ⊳ (fs ⊙ gs)    (3)
```

**Run law:**
```
run (f ⊳ fs) = f (run fs)                      (4)
```

Expression `f ⊳ g ⊳ h ⊳ ...` constructs a stream with `f` at the head, followed by `g`, then `h`, etc.

---

## Lift as a Homomorphism

`rep` (or `lift`) lifts an ordinary function into a hyperfunction and is homomorphic through composition:

```haskell
rep :: (a → b) → (a ↬ b)
rep f = f ⊳ rep f                              (5)
```

**Proof:**
```
rep f ⊙ rep g
  ≡ (f ⊳ rep f) ⊙ (g ⊳ rep g)    [by def of rep]
  ≡ (f ◦ g) ⊳ (rep f ⊙ rep g)    [by axiom (3)]
  ≡ rep (f ◦ g)                    [by def of rep]
```

---

## Example: Subtraction via Streams

**Strategy:** Convert both `n` and `m` to hyperfunction streams, zip them, run the result.

```haskell
n − m = λs z → run (nat n (id⊳) (rep (const z)) ⊙ nat m (id⊳) (rep s))
```

**Construction:**
- `n` becomes: `n` ids, then infinitely many `const z`s
- `m` becomes: `m` ids, then infinitely many `s`s

**After zipping:**
1. First `m` entries: `id ◦ id` (both streams have ids)
2. Next `n − m` entries: `id ◦ s` (m ran out, n still has ids)
3. Then: `const z ◦ s` (both exhausted; const z dominates)

**After run:** The stream collapses to `s (s (... (s z)))` with `n − m` applications of `s`.

**See Fig. 1** (nlab-selinger-diagram.png) for the full derivation.

---

## The Continuation Model

In Hyp.hs, we swap out the stream interface for the continuation-based implementation via `ι`:

```haskell
ι (f ⊳ h) k = f (ι k h)            (6)
ι (f ⊙ g) h = ι f (g ⊙ h)         (7)
run h = ι h (Hyp run)              (8)
```

**All equalities are preserved.** Code written with the stream model in mind compiles to the continuation model without loss.

---

## Bridge: The Fundamental Law

```haskell
ι f g = run (f ⊙ g)                (9)
```

This identity connects the stream model (high-level reasoning) to the continuation model (low-level implementation). The primitive operation on `a ↬ b` is `ι`; in the stream model, the primitive operations are `⊳`, `⊙`, `run`.

---

## Axiom Alignment (Round 3)

Map equations (3)–(9) to yarn-axioms 1–7 and JSV/Hasegawa axioms:
- (3): Axiom 3 (lift/rep is functor)
- (4): Axiom 4 (run = fixed-point)
- (6)–(9): Axioms 5–7 (<<, sliding, naturality) + bridge law

Reference: [hyp-formulae.md](hyp-formulae.md)
