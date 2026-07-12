---
name: symbols
description: Notation table for symbols used in the narrative
tags: ['notation', 'symbols', 'reference']
---
# Notation

**Summary:** The symbols used throughout the examples. Mathematical
notation, used as mathematical notation — no apologies to GHC.

---

## The Table

| Symbol | Name | Type | Meaning |
|--------|------|------|---------|
| `↑` | lift | `(a → b) → Hyper a b` | embed a plain arrow |
| `↓` | observe | `Hyper a b → (a → b)` | observe a hyperfunction (not `Circuit.Layer.lower`) |
| `⊙` | compose | `cat b c → cat a b → cat a c` | sequential composition |
| `⊲` | push | `(a → b) → Hyper a b → Hyper a b` | prepend to the continuation |
| `⥁` | runHyper | `Hyper a a → a` | tie the self-referential knot (not `Circuit.Layer.run`) |
| `∥` | ambient | `Trace t arr a b → Trace t arr (t s a) (t s b)` | thread state wire alongside |
| `↮` | knot | `arr (t a b) (t a c) → Trace t arr b c` | feedback loop constructor (body is a base arrow) |
| `↘` | run | `Trace t arr x y → arr x y` | interpret Trace to plain arrow |
| `↪` | trace | `arr (t a b) (t a c) → arr b c` | close the feedback channel |
| `↩` | untrace | `arr b c → arr (t a b) (t a c)` | open the feedback channel |
| `⇨` | encode | `Trace (,) (->) a b → Hyper a b` | initial → final |
| `⇨F` | encodeFree | `Free (->) a b → Hyper a b` | free category → final encoding |
| `⇦` | flatten | `Hyper a b → Trace (,) (->) a b` | final → initial (lossy) |
| `⇸` | invoke | `Hyper a b → Hyper b a → b` | apply a hyperfunction to its dual |
| `○` | base | `a → Hyper b a` | constant continuation |

Free and encodeFree are the post-0.2 additions. `Trace` is now the
normal-form initial encoding, with `Arr` and `Knot` as its only constructors.

---

## Two Registers

**The initial encoding** (`Free`, `Trace`, `Net`) has visible
constructors. Its symbols are construction and elimination:

```
↑ f          — Arr f (embed arr into Trace) / Lift f (embed arr into Free/Net)
↮ k          — Knot k (feedback loop; body is a base arrow in Trace, a diagram in Free/Net)
f ⊙ g        — sequential composition via (.) or (>>>) in Trace; Compose f g in Free/Net
↘ c          — run: Trace → arr / runFree: Free → arr
```

**The final encoding** (`Hyper`, `Queue`) has no visible constructors.
Its symbols are observation and composition:

```
↑ f          — lift f into Hyper (coinductive unrolling)
↓ h          — observe h by severing the feedback
⥁ h          — run h by feeding its own dual back
f ⊙ g        — compose: Hyper (\k -> invoke f (g . k))
```

`⊙` and `↑` appear in both registers with the same meaning — compose
and lift are the same operation in both encodings.

---

## The Six Axioms

```
axiom 1   (f ⊙ g) ⊙ h  =  f ⊙ (g ⊙ h)               associativity
axiom 2    f ⊙ ↑ id     =  f  =  ↑ id ⊙ f             identity
axiom 3    ↑ (f . g)    =  ↑ f ⊙ ↑ g                  lift is a functor
axiom 4    ⥁ (↑ f)       =  fix f                      run recovers fix of base arrows
axiom 5    ⊲ f ⊙ ⊲ g    =  ⊲ (f . g)                  push is a homomorphism
axiom 6    ⥁ ((f ⊲ p) ⊙ q)  =  f (⥁ (q ⊙ p))          feedback / sliding
```

---

## The Traced Functor Lemma

Not an axiom of a single traced category, but a homomorphism between two:

```
↑ . ↪  =  ↪ . ↑        (lift . trace = trace . lift)
```

`lift` preserves trace — it's a traced functor from `(->)` to `Hyper`.
Proved in `examples/lift-trace-commute.md`. This lemma is the
load-bearing step in the triangle proof for the `Knot` case.

---

## The Triangle

```
         ⇨
Trace ──────────────▶ Hyper
    \                     │
     \                    │ ↓
      \                   ▼
       run──────────────▶ arr
```

```
↓ . ⇨  =  run
```

Mapping a `Trace` to `Hyper` then observing gives the same result
as running the `Trace` directly.

---

## The Mendler Identity

In pre-0.2 Trace, sequential composition was a constructor (`Compose`).
Interpreting `Compose (Knot f) g` required a Mendler-style case so the
knot did not close its feedback channel before surrounding wiring
participated — freeze early and the sliding law fails.

Post-0.2 `Trace` is already in normal form: only `Arr` and `Knot`. There
is no `Compose` constructor and no Mendler case in `run`:

```haskell
run :: Traced t arr => Trace t arr a b -> arr a b
run (Arr f)  = f
run (Knot f) = trace f
```

Sliding lives in the `Category` instance instead. Composition rewrites
into a single top-level `Knot` (or plain `Arr`) before `run` ever sees it:

```haskell
-- Category (Trace t arr) — the sliding law, as pattern match
Arr f  . Arr g  = Arr (f . g)
Knot f . Arr g  = Knot (f . untrace g)     -- pre-compose into the channel
Arr f  . Knot g = Knot (untrace f . g)     -- post-compose into the channel
Knot f . Knot g = Knot (… fuse via braid …)
```

| old (pre-0.2) | now (0.2 normal form) |
|---------------|------------------------|
| `Compose (Knot f) g` Mendler case in the interpreter | `Knot f . Arr g` / `Arr f . Knot g` in `Category` |
| freeze, then run | rewrite at compose time; `run` is a direct fold |
| risk: close channel before wiring joins | `untrace` threads surrounding arrows into the body |

Narrative intent preserved: the knot must not close its feedback channel
before surrounding wiring participates. The mechanism moved from
interpreter case analysis to compile-time normal form.

Worked witness (post-compose slides into the loop exit):

```haskell
import Circuit (Trace, run)
import qualified Circuit.Trace as T
import Control.Category ((>>>))

-- >>> let step n = if n < 3 then Left (n + 1) else Right n
-- >>> let counter = T.Knot (either step step) :: Trace Either (->) Int Int
-- >>> run (counter >>> T.Arr (* 2)) 0
-- 6
```

`counter >>> T.Arr (* 2)` is not `(* 2) . run counter`. The `Category`
instance builds `T.Knot (untrace (* 2) . either step step)`, so the
doubling sits inside the feedback body before `run` closes the channel.
(Qualify `T.Arr`/`T.Knot` in `cabal repl` — interpreted mode also
loads `Circuit.Mon`, which exports its own `Arr`.)

See `examples/axioms.md` (Mendler case), `examples/circuit.md` (sliding),
`examples/knot-and-fix.md` (why `Knot` exists).

---

## The Push/Lift Dual

`push` and `(:)` play the same structural role:

```
(:) x . foldr' xs   ≡   push x . foldh' xs
```

`(:)` attaches to the outside. `push` threads inside through the
continuation. Same shape, flipped polarity.

---

## Encoding Worked Example

Fibonacci stream via the triangle:

```
fibs :: Trace (,) (->) () [Int]
fibs = ↮ (\(xs, ()) -> (0 : 1 : zipWith (+) xs (drop 1 xs), xs))

run fibs ()   = let (xs, ys) = ... in ys      -- lazy knot
↓ (⇨ fibs) () = same result                     -- triangle: ↓ . ⇨ = run
```

---

## References

- [marks-and-stacks.md](../examples/marks-and-stacks.md) — the five marks introduced
- [knot-and-fix.md](../examples/knot-and-fix.md) — the Mendler identity derived; Free discovered
- [hyper-buries-the-knot.md](../examples/hyper-buries-the-knot.md) — the triangle proved; lift.trace = trace.lift
- [axioms.md](axioms.md) — JSV axioms proved for both tensors
- `examples/lift-trace-commute.md` — full proof of the traced functor lemma
