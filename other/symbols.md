# Notation

**Summary:** The symbols used throughout the arc and examples. Mathematical
notation, used as mathematical notation — no apologies to GHC.

---

## The Table

| Symbol | Name | Type | Meaning |
|--------|------|------|---------|
| `↑` | lift | `(a → b) → Hyper a b` | embed a plain arrow |
| `↓` | lower | `Hyper a b → (a → b)` | observe a hyperfunction |
| `⊙` | compose | `cat b c → cat a b → cat a c` | sequential composition |
| `⊲` | push | `(a → b) → Hyper a b → Hyper a b` | prepend to the continuation |
| `⥁` | run | `Hyper a a → a` | tie the self-referential knot |
| `∥` | ambient | `braid → Trace t arr a b → Trace t arr (t s a) (t s b)` | thread state wire alongside |
| `↮` | knot | `Trace t arr (t a b) (t a c) → Trace t arr b c` | feedback loop constructor (body is a base arrow) |
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

TODO: Rederive for the normal-form `Trace` GADT. `Trace` has no `Compose`
constructor, so the old `freeze`-based Mendler case (`❄ (↮ f ⊙ g)`) no
longer applies literally. The corresponding interaction between `Knot`
and sequential composition is now encoded in the `Trace` `Category`
instance / `run` interpreter. Preserve the narrative intent: the knot
must not close its feedback channel before surrounding wiring participates.

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

- [01-marks-and-stacks.md](01-marks-and-stacks.md) — the five marks introduced
- [02-a-knot-recovers-fix.md](02-a-knot-recovers-fix.md) — the Mendler identity derived; Free discovered
- [03-hyper-buries-the-knot.md](03-hyper-buries-the-knot.md) — the triangle proved; lift.trace = trace.lift
- [axioms.md](axioms.md) — JSV axioms proved for both tensors
- `examples/lift-trace-commute.md` — full proof of the traced functor lemma
