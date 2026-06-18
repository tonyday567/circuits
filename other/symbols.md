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
| `∥` | ambient | `braid → Circuit arr t a b → Circuit arr t (t s a) (t s b)` | thread state wire alongside |
| `↮` | knot | `Circuit arr t (t a b) (t a c) → Circuit arr t b c` | feedback loop constructor (body is a Circuit, not a base arrow) |
| `↘` | reify | `Circuit arr t x y → arr x y` | interpret Circuit to plain arrow |
| `❄` | freeze | `Circuit arr t a b → Free arr t a b` | dissolve Knot into Lift via base-arrow trace |
| `↪` | trace | `arr (t a b) (t a c) → arr b c` | close the feedback channel |
| `↩` | untrace | `arr b c → arr (t a b) (t a c)` | open the feedback channel |
| `⇨` | encode | `Circuit (->) (,) a b → Hyper a b` | initial → final (= encodeFree . freeze) |
| `⇨F` | encodeFree | `Free (->) (,) a b → Hyper a b` | free category → final encoding |
| `⇦` | flatten | `Hyper a b → Circuit (->) (,) a b` | final → initial (lossy) |
| `⇸` | invoke | `Hyper a b → Hyper b a → b` | apply a hyperfunction to its dual |
| `○` | base | `a → Hyper b a` | constant continuation |

Free and encodeFree are the post-0.2 additions. `❄` (freeze) is the
load-bearing one — the Mendler case lives here.

---

## Two Registers

**The initial encoding** (`Free`, `Circuit`, `Net`) has visible
constructors. Its symbols are construction and elimination:

```
↑ f          — Lift f (embed arr into Free/Circuit/Net)
↮ k          — Knot k (feedback loop, body is a Circuit)
f ⊙ g        — Compose f g
❄ c          — freeze: Circuit → Free (eliminates Knot)
↘ c          — reify: Circuit → arr (runFree . freeze)
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
         ⇨ (= ⇨F . ❄)
Circuit ──────────────▶ Hyper
    \                     │
     \                    │ ↓
      \                   ▼
       ↘────────────────▶ arr
          (= runFree . ❄)
```

```
↓ . ⇨  =  ↘
```

Mapping a `Circuit` to `Hyper` then observing gives the same result
as running the `Circuit` directly. Factorized: `⇨ = ⇨F . ❄` and
`↘ = runFree . ❄`.

---

## The Mendler Identity (in freeze)

```
❄ (↑ f)         =  ↑ f                  identity arrows have no Knot
❄ (↮ k)         =  ↑ (↪ (↘ k))          dissolve Knot into base-arrow trace
❄ (↮ f ⊙ g)     =  ↑ (↪ (↘ f . ↩ (↘ g)))  Mendler case: g participates inside
❄ (f ⊙ g)       =  ❄ f ⊙ ❄ g            functoriality through Compose
```

The third line is the load-bearing one. Without it, `❄ (↮ f ⊙ g)` would
reduce to `↑ (↪ (↘ f)) ⊙ ❄ g` — the naive form that closes the channel
before `g` participates. One equation separates the free traced monoidal
category from the degenerate model.

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
fibs :: Circuit (->) (,) () [Int]
fibs = ↮ (\(xs, ()) -> (0 : 1 : zipWith (+) xs (drop 1 xs), xs))

↘ fibs ()     = let (xs, ys) = ... in ys      -- lazy knot
↓ (⇨ fibs) () = same result                     -- triangle: ↓ . ⇨ = ↘
```

---

## References

- [01-marks-and-stacks.md](01-marks-and-stacks.md) — the five marks introduced
- [02-a-knot-recovers-fix.md](02-a-knot-recovers-fix.md) — the Mendler identity derived; Free discovered
- [03-hyper-buries-the-knot.md](03-hyper-buries-the-knot.md) — the triangle proved; lift.trace = trace.lift
- [axioms.md](axioms.md) — JSV axioms proved for both tensors
- `examples/lift-trace-commute.md` — full proof of the traced functor lemma
