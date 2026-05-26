# Notation

**Summary:** The symbols used throughout the arc and examples. Mathematical
notation, used as mathematical notation — no apologies to GHC.

---

## The Table

| Symbol | Name | Type | Meaning |
|--------|------|------|---------|
| `↑` | lift | `(a → b) → Circuit arr t a b` | embed a plain arrow |
| `↓` | lower | `Hyper a b → (a → b)` | observe a hyperfunction |
| `⊙` | compose | `cat b c → cat a b → cat a c` | sequential composition |
| `⊲` | push | `(a → b) → Hyper a b → Hyper a b` | prepend a plain function |
| `⥁` | run | `Hyper a a → a` | tie the self-referential knot (recovers fix on lifted arrows) |
| `∥` | ambient | `braid → Circuit arr t a b → Circuit arr t (t s a) (t s b)` | thread state wire alongside |
| `↮` | knot | `arr (t a b) (t a c) → Circuit arr t b c` | feedback loop constructor |
| `↘` | reify | `Circuit arr t x y → arr x y` | interpret to plain arrow |
| `↪` | trace | `arr (t a b) (t a c) → arr b c` | close the feedback channel |
| `↩` | untrace | `arr b c → arr (t a b) (t a c)` | open the feedback channel |
| `⇨` | encode | `Circuit (->) (,) a b → Hyper a b` | initial → final (preserving) |
| `⇦` | flatten | `Hyper a b → Circuit (->) (,) a b` | final → initial (lossy) |
| `⇸` | invoke | `Hyper a b → Hyper b a → b` | apply a hyperfunction to its dual |
| `○` | base | `a → Hyper b a` | constant continuation |
| `↬` | — | `type ↬ = Hyper` | type-level synonym |

The canonical API uses lowercase names (`lift`, `lower`, `reify`, etc.).
The symbols are notation — used in proofs, diagrams, and the arc documents
where the mathematical content should be visible without syntactic noise.

---

## Two Registers

**The initial encoding** (`Circuit`) has visible constructors. Its symbols
are construction and elimination forms:

```
↑ f          — constructor: embed f as a Lift
↮ f          — constructor: embed f as a Knot
f ⊙ g        — constructor: Compose f g
↘ c          — eliminator: reify the circuit to a plain arrow
```

**The final encoding** (`Hyper`) has no constructors — only behaviour.
Its symbols are observation and composition:

```
↑ f          — lift f into Hyper (coinductive unrolling)
↓ h          — observe h by severing the feedback channel
⥁ h          — run h by feeding its own dual back
f ⊙ g        — compose: Hyper (\k -> invoke f (g . k))
```

`⊙` and `↑` appear in both registers with the same meaning — compose and
lift are the same operation in both encodings. The difference is what
the type checker sees underneath.

---

## The Six Axioms

Written as we mean them, not as GHC requires them:

```
axiom 1   (f ⊙ g) ⊙ h  =  f ⊙ (g ⊙ h)               associativity
axiom 2    f ⊙ ↑ id     =  f  =  ↑ id ⊙ f             identity
axiom 3    ↑ (f . g)    =  ↑ f ⊙ ↑ g                  lift is a functor
axiom 4    ⥁ (↑ f)       =  fix f                      run recovers fix of base arrows
axiom 5    ⊲ f ⊙ ⊲ g    =  ⊲ (f . g)                  push is a homomorphism
axiom 6    ⥁ ((f ⊲ p) ⊙ q)  =  f (⥁ (q ⊙ p))          feedback / sliding
```

Axioms 1–3 are the free category. Axiom 4 is the sanity check on lifted arrows
(run recovers classical fixed points for base arrows). Axiom 5 says push
respects composition. Axiom 6 is the one that isn't free (it forces Knot).

---

## The Five JSV Axioms

The Joyal–Street–Verity axioms for a traced monoidal category. Channel
is on the left; payload on the right. `⊗` is the tensor.

```
vanishing    ↪ (id ⊗ f)       =  f                    unit channel is a no-op
sliding      ↪ ((id ⊗ g) ⊙ f) =  ↪ (f ⊙ (id ⊗ g))    channel bridge commutes
tightening   ↪ ((g ⊗ id) ⊙ f ⊙ (h ⊗ id))  =  g ⊙ ↪ f ⊙ h    payload passes through
strength     ↪ (g ⊗ f)        =  g ⊗ ↪ f              independent wire invisible
yanking      ↪ swap            =  id                   tracing a swap is identity
```

For `(,)`, `↪` ties a lazy knot. For `Either`, `↪` runs a while-loop.
The axioms hold for both by the same logical structure.

---

## The Triangle

The commuting triangle connecting initial and final encodings:

```
         ⇨
Circuit ────▶ Hyper
    \           │
     \          │ ↓
      \         ▼
       ↘──────▶ arr
```

```
↓ . ⇨  =  ↘
```

Mapping a `Circuit` into `Hyper` and then observing gives the same result
as running the `Circuit` directly. Proved case by case in
[03-hyper-buries-the-knot.md](03-hyper-buries-the-knot.md).

---

## The Mendler Identity

The operational form of the sliding axiom in `reify`:

```
↘ (↑ f)           =  f                    faithful embedding
↘ (↮ k)           =  ↪ k                  trace closes the channel
↘ (↮ f ⊙ g)       =  ↪ (f . ↩ (↘ g))     Mendler case: g participates inside
↘ (f ⊙ g)         =  ↘ f . ↘ g            functoriality
```

The third line is the load-bearing one. Without it, `↘ (↮ f ⊙ g)` would
reduce to `↪ f . ↘ g` — closing the channel before `g` participates.
One equation separates the free traced monoidal category from the
degenerate model.

---

## The Push/Lift Dual

`push` and `(:)` play the same structural role in different carriers:

```
(:) x . foldr' xs   ≡   push x . foldh' xs
```

`(:)` attaches to the outside of a list. `push` threads into the inside
of a `Hyper`, through the continuation channel. Same shape, flipped
polarity. Both build endofunction chains:

```
foldr'  :: [a → a] → ([a] → [a])       — Endo([a])
foldh'  :: [a → a] → (Hyper a a → Hyper a a)   — Endo(Hyper a a)
```

`push` is not compound in `Hyper` — it is primitive, threading through the
feedback channel.  The GADT has no direct counterpart; `Compose (Lift f) h`
(post-composition on `reify`) is the closest analogue but not equivalent.

---

## State Threading

`ambient` (symbol `∥`) threads a state wire through a circuit unchanged.
The braid argument swaps state past the feedback channel:

```
∥ braid (↑ f)    =  ↑ (↩ f)            state tags along via untrace
∥ braid (f ⊙ g)  =  ∥ braid f ⊙ ∥ braid g   state threads both stages
∥ braid (↮ k)    =  ↮ (dimap braid braid (↩ k))   state slides past knot
```

The third equation is the sliding axiom wearing circuit clothes: a state
wire slides past a feedback loop via braiding. This is why `ambient`
requires an explicit braid argument — the braid is the proof that the
state and the channel are independent.

---

## Encoding Worked Example

Fibonacci stream via the triangle:

```
fibs :: Circuit (->) (,) () [Int]
fibs = ↮ (\(xs, ()) -> (0 : 1 : zipWith (+) xs (drop 1 xs), xs))

-- Run directly:
↘ fibs ()
= ↪ (\(xs, ()) -> (0 : 1 : zipWith (+) xs (drop 1 xs), xs)) ()
= let (xs, ys) = ... in ys      -- lazy knot

-- Run via Hyper:
↓ (⇨ fibs) ()
= ↓ (↪ (↑ step)) ()             -- encode (↮ f) = ↪ (↑ f)
= ... same lazy knot ...         -- triangle: ↓ . ⇨ = ↘
```

Both paths reach the same stream. The triangle is not just a diagram —
it is an equality between two ways of running the same program.

---

## Factorial via Either

```
fac :: Circuit (->) Either (Int, Int) Int
fac = ↮ step
  where
    step (Right (n, acc))  | n <= 1  =  Right acc
    step (Right (n, acc))            =  Left (n - 1, n * acc)
    step (Left s)                    =  step (Right s)

↘ fac (5, 1)
= ↪ step (5, 1)
= go (Right (5, 1))
= go (Left (4, 5))
= go (Left (3, 20))
= go (Left (2, 60))
= go (Left (1, 120))
= 120
```

`↪` on `Either` is the while-loop. `Left` feeds back; `Right` exits.
The `↮` constructor is the same as for `(,)` — the tensor choice is what
changes the operational character.

---

## References

- [01-marks-and-stacks.md](01-marks-and-stacks.md) — the five marks introduced
- [02-a-knot-recovers-fix.md](02-a-knot-recovers-fix.md) — the Mendler identity derived
- [03-hyper-buries-the-knot.md](03-hyper-buries-the-knot.md) — the triangle proved
- [axioms.md](axioms.md) — JSV axioms proved for both tensors
- [Launchbury, Krstic & Sauerwein (2013)](https://doi.org/10.4204/eptcs.129.9) — original LKS axiom system
- [Joyal, Street & Verity (1996)](https://doi.org/10.1017/s0305004100074338) — traced monoidal categories
