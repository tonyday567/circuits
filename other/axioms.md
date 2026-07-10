# Traced Monoidal Category Axioms

**Summary:** Equational proofs for all five axioms, both tensors. For when
you need to be sure.
**Reference:** https://ncatlab.org/nlab/show/traced+monoidal+category
**See also:** `examples/knot-recovers-fix.md` (GADT derivation), `src/Circuit/Trace.hs` (`Traced` instances)

The five Joyal–Street–Verity axioms proved for tensors `(,)` and `Either`
over the base arrow `(->)`. Narrative motivation lives in the arc docs (01–07).

## Preliminaries

```haskell
class Traced arr t where
  trace   :: arr (t a b) (t a c) -> arr b c   -- close the channel
  untrace :: arr b c -> arr (t a b) (t a c)   -- inject into channel
```

For `arr = (->)`:

| Tensor | `trace` | `untrace` |
|--------|---------|-----------|
| `(,)` | `\f b -> let (a, c) = f (a, b) in c` | `fmap` / `second` |
| `Either` | while-loop: `Left` continues, `Right` exits | `fmap` / `right` |

The left-channel convention puts the channel on the left: `t a b` means
channel `a`, payload `b`. So `id ⊗ f` means `first f` for `(,)` and
`left f` for `Either` — both act on the channel component, leaving the
payload untouched.

The two tensors are operationally dual:

- **`(,)`** ties a lazy knot — feedback and output co-occur in a single
  recursive binding. Proofs reduce to substituting the knot.
- **`Either`** runs a while-loop — `Left` re-enters, `Right` exits.
  Proofs compare the reachable states of two state machines.

Every axiom holds for both by the same logical structure, reached by
different computational paths.

## The Five Axioms

**1. Vanishing.** Tracing over the unit does nothing. Nested channels
trace in sequence.
```
(a) tr^I(f) = f           for f : A ⊗ I → B ⊗ I
(b) tr^{X⊗Y}(f) = tr^X(tr^Y(f))   for f : A ⊗ X ⊗ Y → B ⊗ X ⊗ Y
```

**2. Sliding.** A morphism on the channel can slide from one side of `f`
to the other inside the trace.
```
tr^X((id_B ⊗ g) ∘ f) = tr^Y(f ∘ (id_A ⊗ g))
for f : A ⊗ X → B ⊗ Y,  g : Y → X
```

**3. Tightening.** Payload morphisms pass freely through the trace.
```
tr^X((g ⊗ id_X) ∘ f ∘ (h ⊗ id_X)) = g ∘ tr^X(f) ∘ h
for h : A → B,  f : B ⊗ X → C ⊗ X,  g : C → D
```

**4. Strength.** An independent payload wire is invisible to the trace.
```
tr^X(g ⊗ f) = g ⊗ tr^X(f)
for g : A → B,  f : C ⊗ X → D ⊗ X
```

**5. Yanking.** Tracing the braiding is the identity.
```
tr^X(swap_{X,X}) = id_X
```

Yanking is the only axiom that requires a braiding. The other four hold
in any monoidal category with a trace.

## Connection to the Hyperfunction Axioms

Launchbury, Krstic & Sauerwein (2013) state six axioms for hyperfunctions.
`push` is primitive — it prepends a function on the input side of the
feedback channel. The six axioms reduce to three structural roles:

| LKS Axiom | JSV Axiom | Structural role |
|-----------|-----------|-----------------|
| 1–3 | — | Free category (`Lift` + `Compose`) |
| 4 | — | `runHyper (lift f) = fix f` — fixed points of base arrows (Hasegawa Thm 3.1) |
| 5 | — | Push composition: `push f p . push g q = push (f . g) (p . q)`. Push distributes over composition — a homomorphism constraint on the primitive. |
| 6 | Sliding | Feedback (forces `Knot` constructor) |

LKS axioms 1–5 have no direct JSV counterpart — LKS 1–3 fall out of the free
category structure, LKS 4 (`runHyper (lift f) = fix f`) follows from the Hasegawa fixpoint correspondence for base arrows,
and LKS 5 (push composition) constrains how push interacts with composition.
Only LKS 6 (sliding/feedback) maps cleanly to a JSV axiom.

Axioms 4 and 5 introduce no new constructors on the final side. Axiom 4
(`runHyper (lift f) = fix f`) is the key property showing that fixed points of
base arrows are available in the final encoding; it is part of the motivation
for why the initial encoding needs the structure that `Knot` provides.
Only axiom 6 (sliding) forces a new constructor on the initial side.
See `02-a-knot-recovers-fix.md` for the derivation.

## The Mendler Case

In the `Trace` datatype, the sliding axiom is enforced by the `Category`
instance rather than by a special interpreter case. `Trace` values are already
in existential normal form — at most one `Knot` at the top, over a base-arrow
body — so `run` is a direct fold:

```haskell
run :: Traced arr t => Trace t arr a b -> arr a b
run (Arr f)  = f
run (Knot f) = trace f
```

The old `Circuit` interpreter needed a Mendler case for `Compose (Knot f) g`
to avoid closing the channel too early. In the normal-form `Trace`, sequential
composition of `Knot`s is normalized by the `Category` instance before `run`
ever sees it, so there is no `Compose` constructor and no Mendler case. For the
full story see `examples/knot-recovers-fix.md`.

## Proofs

### Axiom 1: Vanishing

#### (a) Unit channel is a no-op

**With `(,)` — unit `I = ()`.**

A morphism `f :: ((), a) -> ((), b)` is, under the unit isomorphism,
`f = \((), x) -> ((), g x)` for some `g :: a -> b`.

```haskell
trace f b
  = let (a, c) = f (a, b) in c       -- Traced (->) (,) definition
  = let ((), c) = f ((), b) in c     -- a :: ()
  = let ((), c) = ((), g b) in c     -- definition of f
  = g b
  = run (Arr g) b                     -- same as a plain Arr
```

The lazy knot has nothing to tie — `()` is determined immediately.

**With `Either` — unit `I = Void`.**

`Either Void a ≅ a` since `Left v` is uninhabited. A morphism
`f :: Either Void a -> Either Void b` can only map `Right x` to
`Right (g x)`.

The while-loop enters at `Right b`. On each step, `f` returns either
`Right c` (exit) or `Left v` — but `Left v` is uninhabited, so the
loop terminates immediately at `g b`. The trace degenerates to plain
function application.

#### (b) Nested channels trace in sequence

**With `(,)`.**

`f :: ((x, y), a) -> ((x, y), b)`. Channel is `(x, y)`, payload is `a`.

**LHS** — trace over `(x, y)` in one lazy knot:
```haskell
trace f a0 = let ((x, y), b) = f ((x, y), a0) in b
```

**RHS** — trace `y` first, then `x`. Reshape `f` via associativity:

```haskell
shuffle   (y, (x, a)) = ((x, y), a)
unshuffle ((x, y), b) = (y, (x, b))
f_Y = unshuffle . f . shuffle   -- channel y, payload (x, a)
```

Inner trace ties `y`, yielding a function of `(x, a0)`. Outer trace
ties `x`. Both find the same fixed point: `((x, y), b) = f ((x, y), a0)`.
Lazy evaluation makes the nested knots equivalent to the single knot.

**With `Either`.**

Channel is `Either a b`. LHS runs one while-loop over the state
`Either a b`. RHS runs two nested loops (trace `b` first, then `a`)
via associativity `Either (Either a b) c ≅ Either a (Either b c)`.
Both reach the same exit state — nested state machines vs one.

The `(,)` and `Either` traces are operationally dual: coinductive lazy
knot vs inductive while-loop. Vanishing holds for both by the same
logical structure, reached by different computational paths.

### Axiom 2: Sliding

`f :: (x, a) -> (y, b)`, `g :: y -> x`. Channel changes from `x` to `y`;
`g` bridges them back.

**With `(,)`.**

LHS — apply `g` to the output channel, trace over `x`:
```haskell
trace (first g . f) a
  = let (x, b) = (first g . f) (x, a) in b
  = let (x, b) = let (y, b') = f (x, a) in (g y, b') in b
  = let (y, b) = f (g y, a) in b             -- substitute x = g y
```

RHS — apply `g` to the input channel, trace over `y`:
```haskell
trace (f . first g) a
  = let (y, b) = (f . first g) (y, a) in b
  = let (y, b) = f (g y, a) in b
```

Both reduce to `\a -> let (y, b) = f (g y, a) in b`. The lazy knot ties
`y` to `g y` from `f`'s output — the same fixed point either side.

**With `Either`.**

`f :: Either x a -> Either y b`, `g :: y -> x`.

LHS — apply `g` to the output channel, trace over `x`:

Enter at `Right b`. On step `s :: Either x a`, call `f s`:
- `Right c` → exit with `c`
- `Left y` → re-enter at `Left (g y)`

RHS — apply `g` to the input channel, trace over `y`:

Enter at `Right b`. On `Right a`, call `f (Right a)`. On `Left y`,
call `f (Left (g y))`.

Both implement the same state machine: each loop step feeds `g`-transformed
values back into `f`. The sequence of states fed to `f` is identical;
the exit condition depends only on `f`'s output. Same result.

### Axiom 3: Tightening

`h :: a -> b`, `f :: (x, b) -> (x, c)`, `g :: c -> d`. Channel `x`
is untouched by `h` and `g` throughout.

**With `(,)`.**

```haskell
trace (second g . f . second h) a
  = let (x, d) = (second g . f . second h) (x, a) in d
  = let (x, d) = second g (f (x, h a)) in d
  = let (x, c) = f (x, h a) in g c
  = g (let (x, c) = f (x, h a) in c)
  = g (trace f (h a))
  = (g . trace f . h) a
```

**With `Either`.**

`h :: a -> b`, `f :: Either x b -> Either x c`, `g :: c -> d`.
`second h` maps `Right a` to `Right (h a)`, leaves `Left x` alone.

The while-loop enters at `Right (h a)`. The channel `x` flows through
`Left` transitions in `f`, never touching `h` or `g`. Exit occurs
when `f` returns `Right c`, at which point `g c` is returned.

Both sides: enter at `Right (h a)`, loop on `f`'s `Left` transitions,
exit with `g c`. `h` and `g` are straight wires — they pass freely
through the trace.

### Axiom 4: Strength

`g :: a -> b` acts on payload `a` independently; `f :: (x, c) -> (x, d)`
runs with the channel `x`. They operate on disjoint parts of the tensor.

**With `(,)`.**

`g ⊗ f` acts on payload `(a, c)` with channel `x`:
```haskell
g `par` f :: (x, (a, c)) -> (x, (b, d))
g `par` f (x, (a, c)) = let (x', d) = f (x, c) in (x', (g a, d))
```

```haskell
trace (g `par` f) (a, c)
  = let (x, (b, d)) = (g `par` f) (x, (a, c)) in (b, d)
  = let (x', d) = f (x, c) in (g a, d)       -- x tied to x' by knot
  = (g a, let (x, d) = f (x, c) in d)
  = (g a, trace f c)
  = (g ⊗ trace f) (a, c)
```

`g` is invisible to the channel — the lazy knot ties only `c`/`d` via `f`.

**With `Either`.**

`g` acts on `Right a`, `f` runs the loop on `Either x c`. `g ⊗ f` maps
`Left x` to `Left x` (channel passes through), `Right (Left a)` to
`Right (Left (g a))` (g on the a-side), and delegates `Right (Right c)`
to `f`.

Both sides: `g` is a straight wire on the `a` component, `trace f`
runs its loop on the `c` component. `g` has no feedback path and
cannot affect when or how the loop exits.

### Axiom 5: Yanking

`swap :: (x, x) -> (x, x)` is the braiding.

**With `(,)`.**

```haskell
trace swap x
  = let (a, c) = swap (a, x) in c
  = let (a, c) = (x, a) in c
  = x
  = id x
```

The lazy knot resolves immediately: `a` is set to `x` from
`swap (a, x) = (x, a)`, and `c = a = x`. One substitution, no recursion.

**With `Either`.**

`swapEither :: Either a b -> Either b a` maps `Left x → Right x`,
`Right x → Left x`.

Enter at `Right x`. `swapEither (Right x) = Left x` — loop.
Re-enter at `Left x`. `swapEither (Left x) = Right x` — exit with `x`.

The while-loop runs exactly two steps. Operationally different from
`(,)` — a two-step state machine vs an immediate lazy substitution —
but the same result.

**Why braiding is required.** The other four axioms involve only the
channel and payload structure — they hold in any monoidal category with
a trace. Yanking requires a morphism `swap : X ⊗ X → X ⊗ X` that is
part of a braiding. In a non-braided monoidal category, no such
morphism is guaranteed to exist, so yanking cannot be stated.

For `(,)` and `Either` in Haskell, both are symmetric monoidal —
`swap` exists and is involutive — so yanking holds.

## Summary

| Axiom | What it says | Key mechanism |
|--------|-------------|---------------|
| Vanishing | Unit channel is a no-op; products nest | Knot with nothing to tie |
| Sliding | Channel bridge commutes past `f` | Same fixed point either side |
| Tightening | Payload morphisms pass through | Channel untouched by `h`, `g` |
| Strength | Independent payload wire is invisible | Disjoint types, no contact |
| Yanking | Tracing a swap is identity | Requires braiding |

The `(,)` and `Either` instances are operationally dual throughout:
lazy knot vs while-loop. Every axiom holds for both by the same logical
structure.

## References

- [Joyal, Street & Verity (1996)](https://doi.org/10.1017/s0305004100074338) — traced monoidal categories
- [Launchbury, Krstic & Sauerwein (2013)](https://doi.org/10.4204/eptcs.129.9) — hyperfunction axioms
- [Hasegawa (1997)](https://doi.org/10.1007/978-1-4471-0865-8_7) — Theorem 3.1: cartesian traces = fixpoints
- [Van der Ploeg & Kiselyov (2014)](https://doi.org/10.1145/2633357.2633360) — Reflection Without Remorse
- `examples/knot-recovers-fix.md` — how the axioms force the GADT
