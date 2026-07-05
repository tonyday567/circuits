# A Knot Recovers Fix

<div align="center">

✦ · ✧ · ✦

*In which a GADT takes shape; a single pattern match enforces honesty; and between Trace and arr, Free is discovered.*

**[⟵ Prev: Marks and Stacks](01-marks-and-stacks.md)** · **[Next: Hyper Buries the Knot ⟶](03-hyper-buries-the-knot.md)**

</div>

---

Hyper gave us five marks on a single coinductive type. Now we want an initial
encoding — a syntax tree where constructors are visible, patterns are
inspectable, and the axioms become operational.

---

## Lift and Compose: The Free Category

The free category over a base arrow `arr` needs two constructors:

```haskell
data Free arr a b where
  Lift    :: arr a b -> Free arr a b
  Compose :: Free arr b c -> Free arr a b -> Free arr a c
```

`↑` is `Lift`. `⊙` is `Compose`. Axioms 1–3 hold by construction. `Free`
is the plain free category — no tensor, no feedback. The `t` parameter
was removed because it was phantom once `Knot` was gone.

The canonical interpreter folds to a plain arrow:

```haskell
runFree :: (Category arr) => Free arr a b -> arr a b
runFree (Lift f)       = f
runFree (Compose f g)  = runFree f . runFree g
```

Two constructors. No `Traced` constraint. This is the free category — the
moves of FP, with no feedback. Historically we didn't discover `Free`
until after building the full `Trace` GADT. It's presented first here
because it's logically prior, even if it came chronologically later.

---

## Adding Knot: The Free Traced Category

Axiom 4 (`⥁ (↑ f) = fix f`) says: for any base arrow `f :: (a,b) → (a,c)`,
there must be an arrow `b → c` that feeds `a` back into itself. The free
category can't express this. We need a new constructor.

Where `Arr` has type `arr a b`, a feedback constructor takes an arrow
with a channel on both sides — `arr (t a b) (t a c)` — and closes the
channel, producing `arr b c`:

```haskell
data Trace t arr a b where
  Arr   :: arr a b -> Trace t arr a b
  Knot  :: arr (t a b) (t a c) -> Trace t arr b c
```

Sequential composition is handled by the `Category` instance, using `(.)`
or `(>>>)`; there is no `Compose` constructor. The `Knot` body is a base
arrow, not a nested `Trace`. This keeps the GADT in normal form: every
feedback loop is tied directly to a base-arrow body. `Net` still permits
nested structure inside `Knot` bodies, but `Trace` itself is the
inspectable, already-normalised layer.

---

## run: The First Interpreter

To eliminate a `Trace` to a plain arrow, we need a `Traced` instance on
the base arrow — something that knows how to close a feedback channel:

```haskell
class Traced arr t where
  trace   :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)
```

For `arr = (->)` and `t = (,)`:

```haskell
instance Traced (->) (,) where
  trace f b   = let (a, c) = f (a, b) in c
  untrace     = fmap
```

The interpreter handles `Knot` by calling `trace`:

```haskell
run :: (Category arr, Traced arr t) => Trace t arr a b -> arr a b
run (Arr f)  = f
run (Knot k) = trace k
```

But this has a fault line.

---

## The Fault Line: Knot on the Left

Sequential composition after a `Knot`:

```haskell
run (Knot f . Arr g) = trace f . g    -- WRONG
```

This applies `trace` first, then composes `g` once at the exit. But
axiom 6 (sliding) requires `g` to participate *inside* every iteration.
The correct form threads `g` into the feedback channel before closing:

```haskell
run (Knot f . Arr g) = trace (f . untrace g)   -- CORRECT
```

The difference: `untrace` lifts `g` into the tensor, so it rides the
feedback channel. On each iteration, `g` runs on the payload while the
channel passes through untouched.

Without this case, `Knot` collapses to `Arr (trace ...)` — the
degenerate model where cyclic sharing becomes mere recursion. One
step separates the free traced monoidal category from collapse.

This sliding/Mendler case is enforced by the `Category` instance for
`Trace`; `run` then interprets the resulting normal form. Either way,
it's the same structural fact, the same operational content.

---

## Normal Form: `Trace` Is Already Normalised

`Trace` is `Free` plus `Knot`, but with a key difference: it has no
`Compose` constructor. Sequential composition lives in the `Category`
instance, which reduces composites to the normal form `Trace` already
exposes. There is therefore no separate `freeze` pass; the old
`freeze` interpreter has been removed.

The Mendler sliding case is enforced while building that normal form.
`run` becomes the direct interpretation:

```haskell
run :: (Category arr, Traced arr t) => Trace t arr x y -> arr x y
run (Arr f)  = f
run (Knot k) = trace k
```

`Trace` eliminates feedback by calling the base arrow's `trace`; `runFree`
still folds `Free` to a plain arrow. The separation is clean: `Free` knows
nothing about `Traced`. `run` is where the trace structure is
operationalized.

---

## The GADT Hierarchy

Putting it together:

```
                constructor added
Free            Lift, Compose          free category
Trace           + Arr, Knot            free traced category
Net             + Par, Copy, Add, ...  free traced PROP with bimonoid
```

And the interpreters:

```
run     :: Trace → arr        apply base-arrow trace to normal form
melt    :: Net → Trace        eliminate structural rows into Arr
runFree :: Free → arr         fold the free category
weave   :: Net → arr          = run . melt
```

The Mendler sliding case is enforced by the `Category` instance for
`Trace` and, implicitly, by `weave` (for `Net.Knot`, via `run . melt`).
It appears at two types because `Knot` appears twice in the GADT
hierarchy. This is not duplication — it's the same structural fact
applied at two different levels.

---

## Summary

`Free` is the free category. `Trace` adds `Arr` and `Knot`. Because
`Trace` has no `Compose` constructor, it is already in normal form;
`run` eliminates `Knot` by calling the base arrow's `trace`, with the
Mendler sliding case enforced by the `Category` instance. `runFree` still
folds `Free` to a plain arrow.

`Free` was discovered after `Trace` — extracted from it by observing
that `Lift` and `Compose` form a complete sub-language that never
mentions `Traced`. The discovery simplified `run`, clarified the
relationship to `Hyper` (chapter 03), and made explicit what was
previously implicit.

**Next:** [03-hyper-buries-the-knot.md](03-hyper-buries-the-knot.md) — Hyper as the final encoding;
the triangle identity; how `lift . trace = trace . lift` makes the
factorization work.

---

## References

- [Launchbury, Krstic & Sauerwein (2013)](https://doi.org/10.4204/eptcs.129.9) — axioms and the degenerate model
- [Joyal, Street & Verity (1996)](https://doi.org/10.1017/s0305004100074338) — traced monoidal categories
- [Hasegawa (1997)](https://doi.org/10.1007/978-1-4471-0865-8_7) — recursion from cyclic sharing
- [axioms.md](axioms.md) — proofs for all five axioms
