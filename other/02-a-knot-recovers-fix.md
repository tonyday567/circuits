# A Knot Recovers Fix

<div align="center">

✦ · ✧ · ✦

*In which a GADT takes shape; a single pattern match enforces honesty; and between Circuit and arr, Free is discovered.*

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

Two constructors. No `Trace` constraint. This is the free category — the
moves of FP, with no feedback. Historically we didn't discover `Free`
until after building the full `Circuit` GADT. It's presented first here
because it's logically prior, even if it came chronologically later.

---

## Adding Knot: The Free Traced Category

Axiom 4 (`⥁ (↑ f) = fix f`) says: for any base arrow `f :: (a,b) → (a,c)`,
there must be an arrow `b → c` that feeds `a` back into itself. The free
category can't express this. We need a new constructor.

Where `Lift` has type `arr a b`, a feedback constructor takes an arrow
with a channel on both sides — `arr (t a b) (t a c)` — and closes the
channel, producing `arr b c`:

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  Knot    :: Circuit arr t (t a b) (t a c) -> Circuit arr t b c
```

The `Knot` body is a `Circuit`, not a base arrow. This is load-bearing:
a `Knot` can contain `Compose`, which can contain another `Knot`. The
feedback structure nests. And `transpose` (in `Circuit.Net`) can reach
inside `Knot` bodies because they're inspectable `Circuit` values, not
opaque arrows.

---

## reify: The First Interpreter

To eliminate a `Circuit` to a plain arrow, we need a `Trace` instance on
the base arrow — something that knows how to close a feedback channel:

```haskell
class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)
```

For `arr = (->)` and `t = (,)`:

```haskell
instance Trace (->) (,) where
  trace f b   = let (a, c) = f (a, b) in c
  untrace     = fmap
```

The naive interpreter handles `Knot` by calling `trace`:

```haskell
reify (Lift f)       = f
reify (Compose f g)  = reify f . reify g
reify (Knot k)       = trace (reify k)
```

But this has a fault line.

---

## The Fault Line: Knot on the Left

Compose something after a `Knot`:

```haskell
reify (Compose (Knot f) g) = trace (reify f) . reify g    -- WRONG
```

This applies `trace` first, then composes `g` once at the exit. But
axiom 6 (sliding) requires `g` to participate *inside* every iteration.
The correct form threads `g` into the feedback channel before closing:

```haskell
reify (Compose (Knot f) g) = trace (reify f . untrace (reify g))   -- CORRECT
```

The difference: `untrace` lifts `g` into the tensor, so it rides the
feedback channel. On each iteration, `g` runs on the payload while the
channel passes through untouched.

Without this case, `Knot` collapses to `Lift (trace ...)` — the
degenerate model where cyclic sharing becomes mere recursion. One
pattern match separates the free traced monoidal category from collapse.

This pattern match — the Mendler case — used to live in `reify`. It
now lives in `freeze` (see below). Either way, it's the same one
pattern match, the same operational content.

---

## freeze: Separating the Free Category from the Trace

`Circuit` is `Free` plus `Knot`. The map that dissolves `Knot` into
`Lift` by calling the base arrow's `trace`:

```haskell
freeze :: (Category arr, Trace arr t) => Circuit arr t a b -> Free arr a b
freeze (Lift f)                = Lift f
freeze (Compose (Knot f) g)    = Lift (trace (runFree (freeze f) . untrace (runFree (freeze g))))
freeze (Compose f g)           = Compose (freeze f) (freeze g)
freeze (Knot k)                = Lift (trace (runFree (freeze k)))
```

The Mendler case lives here. `reify` becomes the composition:

```haskell
reify :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
reify = runFree . freeze
```

`freeze` eliminates `Knot` into `Free`, then `runFree` folds to a plain
arrow. The separation is clean: `Free` knows nothing about `Trace`.
`freeze` is where the trace structure is operationalized.

---

## The GADT Hierarchy

Putting it together:

```
                constructor added
Free            Lift, Compose          free category
Circuit         + Knot                 free traced category
Net             + Par, Copy, Add, ...  free traced PROP with bimonoid
```

And the interpreters:

```
freeze  :: Circuit → Free     eliminate Knot into base-arrow trace
melt    :: Net → Circuit     eliminate structural rows into Lift
runFree :: Free → arr         fold the free category
reify   :: Circuit → arr      = runFree . freeze
loom    :: Net → arr          = reify . melt
```

The Mendler case appears in `freeze` (for `Circuit.Knot`) and implicitly
in `reify` (for `Net.Knot`, via `reify . melt`). It appears twice in the
interpreter chain because `Knot` appears twice in the GADT hierarchy.
This is not duplication — it's the same structural fact applied at two
different types.

---

## Summary

`Free` is the free category. `Circuit` adds `Knot`. `freeze` eliminates
`Knot` by calling the base arrow's `trace`, with the Mendler case
enforcing the sliding axiom. `reify` is the composition `runFree . freeze`.

`Free` was discovered after `Circuit` — extracted from it by observing
that `Lift` and `Compose` form a complete sub-language that never mentions
`Trace`. The discovery simplified `reify`, clarified the relationship to
`Hyper` (chapter 03), and made explicit what was previously implicit.

**Next:** [03-hyper-buries-the-knot.md](03-hyper-buries-the-knot.md) — Hyper as the final encoding;
the triangle identity; how `lift . trace = trace . lift` makes the
factorization work.

---

## References

- [Launchbury, Krstic & Sauerwein (2013)](https://doi.org/10.4204/eptcs.129.9) — axioms and the degenerate model
- [Joyal, Street & Verity (1996)](https://doi.org/10.1017/s0305004100074338) — traced monoidal categories
- [Hasegawa (1997)](https://doi.org/10.1007/978-1-4471-0865-8_7) — recursion from cyclic sharing
- [axioms.md](axioms.md) — proofs for all five axioms
