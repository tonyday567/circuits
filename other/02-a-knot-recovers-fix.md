# A Knot Recovers Fix

<div align="center">

✦ · ✧ · ✦

*In which we learn to slide; try our hand at a GADT; tie a lazy knot that and find a single pattern match.*

**[⟵ Prev: Marks and Stacks](01-marks-and-stacks.md)** · **[Next: Hyper Buries the Knot ⟶](03-hyper-buries-the-knot.md)**

</div>

---

[01](01-marks-and-stacks.md) gave us six axioms on `Hyper`. Now we build
the initial encoding — a GADT where the constructors are visible and the
axioms become operational. The path is concrete first, abstract later.

---

## Axioms 1–3: Lift and Compose

The free category is two constructors:

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
```

`↑` is `Lift`. `⊙` is `Compose`. Axioms 1–3 hold by construction —
associativity from `Compose`, identity from `Lift id`, functoriality from
`↑ (f . g) = ↑ f ⊙ ↑ g`.

Two constructors. If we stopped here we'd have the free category — FP's
core moves, no feedback.

---

## Axiom 4: The Type Change

```
⥁ (↑ f)  =  fix f
```

In `Hyper`, `run` ties the self-referential knot and `lift` embeds. In the
initial encoding, we need a constructor that carries a feedback
channel — a place for the fixed point to live.

The channel is a pair `(,)`. Where `Lift` has type `arr a b`, a feedback
constructor needs `arr (a, b) (a, c)` — the `a` feeds back:

```haskell
Knot' :: arr (a, b) (a, c) -> Circuit arr (,) b c
```

`Knot'` is `Lift` with a type change: `(a, _)` wraps the arrow. The `a`
is the feedback channel. This is axiom 4 in constructor form: the type
change transfers `fix` to the other side of the initial encoding.

The `(,)` is concrete for now. We'll abstract it later.

---

## First Draft of reify'

With `Lift`, `Compose`, and `Knot'`, a first interpreter:

```haskell
reify' :: Circuit (->) (,) a b -> (a -> b)
reify' (Lift f)      = f
reify' (Compose f g) = reify' f . reify' g
reify' (Knot' f)     = trace' f
  where
    -- Arrow.loop, specialised to (,)
    trace' :: ((a, b) -> (a, c)) -> (b -> c)
    trace' f b = let (a, c) = f (a, b) in c
```

This compiles. The Fibonacci stream runs:

```haskell
>>> let fibs = Knot' (\(fibs, i) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs !! i))
>>> reify' fibs 0
0
>>> reify' fibs 4
3
```

It is easy to believe this is complete. It is not.

---

## The Fault Line: Knot on the Left

Compose something after a `Knot'`:

```haskell
reify' (Compose (Lift (* 2)) fibs)
```

The naive `reify'` gives:

```
reify' (Compose (Knot' f) g) = trace' f . reify' g    -- WRONG
```

It applies `trace' f` immediately, then composes `reify' g` once at the
exit. Axiom 6 requires `g` to participate *inside* every iteration:

```
reify' (Compose (Knot' f) g) = trace' (f . second (reify' g))    -- CORRECT
```

The difference: `second (reify' g)` = `untrace` for `(,)`. In the wrong
version, `reify' g` runs once at the end. In the correct version, it
runs on the output channel every iteration.

---

## The Mendler Case

The fix is one extra pattern match, inserted before the general
`Compose` case:

```haskell
reify' (Lift f)                = f
reify' (Compose (Knot' f) g)   = trace' (f . second (reify' g))   -- Mendler
reify' (Compose f g)           = reify' f . reify' g
reify' (Knot' f)               = trace' f
```

The order is load-bearing. Without the `Compose (Knot' f) g` case
appearing before the general `Compose` case, the pattern falls through
and produces the naive — incorrect — behaviour.

Each case corresponds to one axiom:

| Case | Axiom | What it does |
|------|-------|--------------|
| `Lift f` | `↘ . ↑ = id` | Faithful embedding |
| `Compose f g` | Associativity | Composes interpretations |
| `Knot' f` | Axiom 4 | Closes the feedback channel via `trace'` |
| `Compose (Knot' f) g` | Axiom 6 | Threads `g` into the channel before tracing |

The `Compose (Knot' f) g` case must appear before the general `Compose`
case — the order is load-bearing. The name "Mendler" comes from
Mendler-style recursion, where the recursive call is guarded by a
constructor match. Here the constructor being matched is `Knot'` inside
a `Compose`; the guard is the single pattern match that threads `g`
into the feedback channel before closing the loop.

Without the Mendler case, `Knot'` becomes observationally equivalent to
`↑ (trace' f)` — the feedback channel closes immediately, the loop
structure is lost. This is the **degenerate model**: `Knot f` collapses
to `Lift (trace f)`, reducing cyclic sharing to iterated fixed-point
application. Hasegawa (1997) proved this is the difference between
genuine cyclic sharing and mere recursion.

**One pattern match separates the free traced monoidal category from
the degenerate model.**

[Hasegawa (1997)](https://doi.org/10.1007/978-1-4471-0865-8_7) distinguishes two ways to achieve recursion:

- **Fixed-point combinator:** `fix f = f (fix f)`. Applies `f` repeatedly.
  Each application may duplicate resources.
- **Cyclic sharing:** Ties a cycle in the graph. The cycle is shared,
  not duplicated.

In `Circuit`:
- `Knot k` is cyclic sharing — the channel is held open through `Compose`
- `↑ (trace' k)` is the fixed-point combinator — the channel closes immediately

The Mendler case preserves the distinction. Without it, `Knot` collapses
to `↑ (trace' k)` — cyclic sharing becomes the fixed-point combinator.
The structural information (\"this is a shared cycle\") is lost. The
interpreter produced a result — just the wrong one.

---

## Abstracting Trace

The concrete `reify'` has `trace'` and `second` baked in for `(,)`.
Abstract them:

```haskell
class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)
```

For `(,)`:

```haskell
instance Trace (->) (,) where
  trace f b = let (a, c) = f (a, b) in c
  untrace = fmap    -- i.e. second
```

With `Trace`, `Knot'` generalises to `Knot` over any tensor `t`:

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  Knot    :: arr (t a b) (t a c) -> Circuit arr t b c
```

And `reify'` becomes `reify`:

```haskell
reify :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
reify (Lift f)             = f
reify (Compose (Knot f) g) = ↪ (f . ↩ (reify g))   -- Mendler case
reify (Compose f g)        = reify f . reify g
reify (Knot k)             = ↪ k
```

The Mendler case is now `↪ (f . ↩ (reify g))` — `trace` and `untrace`
in symbolic form. The concrete `second` and `trace'` have been absorbed
into the `Trace` instance.

---

## The Full GADT

Three constructors. The roles:

| Constructor | Axioms | Role |
|-------------|--------|------|
| `Lift` | 2, 3 | Embed base arrows; ↑ of the adjunction |
| `Compose` | 1 | Sequential composition |
| `Knot` | 4, 6 | Feedback channel; the trace constructor |

Axiom 4 (`⥁ (↑ f) = fix f`) shows that the final encoding can take fixed points of base arrows. The `Knot` constructor (together with the change of tensor) is what lets the *initial* encoding do the same thing: it gives us a canonical way to form fixed points of arrows `f : A ⊗ X → B ⊗ X` inside the free traced category.

Axiom 6 forces the Mendler case — the single pattern match that keeps the trace honest. Axiom 5 (centrality) introduces no new constructor; it constrains which tensors satisfy the axioms (see [04](04-holding-hands-or-taking-turns.md)).

The `Category` instance is immediate:

```haskell
instance (Category arr) => Category (Circuit arr t) where
  id  = Lift id
  (.) = Compose
```

### GADT ↔ Hyper

Each GADT primitive has a counterpart in the final encoding:

```
GADT                              Hyper
────────────────────────────────────────────────
Lift f                            lift f
Compose f g                       f . g
Knot f                            trace (lift f)
```

`push` has no direct GADT counterpart — it threads `f` through the
continuation channel, which is Hyper behavior, not GADT structure.
The GADT can express two related operations:

| GADT form | `reify` | what it does |
|-----------|---------|-------------|
| `Compose h (Lift f)` | `reify h . f` | `f` on input, then `h` (input-side) |
| `Compose (Lift f) h` | `f . reify h` | `h` first, then `f` on output (output-side) |

Neither is `push`.  `push f h` in Hyper applies `f` to the result of
invoking `h` with the continuation — it threads through the feedback
channel.  Under `encode`, `Compose (Lift f) h` maps to `lift f . encode h`;
`push f (encode h)` is different.  Both are first-class; neither
subsumes the other.

---

## The Universal Property

`Circuit arr t` is the **initial** (free) traced monoidal category over
`arr`. The universal property:

> For any traced monoidal category `C` and any (traced) functor
> `F : arr -> C`, there is a **unique** traced functor
> `F̂ : Circuit arr t -> C` making the triangle commute:
>
> ```
>     ↑
> arr -----> Circuit arr t
>  \               |
>   \          F̂  |
>    \             ↓
>     F ---------> C
> ```

`reify` is the instance where `C = arr` and `F = id`. It is the unique
traced functor from the free object back to the base. Every traced
functor out of `Circuit arr t` factors through `reify`.

---

## Summary

```
↘ (↑ f)         =  f                           -- faithful embedding
↘ (↮ k)         =  ↪ k                         -- trace closes the channel
↘ (↮ f ⊙ g)    =  ↪ (f . ↩ (↘ g))             -- Mendler case (sliding)
↘ (f ⊙ g)      =  ↘ f . ↘ g                    -- functoriality of ↘
```

Axiom 4 forces `Knot` — a type change on `Lift`. Axiom 6 forces the
Mendler case — a single pattern match in `reify`. The `Trace` typeclass
abstracts the concrete loop mechanism. `Circuit` is the free object.
`reify` is the unique elimination.

**Next:** [03-hyper-buries-the-knot.md](03-hyper-buries-the-knot.md) — Hyper as the final encoding; the
coinductive type; why sliding is structural there.

---

## References

- [Launchbury, Krstic & Sauerwein (2013)](https://doi.org/10.4204/eptcs.129.9) — axioms and the degenerate model
- [Joyal, Street & Verity (1996)](https://doi.org/10.1017/s0305004100074338) — traced monoidal categories
- [Hasegawa (1997)](https://doi.org/10.1007/978-1-4471-0865-8_7) — recursion from cyclic sharing; fixed points from traces
- [axioms.md](axioms.md) — proofs for all five axioms
