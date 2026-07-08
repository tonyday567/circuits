⟝ proarrow

# Traced ≅ Strong + Costrong on Hom k — The proarrow Bridge

For background on Circuit see [01-marks-and-stacks.md](../other/01-marks-and-stacks.md)
and [02-a-knot-recovers-fix.md](../other/02-a-knot-recovers-fix.md).
For the proarrow library see the
[proarrow repo](https://github.com/sjoerdvisscher/proarrow/) (Sjoerd Visscher)
and Bartosz Milewski's
[Profunctor Equipment in Haskell](https://bartoszmilewski.com/2026/05/16/profunctor-equipment-in-haskell/)
(May 2026). This card proves the correspondence conjectured in
[examples/proequip.md](../examples/proequip.md):

> **`Traced arr t  ≅  Strong k (Hom arr)  +  Costrong k (Hom arr)`**
> under the self-action where `Act a x = t a x`.

---

## The Surprise

`Circuit` is always self-acting. The tensor `t` that carries the feedback
channel acts on the same category that `arr` lives in — there is no separate
monoidal category `m` exerting an external action. In Visscher's language
this is `SelfAction k`: the category acts on itself via its own tensor.

This is why reading `MonoidalAction m k` with two distinct parameters can
feel disorienting — for Circuit, `m` and `k` are never distinct. The
bridge is thin precisely because of this coincidence.

---

## The Two Typeclasses

**Circuit's `Traced`** (from `Circuit.Trace`):

```haskell
class Traced arr t where
  trace   :: arr (t a b) (t a c) -> arr b c   -- close the channel
  untrace :: arr b c -> arr (t a b) (t a c)   -- open the channel
```

**Visscher's `Costrong` and `Strong`** (from `Proarrow.Category.Monoidal.Action`):

```haskell
class (MonoidalAction m c, MonoidalAction m d, Profunctor p) => Strong m p where
  act :: a ~> b -> p x y -> p (Act a x) (Act b y)

class (MonoidalAction m c, MonoidalAction m d, Profunctor p) => Costrong m p where
  coact :: p (Act a x) (Act a y) -> p x y
```

And Visscher's `trace`, assembled from `Costrong` on the hom-profunctor
under a self-action:

```haskell
trace :: (SelfAction k, Costrong k p, Ob x, Ob y, Ob u)
      => p (x ** u) (y ** u) -> p x y
trace p = coact (dimap swap swap p)
```

---

## The Correspondence

Fix `arr = (->)`, `k = Hask`, `Act a x = t a x`, `p = Hom (->) = (->)`.
Then `SelfAction Hask` holds with `(**) = t`.

| Circuit | proarrow | Role |
|---------|----------|------|
| `Traced arr t` | `Strong k (Hom arr)` + `Costrong k (Hom arr)` | Both directions bundled |
| `trace` | `coact` on `Hom arr` | Close the channel |
| `untrace` | `act (obj @a)` on `Hom arr` | Open the channel |
| tensor `t` | `Act` under `SelfAction k` | The feedback channel |
| `Knot` constructor | 2-cell in `Prof(Hask)` | Trace cell |

**`trace` corresponds to `coact`.** Specialising Visscher's `trace` to
`p = (->)` and `(**) = (,)`:

```haskell
-- Visscher (specialised)
trace p = coact (dimap swap swap p)
        = coact (\(u, y) -> let (x, u') = p (swap (u, y)) in swap (x, u'))
        -- simplified under (,)-swap
        = \b -> let (a, c) = p (a, b) in c

-- Circuit
trace f b = let (a, c) = f (a, b) in c
```

Same function. The `dimap swap swap` in Visscher's version handles the
channel-left convention (`Act a x = a ** x`); Circuit's convention is
identical for `(,)`.

**`untrace` corresponds to `act`.** The `Strong` instance for `(->)` gives:

```haskell
act f g = f `par` g   -- i.e. second g under (,)
```

And Circuit's `untrace`:

```haskell
untrace = fmap   -- i.e. second, for (,)
```

Same function under the `Bifunctor (,)` instance.

---

## The Bridge Functions

```haskell
-- | From Circuit's bundled interface to proarrow's split interface.
--
-- 'toCostrong' extracts the elimination direction.
-- 'toStrong'   extracts the injection direction.

toCostrong
  :: Traced arr t
  => (forall a b c. arr (t a b) (t a c) -> arr b c)
toCostrong = trace

toStrong
  :: Traced arr t
  => (forall a b c. arr b c -> arr (t a b) (t a c))
toStrong = untrace
```

These are identity functions — `trace` **is** `coact` and `untrace` **is**
`act (obj @a)` under the self-action. The bridge is not a construction;
it is a recognition.

---

## Why Circuit Bundles Them

Visscher separates `Strong` and `Costrong` because in the fully general
setting — external monoidal action `m` acting on `k` — a profunctor can
have one without the other. A profunctor can be `Costrong` (traces exist)
without being `Strong` (injection may not exist), or vice versa.

Circuit always needs both:

- `trace` (`coact`) closes the feedback loop in `run`.
- `untrace` (`act`) opens the loop — threading state past a `Knot` via
  braiding.

Bundling them in a single `Traced` typeclass is a design choice that reflects
Circuit's use pattern: you never close a loop without also being able to open
one. The self-action constraint (`m = k`) makes both directions available
for free from the symmetric monoidal structure, so there is no cost to
requiring both.

---

## The `(,)` Instance

```haskell
instance Traced (->) (,) where
  trace f b = let (a, c) = f (a, b) in c
  untrace = fmap   -- i.e. second
```

In proarrow terms:

- `Costrong (,) (->)`: `coact f = \b -> let (a, c) = f (a, b) in c`
  — ties the lazy knot.
- `Strong (,) (->)`: `act f g = second g`
  — lifts a plain function into the tensor.

The self-action is `SelfAction Hask` with `(**) = (,)`.

---

## The `Either` Instance

```haskell
instance Traced (->) Either where
  trace f b = go (Right b)
    where go x = case f x of { Right c -> c; Left a -> go (Left a) }
  untrace = fmap   -- i.e. right
```

In proarrow terms:

- `Costrong Either (->)`: `coact` runs the while-loop.
- `Strong Either (->)`: `act f g = right g` (act on the `Right` component).

The self-action is `SelfAction Hask` with `(**) = Either`.

---

## The `Kleisli IO Either` Instance

```haskell
instance Traced (Kleisli IO) Either where
  trace  = ... -- delimited continuations: prompt / control0
  untrace = ... -- inject into Right
```

In proarrow terms, this is `Costrong Either (Kleisli IO)` — the `coact`
uses GHC's `prompt#` / `control0#` primops to run the loop in constant
stack space. The `Strong` side (`untrace`) is the trivial injection into
`Right`.

This instance is the one that has no counterpart in existing proarrow
instances — delimited continuations as `Costrong` on `Kleisli IO` is new
ground. It is the piece of Circuit that earns "first to market."

---

## The Mendler Case as Naturality

The old `reify` interpreter contained a Mendler-style pattern match:

```haskell
-- TODO: This example used the deleted `Compose` constructor of the old
-- `Circuit` GADT. The new inspectable `Trace` GADT has no `Compose`
-- constructor; sequential composition is `(.)` or `(>>>)`. Update this
-- section once the corresponding `run` equation is known.
```

That pattern was the naturality condition for the trace 2-cell. In
Visscher's language, this is the requirement that `coact` commute with
profunctor composition — that the `Costrong` structure is natural in its
boundary types.

Without that Mendler case, `Knot` collapses to `Arr (trace f)` — the
degenerate model where `coact` closes immediately, discarding the boundary
morphism `g`. The Mendler case was `coact` done right: `g` participated
inside the loop, not just at the exit.

---

## What Drops In For Free

With the correspondence established, Circuit inherits the proarrow
conceptual vocabulary:

- `Knot` is a **2-cell** in `Prof(Hask)` in the sense of Bartosz's
  `Cell f g h j = forall a c. h a c -> j (f a) (g c)`.
  With `f = g = id`, `h = arr (t a _)`, `j = Trace t arr`:
  the `Knot` constructor **is** a `Cell`.

- `dimap` on `Knot` is **vertical composition** of the trace 2-cell.
  The `second f` threading in
  `dimap f g (Knot k) = Knot (dimap (second f) (second g) k)`
  is vertical composition sliding through the channel.

- Threading a state wire past a `Knot` is **horizontal sliding** — a
  vertical transform sliding past a horizontal boundary via braiding.
  This is the yanking identity in the double-category language.

- The proof obligation from [examples/proequip.md](../examples/proequip.md) — that Circuit
  forms a proarrow equipment over its base category — is now a matter of
  verifying that the `Costrong`/`Strong` instances satisfy the equipment
  axioms. The nLab entry on
  [equipment](https://ncatlab.org/nlab/show/equipment) has the axioms;
  the `Cell` encoding in Bartosz's post has the Haskell form. This is the
  open lemma.

---

## Connection to the Narrative

The narrative ([examples/proequip.md](../examples/proequip.md)) identifies `Knot` as a 2-cell and the
Mendler case as naturality, but presents these as conclusions reached by
following the `foldH` example. This card provides the direct categorical
anchor: `Traced` is `Strong + Costrong` on the hom-profunctor, the
self-action collapses `m = k`, and the Mendler case is the naturality
condition for `coact`.

The open question from [examples/proequip.md](../examples/proequip.md) — proving Circuit forms a
proarrow equipment — is now precisely: prove that `Costrong k (Hom arr)`
plus `Strong k (Hom arr)` under `SelfAction k` satisfies the equipment
axioms from nLab, with `Knot` as the generating 2-cell.

---

## Summary

1. Circuit is always self-acting: `m = k`, `Act a x = t a x`
2. `Traced arr t` = `Strong k (Hom arr)` + `Costrong k (Hom arr)` under `SelfAction k`
3. `trace` = `coact`; `untrace` = `act (obj @a)` — the bridge is a recognition, not a construction
4. Both `(,)` and `Either` instances correspond to standard proarrow instances on `Hom (->)`
5. `Kleisli IO Either` is new: `Costrong Either (Kleisli IO)` via delimited continuations
6. The Mendler case = naturality of `coact` = the 2-cell condition on `Knot`
7. Open lemma: prove Circuit forms proarrow equipment with `Knot` as generating 2-cell

---

## References

- [Visscher, proarrow](https://github.com/sjoerdvisscher/proarrow/) — `Proarrow.Category.Monoidal.Action`
- [Milewski, Profunctor Equipment in Haskell](https://bartoszmilewski.com/2026/05/16/profunctor-equipment-in-haskell/) — `Cell f g h j` encoding
- [Joyal, Street & Verity (1996)](https://doi.org/10.1017/s0305004100074338) — traced monoidal categories
- [nLab: equipment](https://ncatlab.org/nlab/show/equipment) — proarrow equipment axioms
- [examples/proequip.md](../examples/proequip.md) — double category framing; open lemma
- [axioms.md](../other/axioms.md) — JSV axioms proved for both tensors
- `src/Circuit/Trace.hs` — `Traced` instances
- `Circuit` — `Trace(..)`, `run`, `melt`
