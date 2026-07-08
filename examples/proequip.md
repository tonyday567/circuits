# foldH ⟜ coroutining folds, profunctor equipment

> **Design-only / exploratory.** This card explores the profunctor-equipment
> structure of `Trace`/`Hyper`. The formal lemmas remain open.

Coroutining folds via Hyper (LKS 2013), plus the double-category /
profunctor-equipment structure they reveal (Milewski 2026).
Concrete example first; categorical framing second.

Translation of the coroutining fold from Launchbury, Krstic &
Sauerwein (2013) into circuits' `Hyper`.  Two folds share a
continuation, interleaving element-by-element — the thing `foldr`
alone cannot express.

```haskell
-- $setup
-- >>> import Circuit
-- >>> import Data.These
-- >>> import Prelude hiding (id, (.))
-- >>> import Control.Category
```

---

## foldH

```haskell
foldH :: [a] -> (a -> b -> c) -> c -> Hyper b c
foldH []     c n = base n
foldH (x:xs) c n = Hyper (\k -> c x (invoke k (foldH xs c n)))
```

Each element `c x` suspends inside the continuation `k`.  The `runHyper`
collapses the Hyper to `foldr`:

```haskell
-- >>> runHyper (foldH [1,2,3] (+) 0)
-- 6
-- >>> runHyper (foldH [1,2,3] (:) [])
-- [1,2,3]
```

Equivalence: `foldr c n xs = runHyper (foldH xs c n)`.

Using `push` to build the chain:

```haskell
foldH []     c n = base n
foldH (x:xs) c n = push (c x) (foldH xs c n)
```

---

## The dual — `(:)` and `push`

Write `foldr` and `foldH` side by side:

```haskell
foldr  :: (a -> b -> b) -> b -> [a] -> b
foldr  c n []     = n
foldr  c n (x:xs) = c x (foldr c n xs)

foldH  :: [a] -> (a -> b -> c) -> c -> Hyper b c
foldH  []     c n = base n
foldH  (x:xs) c n = push (c x) (foldH xs c n)
```

`(:)` attaches to the outside of a list.  `push` threads into the inside
of a Hyper, through the continuation channel.  Same shape, flipped
polarity.

`push` is the Hyper-level primitive for threading a function through the
feedback channel.  The `Trace` GADT has no direct counterpart; `Arr f . h`
(post-composition on `run`) is the closest analogue but not equivalent.
`push f h` applies `f` to the value the continuation feeds back,
before `h` sees it — a structural dual of `(:)` which attaches
to the outside.

---

## Stripping the algebra

Because `push` and `(:)` play the same structural role, the element
function `c x` is just a parameter.  Drop it to expose the bare fold:

```haskell
foldr'  :: [a]     -> [a]     -> [a]
foldr'  []     = id
foldr'  (f:fs) = (:) f . foldr' fs

foldh'  :: [a -> b] -> Hyper a b -> Hyper a b
foldh'  []      = id
foldh'  (f : fs) = push f . foldh' fs
```

`foldH` is `foldh'` with the `c x` pre-applied and `base n` as seed:

```haskell
foldH xs c n = foldh' (map c xs) (base n)
```

Both folds build an endofunction chain.  `foldr'` builds `[a] -> [a]`
via cons.  `foldh'` builds `Hyper a b -> Hyper a b` via push.  The
λ-term is identical — the generator is the only difference.

At `Hyper a a` the types align perfectly:

```
foldr'  :: [a -> a] -> [a -> a]   -> [a -> a]
foldh'  :: [a -> a] -> Hyper a a  -> Hyper a a
```

Both are `[τ] -> M -> M` — a list of endofunctions folded into an
endofunction carrier.  `(:)` and `push` are dual representations of
the same endofunction stack.

---

## zip — two folds, one continuation

The continuous channel has type `Maybe (b, [b])` — an uncons token.
`Nothing` says the list is empty; `Just (y, ys)` hands the head to
the other fold and carries the tail forward.

```haskell
zipH :: [a] -> [b] -> [(a, b)]
zipH xs ys = runHyper (foldH xs first [] . foldH ys second Nothing)
  where
    first x Nothing          = []
    first x (Just (y, xys))  = (x, y) : xys
    second y xys             = Just (y, xys)
```

```haskell
-- >>> zipH [1,2,3] [10,20,30]
-- [(1,10),(2,20),(3,30)]
-- >>> zipH [1,2] [10,20,30]
-- [(1,10),(2,20)]
-- >>> zipH [1,2,3] [10]
-- [(1,10)]
```

The two folds coroutine through `(.)`.  `first` needs a `y` before it
can emit — `second` provides it.  `second` just uncons-es and passes
the token.  The zip output spine is lazy: forcing the first pair does
not force the rest of either input list.

### Variation: These

`Maybe (b, [b])` bundles the element and remainder as a product.  
`These b [(a,b)]` separates them — the element is the payload,
the `[(a,b)]` is the accumulated output passed through the channel.
`These` makes the coroutine structure visible in the type.

From `Data.These` (`these` package):

```haskell
data These a b = This a | That b | These a b
```

`That` is the empty signal (no element).  `These element remainder`
carries the token.  `This` handles the final element with no remainder.

```haskell
zipHThese :: [a] -> [b] -> [(a, b)]
zipHThese xs ys = runHyper (foldH xs first (That []) . foldH ys second (That []))
  where
    first x (This y)      = [(x, y)]
    first x (These y ys)  = (x, y) : ys
    first x (That _)      = []
    second y xs'          = These y xs'
```

`second` always produces `These y xs'` — hands the element forward.
`first` matches three cases: `This` (final element), `These` (element
+ remainder), `That` (other list empty).  The three-way pattern match
replaces the two-way `Maybe`, making the end-of-stream case (`This`)
explicit rather than collapsing it into `These` with an empty remainder.

---

## double category — vertical and horizontal

The zip has two independent composition layers.

**Horizontal** — the coroutine pipeline.  `foldH xs _ . foldH ys _`
is composition in the category of profunctors.  The channel token
(`These b [(a,b)]`) is the profunctor that carries elements between
the two folds.

**Vertical** — the element transform.  `combine x :: These b [(a,b)] -> [(a,b)]`
maps the channel profunctor to the output profunctor.  `lmap (,)`, `lmap bin`,
or `id` are vertical functors — they transform the elements flowing
through the pipeline without affecting the pipeline structure.

In the language of double categories and profunctor equipment
(Milewski 2026, nLab):

| structure | zip instance |
|---|---|
| object | type at a handoff point |
| horizontal arrow (profunctor) | `foldH xs _` or `foldH ys _` |
| vertical arrow (functor) | `first`, `combine`, `id` |
| 2-cell (square) | the per-element step `(x,y) : ys` |

`foldH ys These _` is the **conjoint** (`Star` in Bartosz's encoding):
pure supply — elements pass through unmodified.  This leaves the vertical
slot open, so we can swap `(,)` for `bin` without touching the pipeline:

```haskell
zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith bin xs ys = runHyper (foldH xs combine (That []) . foldH ys These (That []))
  where
    combine x (This y)      = [bin x y]
    combine x (These y ys)  = bin x y : ys
    combine x (That _)      = []
```

The yanking identities (Bartosz, "Bending, Yanking, and Cartesian Squares
in Double Categories", May 2026) guarantee that vertical transforms
commute with horizontal composition — batching, mapping, or other
per-element transformations can slide along the pipeline without
changing the result.

The 2-cell encoding in Haskell (from Bartosz's "Profunctor Equipment
in Haskell"):

```haskell
type Cell f g h j = forall a c. h a c -> j (f a) (g c)
```

In our zip, `h = These b` (channel), `j = (->) [(a,b)]` (output),
`f = combine` (vertical left), `g = id` (vertical right).
The `foldH` mechanism is a particular construction of such cells
via coroutining.

---

## Knot is a 2-cell

The `Trace` constructor `Knot` has the same shape as `Cell`:

```haskell
Knot :: arr (t a b) (t a c) -> Trace t arr b c
```

With `f = g = id`, `h = arr ∘ (t a)`, `j = Trace t arr`:

```haskell
-- Cell id id (arr ∘ (t a)) (Trace t arr)
```

`Knot` is a natural 2-cell in its boundary types.  The `dimap` instance
on `Knot` is vertical composition — `second f` threads through the
channel:

```haskell
dimap f g (Knot k) = Knot (dimap (second f) (second g) k)
```

The `Category` instance on `Trace` supplies the horizontal-composition
cases for `Knot`:

```haskell
Knot f . Arr g = Knot (f . untrace g)
Arr f . Knot g = Knot (untrace f . g)
```

Without them, `Knot` would collapse to `Arr (trace f)` — the degenerate
model where the trace closes immediately.  These cases guarantee that
vertical transforms (`g`) participate *inside* the loop, not just at
the exit.

This is what tightening says in the traced monoidal axioms:

```
tr((g ⊗ id) ∘ f ∘ (h ⊗ id)) = g ∘ tr(f) ∘ h
```

Vertical transforms on the payload commute with the trace.  The
`Category` cases are the operational form of tightening — and the
`dimap` instance on Knot is the type-level form.

### The `ambient` combinator

`ambient` is `ambientBy braid`.  It threads a state wire alongside a
circuit, sliding past `Knot` via braiding:

```haskell
ambientBy braid (Knot k) = Knot (dimap braid braid (untrace k))
```

State slides past Knot via braiding — vertical composition across
the horizontal boundary.  This is the sliding axiom wearing
double-category clothes.

## The breadcrumb trail

1. **foldH** — looked like foldr with push instead of (:).
2. **push** — the generator in Hyper-space. Hyper-specific; no direct Trace equivalent.
3. **foldr' / foldh'** — identical λ-term, different Endo monoids.
4. **zip** — two orthogonal composition layers, independent.
5. **zipWith** — `foldH ys These _` as conjoint, vertical slot open.
6. **These** — the channel type as a profunctor between folds.
7. **Cell f g h j** — Bartosz's encoding of 2-cells in Prof.
8. **Knot as 2-cell** — same shape, dimap = vertical composition.
9. **Category cases as naturality** — the equations enforce Cell structure.
10. **The Trace GADT is a double category** — not layered on; the constructors enforce it.

## Open lemmas

**Proarrow equipment.** Prove that `Trace` with its `Category` and
`Traced` instances forms a proarrow equipment over its base category.
The nLab entry on
[equipment](https://ncatlab.org/nlab/show/equipment) has the axioms; the
`Cell` encoding above has the Haskell form.  From
[proarrow.md](proarrow.md): `Trace t arr ≅ Strong k (Hom arr) + Costrong k (Hom arr)`
under `SelfAction k`.  The bridge is established — the formal lemma is
next.

**The Either 2-cell.** `Trace` already supports the `Either` tensor via
the `Traced` instance; does `dimap` on `Knot` extend cleanly?  The
parser's `<|>` is composition of 2-cells in the Either equipment — a
worked example for the Either tensor would make the connection concrete.

**The Kleisli equipment.** The `ambient` combinator already threads state;
does the vertical structure lift through `Kleisli m`?  The
delimited-continuation `Traced` instance for `Kleisli IO` should form a
2-cell — a worked example showing the Cell structure in effectful
circuits.

**Structural 2-cells beyond trace.** [lawvere.md](lawvere.md) identifies
`Curry`/`UnCurry` (exponential adjunction) as the next structural 2-cell
after `Knot`.  What's the 2-cell for distributive categories?  For linear
logic?  The design direction: Circuit as a free category with accumulating
structural 2-cells.

## reference

Launchbury, Krstic & Sauerwein, *Coroutining Folds with Hyperfunctions*,
EPTCS 129, 2013, pp. 121–135.  doi:10.4204/EPTCS.129.9

Milewski, *Profunctor Equipment in Haskell*, May 2026.
— *Bending, Yanking, and Cartesian Squares in Double Categories*, May 2026.
https://bartoszmilewski.com/

nLab: [double category](https://ncatlab.org/nlab/show/double+category),
[profunctor](https://ncatlab.org/nlab/show/profunctor),
[equipment](https://ncatlab.org/nlab/show/equipment)

[proarrow.md](proarrow.md) — `Trace t arr ≅ Strong + Costrong` under self-action
[lawvere.md](lawvere.md) — comparative engineering; structural 2-cells
