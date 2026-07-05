# Arrows and proarrows in circuits

`circuits` builds string diagrams, and string diagrams are the 2-cells of a
double category (or *proarrow equipment*). But `circuits` is deliberately
lightweight: it uses the vocabulary of proarrow equipment without depending on
proarrow-style category theory code.

## `arr` is a category arrow

In `circuits` the base structure is a Haskell `Category`:

```haskell
class Category arr where
  id  :: arr a a
  (.) :: arr b c -> arr a b -> arr a c
```

`arr a b` is an arrow from `a` to `b`. It does **not** need to be a
`Profunctor`:

```haskell
-- this is enough for Trace/Net
trace :: Costrong t arr => arr (t a x) (t a y) -> arr x y
```

Only operations that actually need two-sided action, such as `ambient`, add a
`Profunctor` constraint:

```haskell
ambientBy :: (Category arr, Profunctor arr, Strong t arr, Costrong t arr, Braided t) => ...
```

This means circuits works for any category, not just for profunctors.

## Relationship to proarrow equipment

A proarrow equipment has:

| Equipment concept | Circuits counterpart |
|---|---|
| Objects | Haskell types `a`, `b`, ... |
| Vertical arrows | Functors, e.g. `Identity`, `(s, -)`, `Either e -` |
| Horizontal arrows | Profunctors. For us, the base arrow `arr a b` plays this role. |
| 2-cells | `Trace t arr a b`, `Net t arr a b`, `Free sig arr a b` |

So `Trace` and `Net` are **free 2-cells** over the horizontal arrow `arr`.

The `Trace` datatype, for example, provides the 2-cell that closes a vertical
feedback loop via its `Knot` constructor:

```haskell
Knot :: arr (t a x) (t a y) -> Trace t arr x y
```

```
    t a x ----arr----> t a y
      |                  |
    trace              untrace
      |                  |
      x ------arr------> y
```

`Trace` also has an `Arr` constructor that embeds a base arrow.
A `Trace` value is already in normal form; `run` interprets it into the base
arrow using the `Costrong` / `Strong` instances.

## Arrow vs. proarrow

- An **arrow** / category gives composition (`id`, `.`).
- A **proarrow** / profunctor gives two-sided action (`dimap`).

Every proarrow is a category in one direction (the hom profunctor), but not
every category is a proarrow. In Haskell:

- `(->)` is both a `Category` and a `Profunctor`.
- `Kleisli m` is both when `m` is a `Functor`.
- An arbitrary GADT category may be a `Category` without a `Profunctor`
  instance.

Circuits stays at the `Category` level so that it does not force every base
arrow to be a profunctor. When an arrow happens to be a profunctor, the
proarrow equipment story lines up perfectly; when it is not, the string-diagram
machinery still works.

## Why not depend on `squares` or `proarrow`?

`squares` and `proarrow` are the real mathematical machinery. They are
valuable as reference and vocabulary, but `circuits` has a different goal:
evaluatable wiring diagrams with a small API.

Pulling in `squares` or `proarrow` would mean:

- Profunctor constraints almost everywhere.
- Kinds and type-level machinery that are powerful but not needed for the
  executables.
- A heavier conceptual footprint for users.

Instead, `circuits` borrows the *idea* of equipment/free 2-cells and implements
a concrete, executable fragment. The attachment to proarrow equipment is loose
and conceptual, not a code dependency. That feels like the right weight: the
vocabulary explains the design, but the library remains small and runnable.

## Optics as an example

`Circuit.Signature.Optic` is a concrete optic type built directly on a base
`Category` and a tensor `t`.  The residual is kept explicit in the type:

```haskell
data Optic t arr r a b = Optic
  { opticGet :: arr a (t r b)
  , opticPut :: arr (t r b) a
  }
```

* `Lens arr r a b = Optic (,) arr r a b` uses products for residuals.
* `Prism arr r a b = Optic Either arr r a b` uses coproducts for residuals.

Composition combines residuals, so an existential wrapper is the actual
category:

```haskell
data SomeOptic t arr a b where
  SomeOptic :: Optic t arr r a b -> SomeOptic t arr a b

type SigOptic t arr = Free SigCompose (SomeOptic t arr)
```

Specialised names are provided for the two common cases:

```haskell
type SomeLens arr = SomeOptic (,) arr
type SigLensCat arr = Free SigCompose (SomeLens arr)

type SomePrism arr = SomeOptic Either arr
type SigPrismCat arr = Free SigCompose (SomePrism arr)
```

The extra type parameter makes the residual visible to handlers.  In
particular, `SomeLens arr` has `Strong (,) (SomeLens arr)` and
`Costrong (,) (SomeLens arr)` instances, and `SomePrism arr` has the dual
`Strong Either (SomePrism arr)` and `Costrong Either (SomePrism arr)`
instances.  They braid an ambient wire past the residual and then use the base
arrow's `strength`/`costrength` to thread or close it.  So the free traced
category over lens diagrams folds back into `SomeLens arr`:

```haskell
type SigLensTrace arr = Trace (,) (SomeLens arr)
type SigPrismTrace arr = Trace Either (SomePrism arr)

foldTrace :: SigLensTrace arr a b -> SomeLens arr a b
```

This is an example of the general pattern: the equipment structure (here,
optics) lives in its own category, `Free SigCompose` over that category gives
the diagram syntax, and a handler folds it back using `Strong`/`Costrong` to
manage the residual channel.

## Spans and squares in Poly

`Circuit.Poly` now also has `Span` and `Square` types.  A `Span p q` is a
polynomial apex `m` with two morphisms `m -> p` and `m -> q`; a `Square` adds
vertical boundary morphisms, giving the proarrow-equipment picture:

```
      p' --span--> q'
       |            |
       v            v
       p ---------> q
```

The connection to optics is direct:

* A **prism** `Prism r a b` is span-shaped in Poly.  Its apex is
  `Exp (Either r b)`, with legs `match :: a -> Either r b` and
  `Right :: b -> Either r b`:

  ```haskell
  prismToSpan :: (a -> Either r b) -> Span (Exp (Either r b)) (Exp a) (Exp b)
  prismToSpan match = Span (ExpMap match) (ExpMap Right)
  ```

* A **lens** `Lens r a b` is cospan-shaped (the dual).  Its apex is
  `Exp (r, b)`, with legs `put :: (r, b) -> a` and `snd :: (r, b) -> b`:

  ```haskell
  lensToCospan :: ((r, b) -> a) -> Cospan (Exp a) (Exp b)
  lensToCospan put = Cospan (ExpMap put) (ExpMap snd)
  ```

So the residual `r` lands as part of the exponent of the mediating polynomial:
cartesian residuals project out (cospan), while cocartesian residuals inject in
(span).  Full horizontal composition of spans requires pullbacks in Poly, which
is the next step toward `SigPoly`.
