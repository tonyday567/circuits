# Layer algebra

The circuits library is a tower of free constructions over a base arrow
`arr :: Cat2`.  This note records the syntax/semantics dictionary and the
conversions between layers.

## Vocabulary

```haskell
type Cat2 = Type -> Type -> Type

type NT p q = forall x y. p x y -> q x y
type arr :~> arr' = NT arr arr'

type HNT f g = forall arr. f arr :~> g arr
type f :~~> g = HNT f g
```

An `NT` is a map between arrows (profunctors).  An `HNT` is a map between
layers, natural in the base arrow.

## Syntax atoms

Every layer adds one kind of structure as a constructor.

| constructor | structure | semantic operation |
|---|---|---|
| `Lift` / `Arr` | embed a base arrow | `unit` |
| `Compose` | sequential composition | `(.)` |
| `Par` | tensor product of morphisms | `par` |
| `Swap` | symmetry / braiding | `swap` |
| `Knot` | trace / feedback | `trace` |
| `Copy`, `Discard` | comonoid | `copy`, `discard` |
| `Plus`, `Zero` | monoid | `plus`, `zero` |

`Lift` (in `Free`) and `Arr` (in `Trace`/`Net`) are the same operation:
the unit `arr :~> f arr` of the free construction.  The names differ by
historical accident.

## Layer compounds

Layers combine by taking the union of their constructors.  `+` is just
union of constructor sets.

```text
Free    = Lift + Compose
Mon     = Free + Par + Swap
        = Lift + Compose + Par + Swap
Trace     = Arr + Knot
          = Lift + Knot            (Arr is Lift)
TraceMon  = Mon + Knot
          = Free + Knot + Par + Swap
          = Lift + Compose + Par + Swap + Knot
Net       = TraceMon + Copy + Discard + Plus + Zero
```

- `Free` is the free category over `arr` (module `Circuit.Free`).
- `Mon` is the free symmetric monoidal category over `arr` (tensor is `(,)`);
  module `Circuit.Mon`.
- `Trace` is the free traced category over `arr`.  The trace is explicit as
  `Knot`; sequential composition and the monoidal product are collapsed into
  the base arrow via its `Category`, `Monoidal` and `Action` instances.  Only
  `Arr` and `Knot` remain as constructors.
- `TraceMon` is the free traced monoidal category over `arr`.  Both the trace
  (`Knot`) and the monoidal product (`Par`/`Swap`) are explicit syntax.  It
  does not exist as a module; it is the conceptual middle ground between
  `Mon` and `Trace`.
- `Net` is the free traced PROP with bimonoid over `arr`.

`+` is commutative and associative on raw constructors.  In the current
implementation this is a design metaphor realised by explicit injections and
projections between separate GADTs: `Free ↪ Mon ↪ Net` via `freeToMon` and
`widen`, with `sift`, `enrich`, and `melt` as the forgetful maps down to
`Mon`, `Net`, and `Trace` respectively.  There is no constructor sharing
between layers because composing free constructions literally requires a
distributive law; the duplicated `bind` clauses in `Net` are the small price
of keeping the direct GADTs canonical.

## Conversions

Each inclusion of a smaller layer into a larger one has a corresponding
forgetful / evaluative map.

| map | type | what it does |
|---|---|---|
| `freeToMon` | `Free :~~> Mon` | include the sequential layer in the monoidal layer |
| `widen` | `Mon :~~> Net t` | include the monoidal layer in the traced PROP |
| `enrich` | `Trace t :~~> Net t` | include normal form in full syntax |
| `sift` | `Net t :~~> Mon` | forget `Knot` and bimonoid rows, keep `Par`/`Swap` |
| `melt` | `Net t :~~> Trace t` | evaluate all structural rows to `Arr` |
| `run` | `Layer f => forall arr. Law f arr => f arr :~> arr` | universal fold into the same base arrow |

`TraceMon` is realised only in `Circuit.Layer.Algebra` as `AlgMonKnot`, with
`monKnotToTrace` / `traceToMonKnot` as the conversion functions.  In the
direct GADT tower `TraceMon` remains conceptual: `melt` is a direct fold over
`Net` constructors, and `sift` captures the intermediate step of forgetting
`Knot` and the bimonoid rows while keeping `Par`/`Swap` inspectable.

## Semantics

The `Layer` class captures the free-forgetful adjunction for a single layer.
The hom-set isomorphism is:

```haskell
unit  :: Category arr => arr :~> f arr
bind  :: Law f arr' => (arr :~> arr') -> (f arr :~> arr')
run   :: Law f arr => f arr :~> arr
lower :: (Layer f, Category arr) => (f arr :~> arr') -> (arr :~> arr')
```

`unit` includes the generators; `bind` folds the free syntax into any
`Law`-abiding target; `run = bind id` is the counit; `lower g = g . unit`
restricts a fold to the generators.  `bind` and `lower` are the two
directions of the hom-set isomorphism, not adjoint functors themselves.

`Layer` is a *relative* (or constrained) monad: `join = bind id` only works
when `Law f (f arr)` holds, and `unit` needs `Category arr`.

Inter-layer maps such as `enrich`/`melt` are not provided by `Layer` itself;
they are higher natural transformations `f :~~> g` between two layers.

## Conditional fold for `Net`

`Net` is the free traced PROP with a bimonoid over `arr`.  The constructors
`Copy`, `Discard`, `Plus`, and `Zero` carry `Dg.Bimonoid arr a` dictionaries
from the *source* arrow.  When `bind h` processes a bimonoid row it applies
`h` to the source's `Dg.copy` / `Dg.discard` / `Dg.plus` / `Dg.zero` — so it
interprets the bimonoid generators as the *image under `h`* of the source
structure, not as the target's own bimonoid.

This is the universal free-PROP fold exactly when `h` is a bimonoid
homomorphism.  That is automatic for `unit` and for `hmap`, but must be
checked for an arbitrary embedding `h`.  In particular, transposition in a
`Net` over `Dg.Dagger` swaps the forward copy / backward plus pairing in the
base arrow, which is why `transpose` is only defined for `Dg.Dagger` bases.

## Signature-based view

`Circuit.Layer.Algebra` gives the same lattice in a different language: each
feature (`Compose`, `Knot`, `Par`, `Swap`, `Bimonoid`) is a signature
functor, and a circuit language is the free `Syntax` over a coproduct of
signatures.  The direct GADTs in `Circuit.Trace` and `Circuit.Net` are the
canonical implementation; the algebra module is a design tool for prototyping
new features and making the adjunction lattice explicit.

`algMelt` and `algFreeze` are the signature-based versions of `melt` and the
forgetful map from `Trace` to `Free`.  `AlgMonKnot t arr` is the
signature-based realisation of the conceptual `TraceMon` layer, with
`monKnotToTrace` / `traceToMonKnot` as the change-of-base maps.
