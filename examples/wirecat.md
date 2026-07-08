# Circuits + WireCat

> **Design-only / exploratory.** This card records a past proof-of-concept
> integrating `circuits` with WireCat. The standalone `circuits-wirecat` package
> has been retired; no WireCat integration currently ships with the library.

Proof-of-concept that the `circuits` free traced monoidal category framework is compatible with WireCat's cartesian record categories.

## What it adds

- `RecordTraced` — a record-category class with feedback via `knotR` on a named field.
- `FreeTraced op` — a free GADT over operations, extending WireCat's `Free` with a `KnotR` constructor.
- A `KleisliRec` instance that ties the lazy knot with `mfix`.

## Key combinators

```haskell
class (RecordCategory cat) => RecordTraced cat where
  knotR
    :: (KnownSymbol fb, Typeable a)
    => Proxy a
    -> Label fb
    -> cat (fb .== a .// r) (fb .== a .// s)
    -> cat r s

data FreeTraced op r s where
  LiftR   :: op (Rec r) (Rec s) -> FreeTraced op r s
  ComposeR :: FreeTraced op s t -> FreeTraced op r s -> FreeTraced op r t
  -- ... project, combine, relabel ...
  KnotR
    :: (KnownSymbol fb, Typeable a)
    => Proxy a -> Label fb
    -> FreeTraced op (fb .== a .// r) (fb .== a .// s)
    -> FreeTraced op r s

foldFreeTraced
  :: (RecordTraced cat)
  => (forall x y. op (Rec x) (Rec y) -> cat x y)
  -> FreeTraced op r s
  -> cat r s
```

## Example: streaming word accumulator

```haskell
wordStageExplicit
  :: FreeTraced
       WordOp
       ("line" .== String .// "acc" .== Map String Int)
       ("acc" .== Map String Int .// "count" .== Map String Int)
wordStageExplicit =
  LiftR Accumulate
    `compose` combine (LiftR GetWords `compose` pickField #line) (pickField #acc)
```

## Building

Requires a local `wirecat` checkout and relaxed bounds on `wirecat:*`.

```cabal
packages:
  circuits-wirecat.cabal
  ../circuits/circuits.cabal
  ../../other/wirecat/wirecat/wirecat.cabal
```

## Status

Proof-of-concept. The standalone package has been downgraded to this example card.
