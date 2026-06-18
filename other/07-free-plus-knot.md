# Circuit as Free + Knot

An exploration.  Can Circuit wrap Free rather than duplicate Lift/Compose?

## First cut: embed Free, add Knot

```haskell
data Circuit arr t a b where
  FreeC :: Free arr t a b -> Circuit arr t a b
  KnotC :: Circuit arr t (t a b) (t a c) -> Circuit arr t b c
```

`freeze` becomes trivial for the FreeC case:

```haskell
freeze (FreeC f) = f
freeze (KnotC k) = Lift (trace (runFree (freeze k)))
```

No Mendler case.  No `Compose (Knot f) g` to handle.

But there is no `Compose (Knot f) g` at all.  `Compose` lives in `Free`,
`KnotC` lives in `Circuit`, and they don't mix.  You can't write:

```haskell
openf >>> readAndCount >>> closef
```

where `readAndCount = Knot ...` and `>>>` is `(.)` from `Category (Circuit arr t)`.
A `Circuit`-level `(.)` is needed for `Circuit` nodes, not just `Free` nodes.

## Second cut: add ComposeC

```haskell
data Circuit arr t a b where
  FreeC    :: Free arr t a b -> Circuit arr t a b
  ComposeC :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  KnotC    :: Circuit arr t (t a b) (t a c) -> Circuit arr t b c
```

Now `ComposeC` takes `Circuit` children, and `KnotC` can be a left child.
The Mendler case reappears in `freeze`:

```haskell
freeze (FreeC f)                = f
freeze (ComposeC (KnotC f) g)   = Lift (trace (runFree (freeze f) . untrace (runFree (freeze g))))
freeze (ComposeC f g)           = Compose (freeze f) (freeze g)
freeze (KnotC k)                = Lift (trace (runFree (freeze k)))
```

`ComposeC` duplicates `Free.Compose`.  We've traded `Lift`+`Compose` duplication
for `FreeC`+`ComposeC` + one wrapper per embedded node.

## Third cut: no ComposeC, use the Category instance

Drop `ComposeC`.  Make `(.)` for `Circuit` handle the four node combinations:

```haskell
instance Category arr => Category (Circuit arr t) where
  id = FreeC (Lift id)

  -- Free . Free  →  compose in Free
  FreeC f . FreeC g = FreeC (Compose f g)

  -- Free . Knot  →  f after the Knot exits
  FreeC f . KnotC k = KnotC (fmap (second f) k)   -- or Lift (rmap f) . KnotC?

  -- Knot . Free  →  THE MENDLER CASE
  KnotC k . FreeC g = ???   -- must slide g inside the feedback channel

  -- Knot . Knot  →  two feedback loops
  KnotC k . KnotC k' = ???
```

The `KnotC . FreeC` case is the Mendler case.  It can't be expressed as
a simple constructor — it must thread `g` inside the `KnotC` body's
feedback channel.  The only way is to push it into `freeze`:

```haskell
KnotC k . FreeC g = FreeC (Lift (trace (runFree (freeze k) . untrace (runFree (freeze (FreeC g))))))
```

But this calls `freeze` inside `(.)`, which calls `(.)`, which may call `freeze` —
mutual recursion between `(.)` and `freeze`.

## The issue

The Mendler case is `Compose (Knot f) g`.  It requires *both* `Compose`
and `Knot` in the same GADT — `Compose` must be able to hold a `Knot`
as its left child, and `freeze` must pattern-match on both constructors
simultaneously.

Any two-layer design (`Circuit` wrapping `Free`) either:
- Forbids `Compose (Knot f) g` entirely (first cut)
- Duplicates `Compose` in `Circuit` (second cut)
- Pushes the Mendler case into `(.)`, creating mutual recursion (third cut)

The current design — `Lift`/`Compose`/`Knot` in one flat GADT — is the
simplest expression of the structure.  The duplication of `Lift`/`Compose`
across `Free`/`Circuit`/`Net` is the cost of flatness.  A two-layer
design would reduce that duplication but create new complexity elsewhere.

The right question isn't "can we eliminate duplication" but "where do we
want the complexity to live?"  Three copies of `Lift`/`Compose` vs a
nesting discipline that forces the Mendler case into `(.)`.
