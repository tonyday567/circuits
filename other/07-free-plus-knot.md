# Trace as Free + Knot

An exploration.  Can `Trace` wrap `Free` rather than duplicate `Arr`?

## First cut: embed Free, add Knot

```haskell
data Trace t arr a b where
  FreeT :: Free arr a b -> Trace t arr a b
  KnotT :: Trace t arr (t a b) (t a c) -> Trace t arr b c
```

`run` becomes trivial for the `FreeT` case:

```haskell
run (FreeT f) = runFree f
run (KnotT k) = trace (run k)
```

No Mendler case.  No `Compose (Knot f) g` to handle.

But there is no `Compose (Knot f) g` at all.  `Compose` lives in `Free`,
`KnotT` lives in `Trace`, and they don't mix.  You can't write:

```haskell
openf >>> readAndCount >>> closef
```

where `readAndCount = KnotT ...` and `>>>` is `(.)` from `Category (Trace t arr)`.
A `Trace`-level `(.)` is needed for `Trace` nodes, not just `Free` nodes.

## Second cut: add ComposeT

```haskell
data Trace t arr a b where
  FreeT    :: Free arr a b -> Trace t arr a b
  ComposeT :: Trace t arr b c -> Trace t arr a b -> Trace t arr a c
  KnotT    :: Trace t arr (t a b) (t a c) -> Trace t arr b c
```

Now `ComposeT` takes `Trace` children, and `KnotT` can be a left child.
The Mendler case reappears in `run`:

```haskell
run (FreeT f)                = runFree f
run (ComposeT (KnotT f) g)   = trace (run f . untrace (run g))
run (ComposeT f g)           = run f . run g
run (KnotT k)                = trace (run k)
```

`ComposeT` duplicates `Free.Compose`.  We've traded `Arr` duplication
for `FreeT`+`ComposeT` + one wrapper per embedded node.

## Third cut: no ComposeT, use the Category instance

Drop `ComposeT`.  Make `(.)` for `Trace` handle the four node combinations:

```haskell
instance Category arr => Category (Trace t arr) where
  id = FreeT (Lift id)

  -- Free . Free  ->  compose in Free
  FreeT f . FreeT g = FreeT (Compose f g)

  -- Free . Knot  ->  f after the Knot exits
  FreeT f . KnotT k = KnotT (fmap (second f) k)   -- or Lift (rmap f) . KnotT?

  -- Knot . Free  ->  THE MENDLER CASE
  KnotT k . FreeT g = ???   -- must slide g inside the feedback channel

  -- Knot . Knot  ->  two feedback loops
  KnotT k . KnotT k' = ???
```

The `KnotT . FreeT` case is the Mendler case.  It can't be expressed as
a simple constructor — it must thread `g` inside the `KnotT` body's
feedback channel.  The only way is to push it into `run`:

```haskell
KnotT k . FreeT g = FreeT (Lift (trace (run k . untrace (run (FreeT g)))))
```

But this calls `run` inside `(.)`, which calls `(.)`, which may call `run` —
mutual recursion between `(.)` and `run`.

## The issue

The Mendler case is `Compose (Knot f) g`.  It requires *both* `Compose`
and `Knot` in the same GADT — `Compose` must be able to hold a `Knot`
as its left child, and `run` must pattern-match on both constructors
simultaneously.

Any two-layer design (`Trace` wrapping `Free`) either:
- Forbids `Compose (Knot f) g` entirely (first cut)
- Duplicates `Compose` in `Trace` (second cut)
- Pushes the Mendler case into `(.)`, creating mutual recursion (third cut)

The current design — `Arr`/`Knot` in one flat GADT with sequential
composition provided by the `Category` instance — is the simplest
expression of the structure.  The constructor duplication across
`Trace`/`Free`/`Net` is the cost of flatness.  A two-layer design would
reduce that duplication but create new complexity elsewhere.

The right question isn't "can we eliminate duplication" but "where do
we want the complexity to live?"  Three copies of the base-arrow
constructor vs a nesting discipline that forces the Mendler case into
`(.)`.
