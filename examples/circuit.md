---
name: circuit
description: The Trace GADT as the initial encoding
tags: ['trace', 'gadt', 'run']
---
# Circuit — the initial encoding

`Trace` is the initial encoding: a GADT with two constructors.
Where `Hyper` dissolves feedback into the type, `Trace` makes it
explicit.  You can inspect the structure, pattern-match constructors,
and build combinators that Hyper cannot.

```haskell
-- $setup
-- >>> :set -XLambdaCase
-- >>> import Control.Arrow (Kleisli(..), runKleisli)
-- >>> import Control.Category ((>>>))
-- >>> import Circuit (Trace, run, encode)
-- >>> import Circuit.Hyper (observe)
-- >>> import qualified Circuit.Trace as T
```

In `cabal repl`, qualify constructors as `T.Arr` / `T.Knot` — interpreted
mode also loads `Circuit.Mon`, which exports its own `Arr`.

---

## the two constructors

```haskell
-- Trace GADT (Circuit.Trace):
--   Arr  :: arr a b -> Trace t arr a b
--   Knot :: arr (t s a) (t s b) -> Trace t arr a b
```

| constructor | what it encodes | axiom |
|------------|----------------|-------|
| `Arr f` | embed a base arrow | 2, 3 — identity, functoriality |
| `Knot f` | feedback loop via tensor `t` | 6 — sliding/feedback |

Two constructors, no more.  Sequential composition is `(.)` or `(>>>)`
via the `Category` instance.  There is no `Compose` constructor and no
`Lift` on `Trace` — those live on `Free` / `Net`.  The GADT is already
in normal form: at most one `Knot`, at the top, over a base-arrow body.

```haskell
-- >>> run (T.Arr (+ 1) :: Trace (,) (->) Int Int) 5
-- 6

-- >>> run (T.Arr (+ 1) >>> T.Arr (* 2) :: Trace (,) (->) Int Int) 5
-- 12

-- >>> let step n = if n < 3 then Left (n + 1) else Right n
-- >>> run (T.Knot (either step step) :: Trace Either (->) Int Int) 0
-- 3
```

---

## run

`run` interprets a `Trace` to a plain arrow.  Structural recursion over
the normal-form GADT:

```haskell
-- run :: T.Traced t arr => Trace t arr a b -> arr a b
-- run (T.Arr f)  = f
-- run (T.Knot k) = T.trace k
```

Sequential composition is handled by the `Category` instance, not by an
explicit constructor.  The instance enforces the sliding law: when an
`Arr` is composed with a `Knot`, the base arrow is pushed inside the
knot's feedback channel rather than applied only at the loop exit.

If composition were naive, `T.Arr f >>> T.Knot k` would collapse to
`f . trace k` at the exit only, and feedback structure would be lost.
That is the degenerate model the 2013 paper warns about.  Pre-0.2 this
was a Mendler case in the interpreter (`Compose (Knot f) g`); post-0.2
it lives entirely in `Category` — see `examples/symbols.md`.

```haskell
-- | A composed loop exercises the sliding law.
-- >>> let step n = if n < 3 then Left (n + 1) else Right n
-- >>> let counter = T.Knot (either step step) :: Trace Either (->) Int Int
-- >>> run (counter >>> T.Arr (* 2)) 0
-- 6
```

The doubling sits inside the feedback body before `run` closes the
channel (`Category` builds `T.Knot (untrace (* 2) . either step step)`).

---

## Kleisli Trace — effects

`Trace` is parametric in the base arrow `arr`.  Setting `arr = Kleisli IO`
gives an effectful circuit.  Paired with `t = Either`, you get IO loops
with constant stack space (delimited continuations in the `Traced`
instance).

```haskell
-- | Effectful loop: append "!" until length >= 3.
-- >>> let exclaim = T.Knot (Kleisli (\case Right s | length s < 3 -> pure (Left (s <> "!")); Right _ -> pure (Right ()); Left _ -> pure (Right ()))) :: Trace Either (Kleisli IO) String ()
-- >>> runKleisli (run exclaim) "a"
-- ()
```

```haskell
-- | Sequence two Kleisli loops.  Second runs after first exits.
-- >>> let echo = T.Knot (Kleisli (\case Right s -> pure (Right (s <> "!")); Left s -> pure (Right s))) :: Trace Either (Kleisli IO) String String
-- >>> let doubler = T.Knot (Kleisli (\case Right s -> pure (Right (s <> s)); Left s -> pure (Right s))) :: Trace Either (Kleisli IO) String String
-- >>> runKleisli (run (echo >>> doubler)) "hi"
-- "hi!hi!"
```

Sliding handles composition here too — the second loop's effect threads
through each iteration of the first.

---

## encode — bridge to Hyper

`encode` maps `Trace` into Hyper, preserving observable behaviour:

```haskell
-- encode :: Trace (,) (->) a b -> Hyper a b
-- encode (T.Arr f)  = lift f
-- encode (T.Knot f) = T.trace (lift f)
```

The `Knot` case uses Hyper's own `Traced` instance — a coinductive
lazy knot.  The triangle `observe . encode = run` holds.

```haskell
-- >>> observe (encode (T.Arr (+ 1) :: Trace (,) (->) Int Int)) 5
-- 6

-- >>> let k = T.Knot (\(xs, ()) -> (0 : xs, take 3 xs)) :: Trace (,) (->) () [Int]
-- >>> observe (encode k) ()
-- [0,0,0]
```

`encode` needs no special composition case — Hyper's `Category`
threads the continuation structurally, and `Trace` composition already
applies sliding.

---

## Trace ↔ Hyper

| capability | Trace | Hyper |
|-----------|-------|-------|
| inspect structure | yes — GADT constructors | no — opaque |
| Kleisli / effects | yes — parametric in `arr` | no — `invoke` returns `b` |
| sliding | `Category` instance enforces | inherent in `(.)` |
| degenerate model | possible (without sliding) | impossible |
| composition cost | O(n²) left-nested | O(1) amortised |

Build in Trace for expressive power.  Encode to Hyper for structural
guarantees.
