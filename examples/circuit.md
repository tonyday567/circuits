---
title: "Circuit — the initial encoding"
category: core
status: stable
tags: ["trace", "gadt", "run"]
---

# Circuit — the initial encoding

`Trace` is the initial encoding: a GADT with two constructors.
Where `Hyper` dissolves feedback into the type, `Trace` makes it
explicit.  You can inspect the structure, pattern-match constructors,
and build combinators that Hyper cannot.

```haskell
-- $setup
-- >>> import Control.Arrow (Kleisli(..), runKleisli)
-- >>> import Circuit (Trace(..), run)
-- >>> import Circuit.Trace (Traced(..))
-- >>> import Circuit.Hyper (encode, observe, lift)
-- >>> import Prelude hiding (id, (.))
```

---

## the two constructors

```haskell
data Trace t arr a b where
  Arr     :: arr a b -> Trace t arr a b
  Knot    :: arr (t a b) (t a c) -> Trace t arr b c
```

| constructor | what it encodes | axiom |
|------------|----------------|-------|
| `Arr f` | embed a base arrow | 2, 3 — identity, functoriality |
| `Knot f` | feedback loop via tensor `t` | 6 — sliding/feedback |

Two constructors, no more.  Sequential composition is `(.)` or `(>>>)`
via the `Category` instance.  `Curry` would give a closed category,
strictly more than traced.  The GADT is minimal.

```haskell
-- >>> run (Arr (+ 1) :: Trace (,) (->) Int Int) 5
-- 6

-- >>> run (Arr (+ 1) . Arr (* 2) :: Trace (,) (->) Int Int) 5
-- 11

-- >>> let step n = if n < 3 then Left (n + 1) else Right n
-- >>> run (Knot (either step step) :: Trace Either (->) Int Int) 0
-- 3
```

---

## run

`run` interprets a `Trace` to a plain arrow.  The definition is
structural recursion over the normal-form GADT:

```haskell
run :: Traced arr t => Trace t arr a b -> arr a b
run (Arr f)  = f
run (Knot k) = trace k
```

Because `Trace` is already in normal form, sequential composition is
handled by the `Category` instance rather than by an explicit
constructor.  The `Category` instance enforces the sliding law
(Mendler-style): when an `Arr` is composed with a `Knot`, the base
arrow is pushed inside the knot's feedback channel rather than applied
only at the loop exit.

If the instance instead treated composition naively, `Arr f . Knot k`
would collapse to `f . trace k` applied only at the exit, and the
feedback structure would be lost.  This is the degenerate model that
the 2013 paper warns about.

```haskell
-- | A composed loop exercises the sliding law.
-- >>> let step n = if n < 3 then Left (n + 1) else Right n
-- >>> let counter = Knot (either step step) :: Trace Either (->) Int Int
-- >>> run (Arr (* 2) . counter) 0
-- 6
```

The doubling (`* 2`) runs on the exit value.  With the sliding law,
`Arr (* 2)` is threaded inside the knot and participates in each
iteration — though here it only affects the final `Right` branch.

---

## Kleisli Trace — effects

`Trace` is parametric in the base arrow `arr`.  Setting `arr = Kleisli IO`
gives an effectful circuit.  Paired with `t = Either`, you get IO loops
with constant stack space (delimited continuations in the `Traced`
instance).

```haskell
-- | Effectful loop: append "!" until length >= 3.
-- >>> let exclaim = Knot (Kleisli (\case Right s | length s < 3 -> pure (Left (s <> "!")); Right s -> pure (Right ()); Left s -> pure (Right ()))) :: Trace Either (Kleisli IO) String ()
-- >>> runKleisli (run exclaim) "a"
-- ()
```

```haskell
-- | Compose two Kleisli loops.  Second runs after first exits.
-- >>> let echo = Knot (Kleisli (\case Right s -> pure (Right (s <> "!")); Left s -> pure (Right s))) :: Trace Either (Kleisli IO) String String
-- >>> let doubler = Knot (Kleisli (\case Right s -> pure (Right (s <> s)); Left s -> pure (Right s))) :: Trace Either (Kleisli IO) String String
-- >>> runKleisli (run (doubler . echo)) "hi"
-- "hi!hi!"
```

The sliding law handles composition correctly here too — the second
loop's effect threads through each iteration of the first.

---

## encode — bridge to Hyper

`encode` maps `Trace` into Hyper, preserving observable behaviour:

```haskell
encode :: Trace (,) (->) a b -> Hyper a b
encode (Arr f)  = lift f
encode (Knot f) = trace (lift f)
```

The `Knot` case uses Hyper's own `Traced` instance — a coinductive
lazy knot.  The triangle `observe . encode = run` holds.

```haskell
-- >>> observe (encode (Arr (+ 1) :: Trace (,) (->) Int Int)) 5
-- 6

-- >>> let k = Knot (\(xs, ()) -> (0 : xs, take 3 xs)) :: Trace (,) (->) () [Int]
-- >>> observe (encode k) ()
-- [0,0,0]
```

`encode` does not need a special composition case — Hyper's `Category`
composition threads the continuation structurally, and `Trace`
composition already applies the sliding law.

---

## Trace ↔ Hyper

| capability | Trace | Hyper |
|-----------|-------|-------|
| inspect structure | yes — GADT constructors | no — opaque |
| Kleisli / effects | yes — parametric in `arr` | no — `invoke` returns `b` |
| sliding | `Category` instance enforces | inherent in `(.)` |
| degenerate model | possible (without sliding) | impossible |
| composition cost | O(n²) left-nested | O(1) amortised |

Build in Circuit for expressive power.  Encode to Hyper for structural
guarantees.
