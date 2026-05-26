# Circuit — the initial encoding

`Circuit` is the initial encoding: a GADT with three constructors.
Where `Hyper` dissolves feedback into the type, `Circuit` makes it
explicit.  You can inspect the structure, pattern-match constructors,
and build combinators that Hyper cannot.

```haskell
-- $setup
-- >>> import Control.Arrow (Kleisli(..), runKleisli)
-- >>> import Circuit.Circuit (Circuit(..), reify)
-- >>> import Circuit.Traced (Trace(..))
-- >>> import Circuit.Hyper (encode, lower)
-- >>> import Prelude hiding (id, (.))
```

---

## the three constructors

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  Knot    :: arr (t a b) (t a c) -> Circuit arr t b c
```

| constructor | what it encodes | axiom |
|------------|----------------|-------|
| `Lift f` | embed a base arrow | 2, 3 — identity, functoriality |
| `Compose f g` | sequential composition | 1 — associativity |
| `Knot f` | feedback loop via tensor `t` | 6 — sliding/feedback |

Three constructors, no more.  `Push` would be `Compose (Lift f)` — already
expressible.  `Curry` would give a closed category, strictly more than
traced.  The GADT is minimal.

```haskell
-- >>> reify (Lift (+ 1) :: Circuit (->) (,) Int Int) 5
-- 6

-- >>> reify (Compose (Lift (+ 1)) (Lift (* 2)) :: Circuit (->) (,) Int Int) 5
-- 11

-- >>> let step n = if n < 3 then Left (n + 1) else Right n
-- >>> reify (Knot (either step step) :: Circuit (->) Either Int Int) 0
-- 3
```

---

## reify and the Mendler case

`reify` interprets a Circuit to a plain arrow.  The definition is
structural recursion with one critical pattern match:

```haskell
reify (Lift f)             = f
reify (Compose (Knot f) g) = trace (f . untrace (reify g))   -- Mendler
reify (Compose f g)        = reify f . reify g
reify (Knot k)             = trace k
```

The Mendler case (`Compose (Knot f) g`) must appear before the general
`Compose` case.  Without it, the pattern falls through to:

```haskell
reify (Compose (Knot f) g) = trace f . reify g    -- WRONG
```

In the wrong version, `reify g` is applied once at the loop's exit.
In the Mendler version, `reify g` is threaded into the feedback channel
via `untrace` on every iteration.  For `(,)` the two give the same
result on single-step loops but diverge on multi-step.  For `Either`
they differ even on the first iteration.

Without the Mendler case, `Knot` collapses to `Lift (trace k)` — the
feedback structure is lost and Circuit degenerates to a free category
with a fixed-point operator.  This is the degenerate model that the
2013 paper warns about.

```haskell
-- | A composed loop exercises the Mendler case.
-- >>> let step n = if n < 3 then Left (n + 1) else Right n
-- >>> let counter = Knot (either step step) :: Circuit (->) Either Int Int
-- >>> reify (Compose (Lift (* 2)) counter) 0
-- 6
```

The doubling (`* 2`) runs on the exit value.  With the Mendler case,
`Lift (* 2)` is threaded through `untrace` and participates in each
iteration — though here it only affects the final `Right` branch.

---

## Kleisli Circuit — effects

Circuit is parametric in the base arrow `arr`.  Setting `arr = Kleisli IO`
gives an effectful circuit.  Paired with `t = Either`, you get IO loops
with constant stack space (delimited continuations in the `Trace`
instance).

```haskell
-- | Effectful loop: append "!" until length >= 3.
-- >>> let exclaim = Knot (Kleisli (\case Right s | length s < 3 -> pure (Left (s <> "!")); Right s -> pure (Right ()); Left s -> pure (Right ()))) :: Circuit (Kleisli IO) Either String ()
-- >>> runKleisli (reify exclaim) "a"
-- ()
```

```haskell
-- | Compose two Kleisli loops.  Second runs after first exits.
-- >>> let echo = Knot (Kleisli (\case Right s -> pure (Right (s <> "!")); Left s -> pure (Right s))) :: Circuit (Kleisli IO) Either String String
-- >>> let doubler = Knot (Kleisli (\case Right s -> pure (Right (s <> s)); Left s -> pure (Right s))) :: Circuit (Kleisli IO) Either String String
-- >>> runKleisli (reify (Compose doubler echo)) "hi"
-- "hi!hi!"
```

The Mendler case handles composition correctly here too — the second
loop's effect threads through each iteration of the first.

---

## encode — bridge to Hyper

`encode` maps Circuit into Hyper, preserving observable behaviour:

```haskell
encode :: Circuit (->) (,) a b -> Hyper a b
encode (Lift f)      = lift f
encode (Compose f g) = encode f . encode g
encode (Knot f)      = trace (lift f)
```

The `Knot` case uses Hyper's own `Trace (,)` instance — a coinductive
lazy knot.  The triangle `lower . encode = reify` holds.

```haskell
-- >>> lower (encode (Lift (+ 1) :: Circuit (->) (,) Int Int)) 5
-- 6

-- >>> let k = Knot (\(xs, ()) -> (0 : xs, take 3 xs)) :: Circuit (->) (,) () [Int]
-- >>> lower (encode k) ()
-- [0,0,0]
```

`encode` does not need a Mendler case — Hyper's `Category` composition
threads the continuation structurally, so `Compose (Knot f) g` reduces
through the general `Compose` case without special treatment.

---

## Circuit ↔ Hyper

| capability | Circuit | Hyper |
|-----------|---------|-------|
| inspect structure | yes — GADT constructors | no — opaque |
| Kleisli / effects | yes — parametric in `arr` | no — `invoke` returns `b` |
| sliding | Mendler case enforces | inherent in `(.)` |
| degenerate model | possible (without Mendler) | impossible |
| composition cost | O(n²) left-nested | O(1) amortised |

Build in Circuit for expressive power.  Encode to Hyper for structural
guarantees.
