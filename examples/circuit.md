# Circuit — the initial encoding

`Circuit` is the initial encoding of a traced monoidal category — a GADT
with three constructors. Where `Hyper` dissolves feedback into the type,
`Circuit` makes it explicit. You can inspect the structure, pattern-match
constructors, and build combinators that Hyper cannot.

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

Three constructors, no more. `Push` would be `Compose (Lift f)` — already
expressible. `Curry` would give a closed category, strictly more than
traced. The GADT is minimal.

```haskell
-- | Lift: a single-step function.
-- >>> reify (Lift (+ 1) :: Circuit (->) (,) Int Int) 5
-- 6

-- | Compose: chain two circuits.
-- >>> reify (Compose (Lift (+ 1)) (Lift (* 2)) :: Circuit (->) (,) Int Int) 5
-- 11

-- | Knot: a feedback loop. Left = continue, Right = exit.
-- >>> let step (Right n) | n < 3 = Left (n + 1); step (Right n) = Right n; step (Left n) | n < 3 = Left (n + 1); step (Left n) = Right n
-- >>> reify (Knot step :: Circuit (->) Either Int Int) 0
-- 3
```

---

## reify and the Mendler case

`reify` interprets a Circuit to a plain arrow. The definition is
structural recursion with one critical pattern match:

```haskell
reify (Lift f)             = f
reify (Compose (Knot f) g) = trace (f . untrace (reify g))   -- Mendler
reify (Compose f g)        = reify f . reify g
reify (Knot k)             = trace k
```

The Mendler case (`Compose (Knot f) g`) must appear before the general
`Compose` case. Without it, the pattern falls through to:

```haskell
reify (Compose (Knot f) g) = trace f . reify g    -- WRONG
```

The difference: in the wrong version, `reify g` is applied once at the
loop's exit. In the Mendler version, `reify g` is threaded into the
feedback channel via `untrace` on every iteration. For `(,)`, the two
give the same result when the loop runs once but diverge on multi-step
loops. For `Either`, they differ even on the first iteration.

Without the Mendler case, `Knot` collapses to `Lift (trace k)` — the
feedback structure is lost and Circuit degenerates to a free category
with a fixed-point operator. This is the degenerate model that the
2013 paper warns about.

```haskell
-- | A composed loop exercises the Mendler case.
-- Knot iterates a counter; doubling runs after the loop exits.
-- >>> let step (Right n) | n < 3 = Left (n + 1); step (Right n) = Right n; step (Left n) | n < 3 = Left (n + 1); step (Left n) = Right n
-- >>> let counter = Knot step :: Circuit (->) Either Int Int
-- >>> reify (Compose (Lift (* 2)) counter) 0
-- 6
```

The doubling (`* 2`) runs on the exit value. With the Mendler case,
`Lift (* 2)` is threaded through `untrace` and participates in each
iteration — though here it only affects the final `Right` branch.
For a case where the post-loop function changes iteration behaviour,
see `examples/two-loops.md`.

---

## product combinators

Circuit's GADT is inspectable — you can pattern-match constructors to
build combinators that Hyper cannot express directly. The `(,)` tensor
carries a product through the feedback channel.

### first — thread a pair

```haskell
{-# LANGUAGE ScopedTypeVariables #-}
-- | Thread a passive value through, touching only the active component.
-- >>> let firstC :: forall b c d. Circuit (->) (,) b c -> Circuit (->) (,) (b, d) (c, d)
-- >>>     firstC (Lift f)    = Lift (\(b, d) -> (f b, d))
-- >>>     firstC (Compose f g) = Compose (firstC f) (firstC g)
-- >>>     firstC (Knot f)    = Knot (\(a, (b, d)) -> let (a', c) = f (a, b) in (a', (c, d)))
-- >>> reify (firstC (Lift (+ 1)) :: Circuit (->) (,) (Int, String) (Int, String)) (5, "hi")
-- (6,"hi")
```

Only `firstC` composes through `Compose` — the `d` appears in both input
and output, so intermediate types match. Reader and state are built
outside the recursive structure by pattern-matching the input pair.

### fanout — share input

```haskell
-- | Route one input to two circuits, pair the outputs.
-- Nail the tensor by binding a monomorphic reify helper.
-- >>> let reify' = reify :: Circuit (->) (,) Int a -> Int -> a
-- >>> let fanout f g = Lift (\a -> (reify' f a, reify' g a))
-- >>> reify' (fanout (Lift (+ 1)) (Lift (* 2))) 5
-- (6,10)
```

### reader and state

```haskell
-- | Reader: thread environment, drop it at exit.
-- >>> reify (Lift (\(_, a) -> a + 1) :: Circuit (->) (,) (String, Int) Int) ("hi", 5)
-- 6

-- | State: thread state through.
-- >>> reify (Lift (\(s, a) -> (s, a + 1)) :: Circuit (->) (,) (String, Int) (String, Int)) ("hi", 5)
-- ("hi",6)
```

### reader + state combined

Reader and state compose naturally inside the feedback channel. Here the
`Either` tensor's `Left` branch carries a pair `(threshold, accumulator)`
— threshold is read-only (reader), accumulator is threaded (state):

```haskell
-- | Each call adds 1 to the accumulator, exits when over threshold.
-- >>> let step (Right val) = if val > 10 then Right (10, val) else Left (10, val)
-- >>>     step (Left (thresh, total)) = let t = total + 1 in if t > thresh then Right (thresh, t) else Left (thresh, t)
-- >>> let acc = Knot step :: Circuit (->) Either Int (Int, Int)
-- >>> reify acc 12
-- (10,12)
-- >>> reify acc 3
-- (10,11)
```

The `Either` tensor gives loop control (continue/exit). The `(Int, Int)`
inside `Left` carries both reader (threshold, never modified) and state
(accumulator, incremented each step). No separate reader/state wrappers
needed — the product inside the feedback channel handles both.

---

## Kleisli Circuit — effects

Circuit is parametric in the base arrow `arr`. Setting `arr = Kleisli IO`
gives an effectful circuit. Paired with `t = Either`, you get IO loops
with constant stack space (delimited continuations in the `Trace`
instance).

```haskell
-- | An effectful loop: keep appending "!" until the string is long enough.
-- >>> let ioLoop = Knot (Kleisli (\case Right s | length s < 3 -> pure (Left (s <> "!")); Right s -> pure (Right ()); Left s -> pure (Right ()))) :: Circuit (Kleisli IO) Either String ()
-- >>> runKleisli (reify ioLoop) "a"
-- ()
```

The `Trace (Kleisli IO) Either` instance uses GHC's delimited
continuation primops (`prompt#` / `control0#`) for constant stack space
regardless of iteration count. See `examples/traced.md` for the
bracket structure.

```haskell
-- | Compose two Kleisli loops. The second runs after the first exits.
-- >>> let echo = Knot (Kleisli (\case Right s -> pure (Right (s <> "!")); Left s -> pure (Right s))) :: Circuit (Kleisli IO) Either String String
-- >>> let doubler = Knot (Kleisli (\case Right s -> pure (Right (s <> s)); Left s -> pure (Right s))) :: Circuit (Kleisli IO) Either String String
-- >>> runKleisli (reify (Compose doubler echo)) "hi"
-- Right "hi!hi!"
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
lazy knot. The triangle `lower . encode = reify` holds (see
`examples/hyper.md`).

```haskell
-- | Encode then observe gives the same result as reify.
-- >>> lower (encode (Lift (+ 1) :: Circuit (->) (,) Int Int)) 5
-- 6
-- >>> reify (Lift (+ 1) :: Circuit (->) (,) Int Int) 5
-- 6

-- | Knot preserves feedback through encode.
-- >>> let k = Knot (\\(xs, ()) -> (0 : xs, take 3 xs)) :: Circuit (->) (,) () [Int]
-- >>> lower (encode k) ()
-- [0,0,0]
-- >>> reify k ()
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
| `first` / fanout | yes — pattern-match | no — continuation barrier |
| Kleisli / effects | yes — parametric in `arr` | no — `invoke` returns `b` |
| sliding | Mendler case enforces | inherent in `(.)` |
| degenerate model | possible (without Mendler) | impossible |
| composition cost | O(n²) left-nested | O(1) amortised |

Build in Circuit for expressive power. Encode to Hyper for structural
guarantees. See `examples/hyper.md` for the full comparison.
