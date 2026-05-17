# Optics and Circuits

A lens is a stateful morphism before the feedback loop is tied. A
`Circuit` is what you get after `Knot` hides the state wire. The
isomorphism is immediate: `Knot` closes the loop, `untrace` opens it,
and the trace axioms handle composition of state wires.

```haskell
-- $setup
-- >>> import Circuit.Circuit
-- >>> import Circuit.Traced
-- >>> import Control.Arrow (second)
-- >>> import Prelude hiding (id, (.))
```

---

## The isomorphism

In a cartesian category, a **stateful morphism** has the shape:

```
f :: (s, b) -> (s, c)
```

The `s` wire carries state through while `b` enters and `c` exits.
`Knot` is precisely the operation that hides this wire, turning the
stateful morphism into a feedback loop:

```haskell
Knot :: ((s, b) -> (s, c)) -> Circuit (->) (,) b c
```

Going the other way, `untrace` exposes a trivial state wire on any
morphism. For the `(,)` tensor, `untrace = second`:

```haskell
untrace :: (b -> c) -> ((s, b) -> (s, c))
```

So within the traced cartesian setting:

```
stateful morphism   ≅   Knot-able circuit fragment
```

A lens `Lens s s b c` is exactly a stateful morphism `(s, b) -> (s, c)`
— the update function carries the state wire through unchanged. `Knot`
hides the wire; `untrace` introduces it.

---

## Hiding the wire

```haskell
-- | Biased addition: new state is input + 10, output is state + input.
biased :: (Int, Int) -> (Int, Int)
biased (s, x) = (x + 10, s + x)

-- | Hide the state wire with Knot.
-- >>> reify (Knot biased) 5
-- 20
```

The `Trace` instance for `(->)` and `(,)` ties the lazy knot:

```haskell
trace biased 5 = let (s, c) = (5 + 10, s + 5) in c
               = let s = 15 in 15 + 5
               = 20
```

Laziness resolves the feedback because the new state `x + 10` does not
depend on the old state `s`.

---

## Exposing the wire

`untrace` introduces a state wire that passes through unchanged:

```haskell
-- | untrace = second for the cartesian trace.
-- >>> let f = reify (Knot biased) in second f (100, 5)
-- (100,20)
```

Given any morphism `b -> c`, `untrace` produces a stateful morphism
`(s, b) -> (s, c)` that ignores the state. This is the constant-state
lens. The full pair `(trace, untrace)` is what lets you move between
stateful and stateless representations.

---

## Composition: merging state wires

When you compose two circuits built from `Knot`, their state wires
merge compositionally. The sliding and vanishing axioms guarantee that
the combined circuit is equivalent to a single `Knot` over a product
state.

```haskell
-- | Compose two knotted circuits. The state wires merge implicitly.
-- >>> let c1 = Knot (\(s, x) -> (x + 10, s + x))
-- >>>     c2 = Knot (\(t, y) -> (y * 2, t + y))
-- >>> in reify (c2 ⊙ c1) 5
-- 60
```

By the vanishing axiom, the composite state wire is the product of the
individual states. The trace handles the tuple introduction and
elimination; you never need to thread state manually.

---

## Sum types: Either and iteration

The same pattern holds for the `Either` tensor. A stateful morphism
`Either s b -> Either s c` has `Left s` carrying state and `Right c`
exiting with output. `Knot` turns this into an iterating circuit:

```haskell
-- | Either-stateful morphism: iterate until Right exits.
-- >>> reify (Knot step) (0 :: Int)
-- 3
step :: Either Int Int -> Either Int Int
step (Right n) | n < 3     = Left (n + 1)
               | otherwise = Right n
step (Left n)  | n < 3     = Left (n + 1)
               | otherwise = Right n
```

This is the sum-type analogue of the lens pattern. Where `(,)` hides a
product state wire, `Either` hides a sum state wire. The trace
iterates on `Left` and returns on `Right`, which is precisely the
shape of optics on sum types — prisms, affine traversals, and more
generally state machines with feedback.

---

## The coend question

The standard categorical formulation of optics (Riley) is a coend:

```
Optic ⟨s, t⟩ ⟨a, b⟩ = ∫^m C(s, m ⊗ a) × D(m ⊗ b, t)
```

The residual `m` is the hidden state wire. The coend quantifies over
all possible residuals — it is a universal type saying "there exists
some `m` such that."

In a traced monoidal category, `trace` and `untrace` give primitives to
introduce and eliminate a specific state wire. `Knot` hides it;
composition of knotted circuits merges wires via vanishing and sliding.
The trace handles the wiring for any *chosen* residual — but it does
not quantify over the family of all possible residuals. That universal
quantification is what the coend adds.

In a compact closed category the coend collapses because the residual
can be constructed explicitly (it is an internal hom). The `Trace`
class is strictly weaker: it eliminates wires but does not construct
new ones. The gap between trace and coend is precisely the gap between
traced monoidal and compact closed.

What the circuits setting gives you is the *practical* side: pick a
residual, `Knot` it, compose with others, let the axioms handle the
wiring. The coend remains the *semantic* type that captures "any
possible wiring" — a different structure at a different level.
