# No Remorse, Once Removed

<div align="center">

✦ · ✧ · ✦

*In which we attempt a remorse-free sliding; disarm a left-nesting performance trap, and the hierarchy of free structures gains a new row.*

**[⟵ Prev: Holding Hands or Taking Turns](04-holding-hands-or-taking-turns.md)** · **[Next: Some More Knots ⟶](06-some-more-knots.md)**

</div>

---

Van der Ploeg & Kiselyov (2014) solve the left-nested composition problem
for monads. The same problem appears in traced categories, and the same
solution applies — with the pattern match in `reify` playing the role of
`viewl`.

---

## The Problem: Left-Nested Composition

In any free structure built from sequential composition, left-nesting is
a performance trap:

```
((a . b) . c) . d . e . ...
```

Each `(.)` must traverse the left spine to find the base case. For a
list this is O(n²). For a free monad it is the same. For `Circuit` it
is the same — and worse: `Knot` gets buried under the left-nesting and
collapses to the degenerate model without the pattern match.

RwR establishes a hierarchy:

| Structure | Naive | Efficient | Inspection |
|-----------|-------|-----------|------------|
| Monoid | list | difference list | head/tail |
| Monad | free monad | codensity monad | `viewl` |
| Category | `Cat` | `Queue` (Ran) | `viewl` on type-aligned queue |
| **Traced category** | **`Circuit`** | **`Hyper`** | **pattern match in `reify`** |

The paper stops at categories. Traced categories is the natural next row.

---

## `viewl` is the Pattern Match

The paper's solution requires `viewl` — inspecting the head of the
sequence before recursing. Without `viewl`, the interpreter falls
through to a general case that buries the structure.

In `reify`:

```haskell
reify (Compose (Knot f) g) = ↪ (f . ↩ (reify g))
```

When a `Knot` appears at the head of a composition, inspect it before
recursing into `g`. Without this case, `reify` falls through to the
general `Compose` rule, closes the channel immediately, and produces
the degenerate model.

```
Cat     +  viewl     =  Queue      -- RwR for categories
Circuit +  viewl     =  Hyper      -- RwR for traced categories
```

---

## `PMonad` and `Trace`

The paper introduces `PMonad` — an alternative to `Monad` where bind
takes an explicit type-aligned sequence:

```haskell
class PMonad m where
  return' :: a -> m a
  (>>^=)  :: m a -> MCExp m a b -> m b
```

This is structurally the same move as `Trace`: instead of hiding the
channel inside the monad, make it an explicit typed argument:

```haskell
class Trace arr t where
  trace   :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)
```

| RwR | Circuits |
|-----|----------|
| `PMonad` | `Trace` typeclass |
| Type-aligned queue | Explicit tensor `t` in `Knot` |
| `viewl` | Pattern match in `reify` |
| `tsingleton` | `untrace` |
| `val` | `trace` |

---

## Performance: Circuit vs Hyper

The RwR analogy explains the performance story:

**`Circuit` (naive):** Left-nested `Compose` produces O(n²) traversal.
Worse: if `Knot` gets buried under left-nesting without the pattern
match, the traced structure collapses.

**`Circuit` (with pattern match):** The pattern match prevents collapse,
but left-nested `Compose` still requires O(n) traversal to find each
`Knot`.

**`Hyper`:** Composition threads the continuation on every step — O(1)
amortised. The feedback channel is always at the head. No left-spine to
traverse.

The transition from `Circuit` to `Hyper` via `encode` is the traced
equivalent of the transition from free monad to codensity monad — it
amortises traversal by making the structure maximally right-associated.

---

## Summary

The pattern match in `reify` is not a hack. It is the application of a
well-understood principle — reflection without remorse — to traced
categories. The hierarchy gains a row. The pattern match is `viewl` for
feedback channels.

**Next:** [06-some-more-knots.md](06-some-more-knots.md) — making
stuff: parsers, pipes, loops, agents, metering.

---

## References

- [Van der Ploeg & Kiselyov (2014)](https://doi.org/10.1145/2633357.2633360) — Reflection Without Remorse
- [03-hyper-buries-the-knot.md](03-hyper-buries-the-knot.md) — Ran characterization and the hierarchy
