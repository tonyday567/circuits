# Holding Hands or Taking Turns

<div align="center">

✦ · ✧ · ✦

*we find a basic choice: hold hands and go together, or take turns passing control back and forth.*

**[⟵ Prev: Hyper Buries the Knot](03-hyper-buries-the-knot.md)** · **[Next: No Remorse, Once Removed ⟶](05-no-remorse-once-removed.md)**

</div>

---

`Trace t arr a b` is generic over the tensor `t`. The two primary
tensors `(,)` and `Either` give fundamentally different semantics for
feedback, and choosing between them is a design decision about how
processes communicate.

---

## The `Traced` Typeclass

```haskell
class Traced arr t where
  trace   :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)
```

For `arr = (->)`:

| Tensor `t` | `trace`    | `untrace`  | Character       |
|------------|------------|------------|-----------------|
| `(,)`      | lazy knot  | `fmap`     | Simultaneous    |
| `Either`   | while-loop | `fmap`     | Sequential      |

The `Knot` constructor syntax is the same in both cases. What changes is
how the feedback channel behaves when `trace` closes it — the semantics
differ via the `Traced` instance.

---

## (,) — Holding Hands

With `t = (,)`, `trace` ties a lazy knot:

```haskell
trace f b = let (a, c) = f (a, b) in c
```

The feedback value `a` and the output `c` are produced simultaneously.
Both sides progress lock-step. Haskell's lazy evaluation unrolls it
productively.

**Operational character:**
- Feedback and output exist in parallel
- Suitable for: dataflow, stream processing, coinductive structures

**When it fails:** When the computation requires strict evaluation and
the feedback forms a cycle that cannot be unrolled productively.

Hyper's `encode` is `(,)`-only — it embeds into `Traced Hyper (,)`.

---

## Either — Taking Turns

With `t = Either`, `trace` runs a while-loop:

```haskell
trace f b = case f (Right b) of
  Left a  -> trace f a    -- iterate
  Right c -> c            -- done
```

Feedback and output take turns. Only one participant acts per step.

**Operational character:**
- Sequential handoff
- Suitable for: coroutines, state machines, parsers

Hyper encodes Either loops via `encodeEither` — a hand-rolled state
machine inside the continuation structure, closed with `run`.

---

## The Kidney–Wu Insight

A simultaneous `(,)` process can be split into two sequential `Either`
processes that communicate via message passing. The hyperfunction type
unifies both perspectives through the duality of the continuation
channel.

---

## Summary

| | `(,)` | `Either` |
|--|-------|---------|
| Character | Simultaneous / holding hands | Sequential / taking turns |
| `trace` | Lazy knot | While-loop |
| `untrace` | `fmap` | `fmap` |
| Hyper encoding | `encode` via `Traced Hyper (,)` | `encodeEither` via hand-rolled loop |

**Next:** [05-no-remorse-once-removed.md](05-no-remorse-once-removed.md) — Reflection Without Remorse; the
Mendler case as `viewl`; the GADT hierarchy.

---

## References

- [Kidney & Wu (2026)](https://doi.org/10.1145/3776649) — producer/consumer insight
- [Hasegawa (1997)](https://doi.org/10.1007/978-1-4471-0865-8_7) — cartesian vs computational traces
- [axioms.md](axioms.md) — proofs for both `(,)` and `Either` instances
