# No Remorse, Once Removed

<div align="center">

✦ · ✧ · ✦

*In which the Mendler case is identified as `viewl`; the GADT hierarchy gains a row; and the Reflection Without Remorse analogy is refined.*

**[⟵ Prev: Holding Hands or Taking Turns](04-holding-hands-or-taking-turns.md)** · **[Next: Some More Knots ⟶](06-some-more-knots.md)**

</div>

---

Van der Ploeg & Kiselyov (2014) solve the left-nested composition problem
for monads with type-aligned sequences. The same pattern appears in
traced categories — and the Mendler case is the traced equivalent of
`viewl`.

---

## The Problem: Left-Nested Composition

In any free structure built from sequential composition, left-nesting is
a performance trap:

```
((a . b) . c) . d . e . ...
```

Each `(.)` traverses the left spine. For a list this is O(n²). For a
free monad it is the same. For `Circuit` with `Compose`, `runFree` on
a left-nested chain pays the same tax.

RwR establishes a hierarchy:

| Structure | Naive | Efficient | Inspection |
|-----------|-------|-----------|------------|
| Monoid | list | difference list | head/tail |
| Monad | free monad | codensity monad | `viewl` |
| Category | `Free`/`ListTr` | `Queue` | `viewl` on type-aligned queue |
| **Traced category** | **`Circuit`** | **`freeze` + `runFree`** | **Mendler case in `freeze`** |

---

## `viewl` is the Pattern Match

In RwR, `viewl` inspects the head of a type-aligned sequence before
recursing. Without it, the interpreter falls through to a general case
that buries the structure.

In `freeze`:

```haskell
freeze (Compose (Knot f) g) = Lift (trace (runFree (freeze f) . untrace (runFree (freeze g))))
```

When a `Knot` appears at the head of a composition, inspect it before
recursing into `g`. Without this case, the general `Compose` rule would
close the channel immediately — the degenerate model.

The mapping:

| RwR | circuits |
|-----|----------|
| `PMonad` | `Trace` typeclass |
| Type-aligned queue | Explicit tensor `t` in `Knot` |
| `viewl` | Mendler case in `freeze` |
| `tsingleton` | `untrace` |
| `val` | `trace` |

---

## The GADT Hierarchy, Corrected

The original narrative said "Circuit + viewl = Hyper." With `Free`, the
analogy refines:

```
Free     + viewl  =  Queue       (type-aligned queue, O(1) elimination)
Free     + encodeFree  =  Hyper  (final encoding, O(1) composition)
Circuit  + freeze  =  Free       (eliminate Knot via base-arrow trace)
Circuit  + freeze + viewl  =  Queue  (full elimination chain)
```

`freeze` is the `viewl` for `Circuit` — the one pattern match that
keeps `Knot` from collapsing. `Queue` is the `viewl` for `Free` — the
type-aligned queue that makes elimination O(n) with no closure overhead.

Hyper is not the efficient elimination path. It is the coinductive
dual — fast to compose, slow to eliminate. Use it for Kidney-Wu
patterns (build in Hyper, run once), not for interpreting GADT trees.

---

## Performance, Measured

Benchmarks comparing elimination paths for 10,000 to 250,000 composed
`(+1)` segments (right-nested, criterion, -O2):

| Depth (ops) | Queue | Free (runFree) | Hyper (lower . encodeFree) |
|-------------|-------|----------------|---------------------------|
| 10,000 | 230 µs | 378 µs | 282 µs |
| 62,500 | 1,615 µs | 3,550 µs | 4,622 µs |
| 250,000 | 8,004 µs | 21,300 µs | 31,020 µs |

Queue is O(n) throughout. Free degrades to ~3x Queue at scale.
Hyper degrades to ~4x — the per-step closure allocation in `(.)` and
`invoke` dispatch becomes visible.

`circuits-meter`'s `ticksN` reproduces these numbers within 10%,
confirming it is calibrated against criterion as an oracle.

The RwR concern — O(n²) from left-nesting — doesn't materialize at
these depths in GHC 9.14. The closure-chain tax from traversal
dominates before O(n²) does.

---

## Summary

The Mendler case is `viewl` for traced categories. The GADT hierarchy
is `Circuit → Free → arr` via `freeze` then `runFree`. `Queue` is the
efficient inspectable encoding of `Free`. `Hyper` is the coinductive
dual — fast to compose, not to eliminate.

**Next:** [06-some-more-knots.md](06-some-more-knots.md) — making
stuff: parsers, pipes, loops, agents, metering.

---

## References

- [Van der Ploeg & Kiselyov (2014)](https://doi.org/10.1145/2633357.2633360) — Reflection Without Remorse
- [Okasaki (1999)](https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf) — Purely Functional Data Structures
- `free-category` package — `Queue`, `ListTr`, `C` from the RwR ecosystem
- `~/haskell/perf-circuits/` — benchmark harness comparing all paths
