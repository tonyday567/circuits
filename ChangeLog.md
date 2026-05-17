# Revision history for circuits

## 0.1.0.0 — 2025-05-17

- Initial release.
- `Circuit` GADT: Lift, Compose, Knot — free traced monoidal category with Profunctor instance.
- `Hyper`: final coinductive encoding. Category, Profunctor, Functor instances. Feedback dissolves into the type.
- `Trace` class with `(,)` (lazy knot) and `Either` (iteration) tensors. `Trace (Kleisli IO) Either` via delimited continuations.
- Triangle identity: `reify = lower . encode`. `flatten` for the reverse direction (lossy).
- Five symbolic operators: ↑ lift, ↓ lower, ⊙ compose, ⊲ push, ⥁ run.
- Axiom doctests and QuickCheck properties for JSV laws on both tensors.
- 12 example cards: lazy knot-tying, parsers, pipes, Elgot iteration, delimited continuations, mealy agents, encode-either gap, reader-monad pattern.
- Six narrative chapters in `other/`: marks → GADT → Hyper → tensors → RwR → circuits-io frontier.
- No Applicative or Monad instances — these collapse feedback structure. See `examples/reader-monad.md`.
