# Revision history for circuits

## 0.1.0.0 — 2025-05-26

- Initial release (not yet published to Hackage).
- **Circuit** — GADT: Lift, Compose, Knot. Free traced monoidal category with Profunctor instance.
- **Hyper** — final coinductive encoding. Category, Profunctor, Functor instances. Feedback dissolves into the type.
- **Trace** class with `(,)` (lazy knot) and `Either` (iteration) tensors. `Trace (Kleisli IO) Either` via delimited continuations.
- Triangle identity: `reify = lower . encode`. `flatten` for the reverse direction (lossy).
- `ambient` / `ambientBy` — state wire threading through feedback loops.
- Cocartesian combinators in `Circuit.Monoidal`: `coassoc`, `coassoc'`, `coseed`, `coabsorbL`, `coabsorbR`, `coreleaseL`, `coreleaseR`.
- `Braided` class with instances for `(,)` and `Either` — merged with cartesian/cocartesian structure into `Circuit.Monoidal`.
- `cellIO` — stateful `Kleisli IO` arrow via `IORef` for strict accumulators in `(,)`-traced pipelines.
- Removed `Circuit.Queue` and `these` dependency — consolidated into `circuits-io`.
- Removed `Iter`/`loopIter` — duplicates `Trace (Kleisli m) Either`.
- Canonical API uses lowercase names: `lift`, `lower`, `reify`, `encode`, `push`, `run`, `trace`, `untrace`.
- Notation conventions in `other/symbols.md`. No `Circuit.Symbols` module — symbols are prose notation, not Haskell identifiers.
- Narrative arc in `other/`: marks → GADT → Hyper → tensors → Mendler case → making stuff.
- 15+ example cards: parsers, pipes, while-loops, Elgot iteration, delimited continuations, proequipment, ambient, hyper-chain, state, pure-queue, etc.
- Boundary rule: symbols in tables/axioms only; names everywhere else.
- `Step` convention unified with `Trace (->) Either`: `Left` = feedback, `Right` = exit.
- Push is Hyper-only — no direct GADT counterpart.
- Axiom doctests and QuickCheck properties for JSV laws and Hyper embedding/functoriality.
- No Applicative or Monad instances — these collapse feedback structure.
- README: tank mode, Hackage/CI badges, paper link.
