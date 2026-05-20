# Revision history for circuits

## 0.1.0.0 — 2025-05-26

- Initial release (not yet published to Hackage).
- **Circuit** — GADT: Lift, Compose, Knot. Free traced monoidal category with Profunctor instance.
- **Hyper** — final coinductive encoding. Category, Profunctor, Functor instances. Feedback dissolves into the type.
- **Trace** class with `(,)` (lazy knot) and `Either` (iteration) tensors. `Trace (Kleisli IO) Either` via delimited continuations.
- Triangle identity: `reify = lower . encode`. `flatten` for the reverse direction (lossy).
- `ambient` — state wire threading through feedback loops (requires Profunctor for `dimap braid braid` on Knot case).
- Canonical API uses lowercase names: `lift`, `lower`, `reify`, `encode`, `push`, `run`, `trace`, `untrace`.
- Notation conventions in `other/symbols.md`. No `Circuit.Symbols` module — symbols are prose notation, not Haskell identifiers.
- Narrative arc in `other/`: marks → GADT → Hyper → tensors → Mendler case → making stuff.
- 15 example cards: parsers, pipes, while-loops, Elgot iteration, delimited continuations, proequipment, ambient, hyper-chain, etc.
- Boundary rule: symbols in tables/axioms only; names everywhere else.
- `Step` convention unified with `Trace (->) Either`: `Left` = feedback, `Right` = exit.
- Push is Hyper-only — no direct GADT counterpart.
- Axiom doctests and QuickCheck properties for JSV laws.
- No Applicative or Monad instances — these collapse feedback structure.
- README: tank mode, Hackage/CI badges, paper link.
