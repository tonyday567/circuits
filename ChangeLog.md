# Revision history for circuits

## 0.2.0.0 — 2026-06-13

*BREAKING: **Knot takes a Circuit body.** `Knot :: Circuit arr t (t a b) (t a c) -> Circuit arr t b c`. Previously `Knot :: arr (t a b) (t a c) -> Circuit arr t b c`. The body is now a full `Circuit`, making loop wiring inspectable — transpose can recurse into knot bodies, the encode case is `trace (encode k)` (uniform recursion, no special `lift`), and the Mendler case in reify works uniformly. JSV's trace is an operation on all morphisms, not just generators, so recursive bodies are the correct presentation of the free traced category.*

*New: **Circuit.Net** — the free traced PROP with a bimonoid. Structural rows: Par, Swap (monoidal), Copy, Discard (comonoid), Add, Zero (monoid), all inspectable before reify. Transposition (`transpose`) is structural recursion: Compose reverses, Copy↔Add, Discard↔Zero, Knot↔Knot.*

*New: **Circuit.Dagger** — consolidated module for 'Monoid', 'Comonoid', 'Dagger', and 'Bimonoid'. 'Monoid' (was 'Additive') provides channel-object addition; 'Comonoid' (was 'Dup') provides 'copy' and 'discard'; 'Dagger' (was 'Duplex') is the free dagger category with 'transpose' (was 'transposeDuplex'); 'Bimonoid' (was 'Linear') is the constraint synonym.*

*New: **Co/Contra** — companion/conjoint channel ends, now exported from Circuit.Circuit directly.*

*Removed: **Circuit.AD** moved to circuits-ad package. The Diff arrow, backprop, traceStar, and Oracle live there.*

*Fixed: README, symbols.md, and arc chapters 02–03 updated for the new Knot shape. Triangle proof in 03 redone for `trace (encode k)`.*

*Quality: 100% haddock coverage (54/54), 123/123 doctests, ormolu/formatted, hlint/clean. GHC 9.14 backend.*

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
