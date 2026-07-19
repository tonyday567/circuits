# Revision history for circuits

## 0.2.0.0 — 2026-07-09

*BREAKING: **The GADT is renamed from `Circuit` to `Trace`.** The previous name `Circuit` is retired to the library-level metaphor. Constructors are now `Arr` (plain base arrow) and `Knot` (feedback loop). The trace class is renamed from `Trace` to `Traced`. Type parameter order is now tensor-first: `Trace t arr a b` and `Net t arr a b`.*

*BREAKING: **Normal-form `Trace`.** Composition fuses via the `Category` instance, so every `Trace` is in normal form: at most one `Knot` at the top over a base-arrow body. There is no explicit `Compose` constructor and no Mendler case in `run`.*

*BREAKING: **`Circuit.Traced` is merged into `Circuit.Trace`.** The `Traced`
class, base instances, and `cellIO` now live alongside the `Trace` GADT in a
single module.*

*BREAKING: **`Traced` takes the tensor first.** The class is now
`Traced t arr` (was `Traced arr t`), matching `Trace t arr a b`.*

*BREAKING: **`Channelled` is replaced by `Monoidal`.** The structural
superclass lives in `Circuit.Monoidal`. `Traced` is now a subclass of
`Monoidal`; the `Trace`/`Net` `Category` instances require only `Traced t arr`.*

*BREAKING: **`Circuit.Classes` is renamed to `Circuit.Category`.** MicroHs
support and CPP shims are removed; `Category`, `Discrete`, `Ob`, `(>>>)`, and
`(<<<)` now live in the GHC-only `Circuit.Category` module.*

*BREAKING: **The free-layer vocabulary is unified under `Circuit.Layer`.*
`FreeLayer` is renamed to `Layer`; `Lawful` is renamed to `Law`.
`rightAdjunct` becomes `bind`; `leftAdjunct` becomes `lower`.
The per-layer folds are now `run` with a type application:*

  * `run @Free` (was `runFree`)
  * `run @(Trace t)` (was `run`)
  * `run @(Net t)` (was `weave`)

*`hoist` becomes `hmap`; `realise` becomes `run`; `Hyper.lower` becomes `observe`.
`Circuit.Adjunction` is removed; `Circuit.Layer` is the canonical module.
All instances are now orphan `Layer` instances in `Circuit.Free`, `Circuit.Trace`,
and `Circuit.Net`.*

*BREAKING: **`Circuit.Signature` is renamed to `Circuit.Algebra`.**
The generic `Free` construction becomes `Syntax`, `Handler` becomes `Algebra`,
`handle` becomes `alg`, and the folds become `eval`/`evalInto`.*

*New: **Circuit.Net** — the free traced PROP with a bimonoid. Structural rows: `Par`, `Swap` (monoidal), `Copy`, `Discard` (comonoid), `Plus`, `Zero` (monoid), all inspectable before interpretation. `Net.Knot` takes a `Net` body so `transpose` can recurse into loops. Transposition is structural recursion: `Compose` reverses, `Copy↔Plus`, `Discard↔Zero`, `Knot↔Knot`.*

*New: **Circuit.Dagger** — consolidated module for `Monoid`, `Comonoid`, `Dagger`, and `Bimonoid`. `Monoid` (was `Additive`) provides channel-object addition; `Comonoid` (was `Dup`) provides `copy` and `discard`; `Dagger` (was `Duplex`) is the free dagger category with `transpose` (was `transposeDuplex`); `Bimonoid` (was `Linear`) is the constraint synonym.*

*New: **Co/Contra** — companion/conjoint channel ends, exported from `Circuit.Trace`.*

*New: **Circuit.Int** — intensional morphism constructors over polynomial channel shapes, with `IntMorph` composition via `par`, `braid`, and `trace`.*

*New: **Circuit.Poly** — polynomial object kind for channel shapes (`Y`, `Const`, `Exp`, `Sum`, `Prod`, `Tensor`, `Comp`) with `Netlist` conversion to position/direction pairs.*

*Removed: **Circuit.AD** moved to circuits-ad package. The Diff arrow, backprop, traceStar, and Oracle live there.*

*Removed: The `signature-tests` Cabal test suite. Verification is now via
`cabal-docspec` (doctests) and `cabal check`.*

*Fixed: README updated to the `Arr`/`Knot` normal form and the `Layer` tower.*

*Quality: ormolu-formatted, hlint-clean, 100% Haddock coverage on library modules, 249 examples and 75 setup blocks pass `cabal-docspec`, 12 property laws documented in source. GHC 9.14 backend.*

## 0.1.0.0 — 2025-05-26

- Initial release (not yet published to Hackage).
- **Trace** — GADT: Lift, Compose, Trace. Free traced monoidal category with Profunctor instance.
- **Hyper** — final coinductive encoding. Category, Profunctor, Functor instances. Feedback dissolves into the type.
- **Trace** class with `(,)` (lazy knot) and `Either` (iteration) tensors. `Trace (Kleisli IO) Either` via delimited continuations.
- Triangle identity: `realise = lower . encode`. `flatten` for the reverse direction (lossy).
- `ambient` / `ambientBy` — state wire threading through feedback loops.
- Cocartesian combinators in `Circuit.Monoidal`: `coassoc`, `coassoc'`, `coseed`, `coabsorbL`, `coabsorbR`, `coreleaseL`, `coreleaseR`.
- `Braided` class with instances for `(,)` and `Either` — merged with cartesian/cocartesian structure into `Circuit.Monoidal`.
- `cellIO` — stateful `Kleisli IO` arrow via `IORef` for strict accumulators in `(,)`-traced pipelines.
- Removed `Circuit.Queue` and `these` dependency — consolidated into `circuits-io`.
- Removed `Iter`/`loopIter` — duplicates `Trace (Kleisli m) Either`.
- Canonical API uses lowercase names: `lift`, `lower`, `realise`, `encode`, `push`, `run`, `trace`, `untrace`.
- Notation conventions in `other/symbols.md`. No `Circuit.Symbols` module — symbols are prose notation, not Haskell identifiers.
- Narrative arc in `other/`: marks → GADT → Hyper → tensors → Mendler case → making stuff.
- 15+ example cards: parsers, pipes, while-loops, Elgot iteration, delimited continuations, proequipment, ambient, hyper-chain, state, pure-queue, etc.
- Boundary rule: symbols in tables/axioms only; names everywhere else.
- `Either` iteration convention: `Left` = feedback (continue), `Right` = exit.
- Push is Hyper-only — no direct GADT counterpart.
- Axiom doctests and QuickCheck properties for JSV laws and Hyper embedding/functoriality.
- No Applicative or Monad instances — these collapse feedback structure.
- README: tank mode, Hackage/CI badges, paper link.
