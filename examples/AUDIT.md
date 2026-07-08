# Examples audit

Last updated: 2026-07-08.

This audit covers the `examples/` directories in the circuits-related
repositories. Status legends:

- 🟢 **working** — compiles (for `.hs`) and aligns with current API names.
- 🟡 **attention** — needs minor updates (naming, commentary) or has known
  non-fatal issues.
- 🔴 **discard / major rework** — broken by API changes or depends on removed
  modules; probably not worth rescuing without a deliberate rewrite.

---

## `circuits-io`

| file | type | status | notes |
|------|------|--------|-------|
| `examples/cabal-repl.hs` | executable | 🟢 | Cabal target `cabal-repl-example`. Builds and runs. Uses only `Circuit.Repl`, unaffected by rename. |
| `examples/box-core.hs` | example module | 🟢 | Updated to `Trace`, `run`, and `Identity` to avoid overlapping `Traced (Kleisli m) Either` instances. Compiles cleanly. |
| `examples/box-api-audit.md` | design doc | 🟡 | A migration design doc from the old `Circuit` names to the current `Trace`/`run` API. Useful historical context but should be updated or archived once the migration is final. |
| `examples/box-concurrent.md` | design doc | 🟡 | Likely references old names; needs a pass. |
| `examples/box-socket.md` | design doc | 🟡 | Likely references old names; needs a pass. |
| `examples/channel-ends.md` | design doc | 🟡 | Likely references old names; needs a pass. |
| `examples/channel-kw.md` | design doc | 🟡 | Likely references old names; needs a pass. |
| `examples/nucleus.md` | design doc | 🟡 | References old `Knot`, `loom`, `Circuit` names. Deep design doc; worth updating if it stays in the repo. |

---

## `circuits-parser`

| file | type | status | notes |
|------|------|--------|-------|
| `examples/debug-deck.hs` | example | 🟢 | Compiles. Minor unused-import / missing-signature warnings only. |
| `examples/deck-test.hs` | example | 🟢 | Compiles cleanly. |
| `examples/mealy-example.hs` | example | 🟢 | Compiles cleanly. Comment says "Mealy machines as Circuits" — should say "as Traces" for consistency. |
| `examples/step-test.hs` | example | 🟢 | Compiles cleanly. |
| `examples/bench-parse.hs` | example | 🔴 | Imports removed module `Circuit.Perf (times)`. No replacement exists. Either discard or rewrite against `circuits-meter` (`Circuit.Meter.Time.ticks`). |

---

## `mealy`

| file | type | status | notes |
|------|------|--------|-------|
| `examples/ProducerConsumer.hs` | example module | 🟡 | Code aligns with current API, but it is not a Cabal target, so `import Data.Mealy` fails when compiled standalone. Add as an executable/example stanza or move to `test/` if it should be guaranteed to build. |
| `examples/circuits-mealy.md` | design doc | 🟢 | Updated interpreter calls to `run` and the `Trace` class to `Traced`. Conceptual/code snippets still need manual checking if promoted to a runnable example. |

---

## `circuits`

The `circuits/examples/` directory is large and mostly design/exploration
`.md` cards. A full pass is beyond a quick tidy-up. The table below flags the
ones that were updated or are known to be high-impact.

| file | type | status | notes |
|------|------|--------|-------|
| `examples/circuits.md` | quick reference | 🟢 | Rewritten: import list matches current `Circuit` exports; `Trace`/`Arr`/`Knot`/`run`. |
| `examples/circuit.md` | quick reference | 🟢 | Rewritten: `Trace` GADT intro; `observe` replaces old `lower` for Hyper. |
| `examples/words.md` | worked example | 🟢 | `Trace t (Kleisli IO)`, `Arr`/`Knot`, `run`, `Traced`. |
| `examples/parser.md` | design doc | 🟢 | `Trace`/`Arr`/`Knot` parser combinators; `run`. |
| `examples/while.md` | design doc | 🟢 | Loop patterns over `Trace Either (->)` with `run`. |
| `examples/traced.md` | design doc | 🟢 | Explains `Traced` class, `trace`/`untrace`. |
| `examples/hyper.md` | design doc | 🟢 | Hyper API; `observe` replaces old `lower`. |
| `examples/hyper-chain.md` | design doc | 🟢 | Hyper chain composition; `observe`. |
| `examples/encode-either.md` | design doc | 🟢 | Why `Traced Hyper Either` is absent; `encodeEither`/`runEither`. |
| `examples/lift-trace-commute.md` | design doc | 🟢 | `lift`/`trace` commutation; `observe`. |
| `examples/reader-monad.md` | design doc | 🟢 | Escape hatch to monadic style; `observe`/`run`. |
| `examples/resource-io.md` | design doc | 🟢 | Resource lifecycle via `Trace Either (Kleisli IO)` and `run`. |
| `examples/state.md` | design doc | 🟢 | Visible / ambient / hidden state mechanisms. |
| `examples/ambient.md` | design doc | 🟢 | `ambientBy` for custom braids; `ambient` is the canonical braid version. |
| `examples/debug-trace.md` | design doc | 🟢 | Feedback as history; uses `ambientBy`. |
| `examples/effects.md` | design doc | 🟢 | Cross-library effects comparison; `observe`/`freeze` naming updated. |
| `examples/pure-queue.md` | design doc | 🟢 | Pure queue strategies; no stale naming. |
| `examples/pure-queue-circuit.md` | design doc | 🟢 | Queue ends lifted into `Trace (,) (->)` with `run`. |
| `examples/pure-queue-ends.md` | design doc | 🟢 | Simpler `[a]` queue ends. |
| `examples/pure-queue-test.md` | design doc | 🟢 | Pipeline test using `Trace`/`Arr`/`run`. |
| `examples/arrow-proarrow.md` | design doc | 🟡 | Design-only; `Circuit.Signature.Optic`/`Free SigCompose` are not implemented. |
| `examples/proarrow.md` | design doc | 🟡 | Design-only; advanced proarrow bridge. |
| `examples/proequip.md` | design doc | 🟡 | Design-only; profunctor equipment lemmas open. |
| `examples/lawvere.md` | design doc | 🟡 | Design-only; exponential adjunction speculation. |
| `examples/elgot-abacus.md` | design doc | 🟡 | Design-only; `Circuit.Abacus` not implemented. |
| `examples/yaya.md` | design doc | 🟡 | Design-only; `Circuit.Hyper.Fix` not implemented. |
| `examples/wirecat.md` | design doc | 🟡 | Design-only; retired WireCat integration sketch. |
| `examples/relations.md` | design doc | 🟡 | Design-only; `Rel` base arrow not implemented. |
| `examples/optics.md` | design doc | 🟡 | Design-only; no `Optic` module currently exists. |
| `examples/pipes.md` | design doc | 🟡 | Design-only; Proxy decomposition sketch. |
| `examples/words-circuit.svg`, `words-metered.svg` | assets | 🟢 | SVG diagrams; filenames are fine. |

### Recommendation for `circuits/examples/`

The directory has drifted into a mix of:

1. **Worked examples** (`words.md`) — keep and maintain.
2. **Design cards** (`parser.md`, `while.md`, `hyper.md`, etc.) — keep the good
   ones, update naming, archive the rest.
3. **Exploratory sketches** (`lawvere.md`, `elgot-abacus.md`, `yaya.md`) —
   probably belong in `buff/` or an archive rather than shipping with the
   library.

A reasonable next step is to move the speculative cards out of `examples/`
and leave only the maintained worked examples and a small set of current
 design cards.

---

## `circuits-meter`

| file | type | status | notes |
|------|------|--------|-------|
| `examples/core-analysis.md` | design doc | 🔴 | Deeply tied to the old `Circuit` GADT, `Knot` constructor, and pre-`run` interpreter implementation. It is a core-dump style analysis of the *old* code. Retain as historical archive if useful, but do not present as current documentation. |
| `examples/nub.md` | design doc | 🟡 | Needs checking against current `Circuit.Meter` API. |
| `examples/scaling.md` | design doc | 🟡 | Needs checking against current `Circuit.Meter` API. |
| `examples/seismo.md` | design doc | 🟡 | Needs checking against current `Circuit.Meter` API. |

---

## Cross-cutting issues found

1. **Overlapping `Traced (Kleisli m) Either` instances.** The generic
   `Monad m => Traced (Kleisli m) Either` instance overlaps with the
   `Traced (Kleisli IO) Either` instance. This makes polymorphic
   `run` over `Kleisli m Either` unusable (e.g. `box-core.hs` had to be
   specialised to `Identity`). Consider removing the `IO`-specific instance
   or making it opt-in via a newtype.

2. **`Circuit.Perf` is gone.** `circuits-parser/examples/bench-parse.hs`
   references it. No equivalent module exists in `circuits-meter` under that
   name.

3. **`ProducerConsumer.hs` is not built.** It lives in `mealy/examples/` but
   is not a Cabal component, so it rots silently.
