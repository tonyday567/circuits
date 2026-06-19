# Examples audit

Last updated: 2026-06-19.

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
| `examples/box-core.hs` | example module | 🟢 | Updated to `Trace`, `realise`, and `Identity` to avoid overlapping `Traced (Kleisli m) Either` instances. Compiles cleanly. |
| `examples/box-api-audit.md` | design doc | 🟡 | A migration design doc from the old `Circuit`/`Knot`/`reify` names. Useful historical context but should be updated or archived once the migration is final. |
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
| `examples/circuits-mealy.md` | design doc | 🟢 | Updated `reify` → `realise` and `Trace` class → `Traced`. Conceptual/code snippets still need manual checking if promoted to a runnable example. |

---

## `circuits`

The `circuits/examples/` directory is large and mostly design/exploration
`.md` cards. A full pass is beyond a quick tidy-up. The table below flags the
ones that were updated or are known to be high-impact.

| file | type | status | notes |
|------|------|--------|-------|
| `examples/words.md` | worked example | 🟢 | Updated to `Trace t (Kleisli IO)`, `Trace` constructor, `realise`, `Traced`. |
| `examples/parser.md` | design doc | 🟢 | Updated `Circuit` → `Trace`, `Knot` → `Trace`, `reify` → `realise`. |
| `examples/while.md` | design doc | 🟢 | Updated `Knot` → `Trace`, `reify` → `realise`, `Trace` class → `Traced`. |
| `examples/pure-queue-circuit.md` | design doc | 🟡 | Contains `reify pipe ()` and likely old type order. Needs a pass. |
| `examples/reader-monad.md` | design doc | 🟡 | References `reify`, `Circuit`, old module paths. |
| `examples/pure-queue*.md` | design docs | 🟡 | Queue design sketches; likely use old names. |
| `examples/hyper*.md` | design docs | 🟡 | Hyper examples; check `encode`, `lower`, `run` naming. |
| `examples/effects.md` | design doc | 🟡 | Likely outdated. |
| `examples/state.md` | design doc | 🟡 | Likely outdated. |
| `examples/traced.md` | design doc | 🟡 | May be partly superseded by `Circuit.Traced` haddock. |
| `examples/wirecat.md` | design doc | 🟡 | Likely outdated. |
| `examples/relations.md` | design doc | 🟡 | Likely outdated. |
| `examples/optics.md` | design doc | 🟡 | Likely outdated. |
| `examples/proarrow.md`, `proequip.md` | design docs | 🟡 | Advanced design docs; update if kept. |
| `examples/lawvere.md`, `elgot-abacus.md`, `yaya.md` | design docs | 🟡 | Highly speculative / exploratory. Consider archiving if not actively maintained. |
| `examples/ambient.md` | design doc | 🟡 | Check `ambient`, `ambientBy` naming. |
| `examples/resource-io.md` | design doc | 🟡 | Likely outdated. |
| `examples/debug-trace.md` | design doc | 🟡 | Likely outdated. |
| `examples/circuits.md`, `circuit.md` | design docs | 🔴 | Almost certainly use the old `Circuit` GADT name throughout. Either rewrite as `Trace` intro or discard. |
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
| `examples/core-analysis.md` | design doc | 🔴 | Deeply tied to the old `Circuit` GADT, `Knot`, and `reify` implementation. It is a core-dump style analysis of the *old* code. Retain as historical archive if useful, but do not present as current documentation. |
| `examples/nub.md` | design doc | 🟡 | Needs checking against current `Circuit.Meter` API. |
| `examples/scaling.md` | design doc | 🟡 | Needs checking against current `Circuit.Meter` API. |
| `examples/seismo.md` | design doc | 🟡 | Needs checking against current `Circuit.Meter` API. |

---

## Cross-cutting issues found

1. **Overlapping `Traced (Kleisli m) Either` instances.** The generic
   `Monad m => Traced (Kleisli m) Either` instance overlaps with the
   `Traced (Kleisli IO) Either` instance. This makes polymorphic
   `realise` over `Kleisli m Either` unusable (e.g. `box-core.hs` had to be
   specialised to `Identity`). Consider removing the `IO`-specific instance
   or making it opt-in via a newtype.

2. **`Circuit.Perf` is gone.** `circuits-parser/examples/bench-parse.hs`
   references it. No equivalent module exists in `circuits-meter` under that
   name.

3. **`ProducerConsumer.hs` is not built.** It lives in `mealy/examples/` but
   is not a Cabal component, so it rots silently.
