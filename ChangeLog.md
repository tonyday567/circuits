# Revision history for circuits

## 0.3.0.0 — 2026-07-22

Kernel tidy before release: split the bimonoid signature and make
`Layer.run` default to `bind id`.

*Signature split*

- `Circuit.Algebra.SigBimonoid` is replaced by `SigCopyDiscard` and
  `SigMergeZero`. The old bundled signature forced users to supply a full
  `Bimonoid` instance even when they only needed copy/discard wiring.
- `Circuit.Net.Net` constructors now carry the precise constraint:
  `Copy`/`Discard` require `CopyDiscard`, `Plus`/`Zero` require `MergeZero`.
- `AlgBimonoidal` and `AlgNet` updated to the new signature pair; the
  `algNet` / `runAlgNet` isomorphisms match the new injection order.

*Layer coherence*

- `Circuit.Layer.Layer.run` now defaults to `bind id`. The separate direct
  implementations are removed from `Free`, `Sym`, `Loop`, and `Net`.
- `Run Free arr` now includes `Discrete arr`, which is the price of the
  default. `Circuit.Free.freeze` remains available for same-category folds
  that do not have a `Discrete` base.

*Migrating*

- Replace `SigBimonoid` with `SigCopyDiscard :+: SigMergeZero`.
- Replace `SigCopy`/`SigDiscard`/`SigPlus`/`SigZero` patterns at the
  corresponding injection depth (now five right-injections for copy/discard,
  six for plus/zero in `AlgNet`).
- Any custom `Net` consumer pattern-matching on `Copy`/`Discard`/`Plus`/`Zero`
  now sees split constraints instead of `Bimonoid`.

## 0.2.0.0 — 2026-07-20

Total revamp of the API around a single normal-form GADT and a clearer
separation between syntax and semantics.

*New core vocabulary*

- `Circuit.Loop.Loop t arr a b` is the free traced monoidal category in
  normal form: either `Lift` (a base arrow) or `Knot` (a feedback loop).
  Composition fuses via the `Category` instance, so every value has at most
  one `Knot` at the top.
- `Circuit.Free.Free` is the free category (`Lift`, `Compose`).
- `Circuit.Sym.Sym` is the free symmetric monoidal category (`Lift`,
  `Compose`, `Par`, `Swap`).
- `Circuit.Net.Net` is the free traced PROP with a bimonoid: `Lift`,
  `Compose`, `Par`, `Swap`, `Knot`, `Copy`, `Discard`, `Plus`, `Zero`.
  Wiring stays inspectable for `transpose`, metering, and fusion.
- `Circuit.Hyper.Hyper` is the final coinductive encoding; `encode` and
  `observe` move between `Loop` and `Hyper`.

*Semantics split across two tracks*

- Structural semantics: `Circuit.Category.Category` → `Circuit.Channel.Channel`
  → `Circuit.Channel.Strength` → `Circuit.Channel.Traced`.
- Functorial semantics: `Circuit.Category.Category` → `Circuit.Tensor.Tensor`
  → `Circuit.Tensor.Action`.

*Layer tower*

- `Circuit.Layer.Layer` unifies the free-forgetful folds: `unit`, `run`,
  `bind`, `lower`. `Law`, `Run`, and `Bind` associated types capture what
  each layer needs from its target and source categories.

*Ends, boxes, and queues*

- `Circuit.Ends` replaces the old `Circuit.Box` and `Circuit.Queue` modules.
  Companion/conjoint ends (`Out`, `In`), matched `Ends`, `box`,
  `boxAsymmetric`, `Queue` strategies, `openSTM`, and `openIO` all live here.

*Dagger and bimonoid*

- `Circuit.Dagger` consolidates `CopyDiscard`, `MergeZero`, `Bimonoid`,
  `Dagger`, and `transpose`.

*À-la-carte syntax*

- `Circuit.Algebra` provides compositional signatures (`SigCompose`,
  `SigKnot`, `SigPar`, `SigSwap`, `SigBimonoid`) and direct GADT ↔ syntax
  isomorphisms (`algLoop`, `runAlgLoop`, `algNet`, `runAlgNet`).

*Operators*

- Forward composition is `(.>)`; backward composition is `(.)` from
  `Control.Category`.
- Forward/backward application operators `(|>)` and `(<|)` live in
  `Circuit.Category`.

*Removed*

- `Circuit.Trace` / `Circuit` GADT name retired to `Circuit.Loop`.
- `Circuit.Strength`, `Circuit.Monoidal`, `Circuit.Classes`,
  `Circuit.Adjunction`, `Circuit.Signature`, `Circuit.Box`, `Circuit.Queue`,
  `Circuit.Loopd`, and `Circuit.Dup` are gone; their contents are merged or
  renamed as above.
- `cellIO`, `openCollectSTM`, `openCollectIO`, `openBatchSTM`,
  `openBatchMaybeSTM`, `freeToMon`, `monTranspose`, `AlgSymKnot`,
  `loopToSymKnot`, and the old `traceToAlg` / `algToTrace` names are removed.
  Helpers that are not core API moved to `circuits-examples`.
- The `signature-tests` Cabal test suite is removed; verification is via
  `cabal-docspec` and `cabal check`.

*Examples and companion libraries*

- Example cards moved to the separate `circuits-examples` repository.
- `Circuit.AD` moved to the `circuits-ad` package.
