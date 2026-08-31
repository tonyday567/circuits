# Revision history for circuits

## 0.3.0.0 — unreleased

Linear-logic refactor: multiplicative/additive/exponential connectives, the
knot-body category, polynomial interfaces, shared-medium scheduling, and the
move from `Loop` to `Trace`.

*Knot-body category and trace syntax*

- `Circuit.Body` introduces `Body t ch arr a b`, the category
  `arr (t ch a) (t ch b)` that underlies loops, processes, systems, and
  channel poles.
- The free traced monoidal category is now `Circuit.Trace.Trace` (with
  constructors `base` and `yank`), replacing the old `Circuit.Loop.Loop`.
- `Circuit.Layer` hosts the free category `Free`, with `freeze` for
  same-category interpretation. `Layer.run` now defaults to `bind id`.
- `Run Free arr` now includes `Discrete arr`, which is the price of the
  default. `freeze` remains available for same-category folds that do not
  have a `Discrete` base.

*Polynomial interfaces and stateful processes*

- New modules `Circuit.Poly`, `Circuit.Channel`, and `Circuit.System`.
  `SystemT t arr s p` is `Body t arr s (Dir p) (Pos p)`; `System` is the
  cartesian specialisation. `mooreSystem`, `runSystem`, and lens conversions
  live here.
- `Circuit.Process` provides `Process` as a Moore-machine base arrow,
  with `scan`, `fold`, `mealy`, `delay`, `register`, and conversions to/from
  `Body`, `System`, and `Trace Either (->)`.

*Multiplicative/additive connectives and scheduling*

- `Circuit.Linear` adds linear-logic classes: `Lolli` (internal hom) and
  `Exponential` with `Bang`/`WhyNot` modalities.
- `Circuit.Par` provides the multiplicative disjunction `⅋`, `Bot`, and
  linear distributors `distL` / `distR` / `mix`.
- `Circuit.Shared` gives shared-medium fusion (`sharedBy`) over a single
  feedback channel, driven by a `Schedule` and `Pick` (`L`/`R`/`Both Bias`).
- `Circuit.Tensor.superpose` fuses two independent-feedback bodies when the
  tensor matches.
- `Bias` is reused for additive disjunction in `Circuit.Poles`.

*Channel poles and bimonoid wiring*

- `Circuit.Poles` replaces the old `Circuit.Ends` API: companion `Out`,
  conjoint `In`, matched `Poles`, `close`, `box`, `copycat`, additive `pair`
  and `race`, and the `HasDual` unit-pole class.
- `Circuit.Bimonoid` splits the structural rules into `Copy`/`Discard`
  (`CopyDiscard`) and `Merge`/`Zero` (`MergeZero`).
- `Circuit.Net` constructors now carry the precise constraint:
  `Copy`/`Discard` require `CopyDiscard`, `Plus`/`Zero` require `MergeZero`.
- `Circuit.Dagger` provides the free dagger category and `transpose`.

*Free syntax substrate*

- `Circuit.Fragment` is removed. Free syntax is now built from the generic
  substrate in `Circuit.Syntax` plus the signature modules in
  `Circuit.Trace`, `Circuit.SMC`, `Circuit.Net`, and `Circuit.Shared`.
- `Circuit.SMC` is the free symmetric monoidal category over a wiring tensor.
- `Circuit.Net` is `SMC` plus bimonoid rows; `melt` forgets wiring into
  `Trace`.

*Trace honesty and oracles*

- `Circuit.Trace` documents the Central Sliding side-condition
  (Benton–Hyland Def 3.2): the free traced monoidal normal form is sound over
  a premonoidal base only when structural maps are central.
- `Circuit.FinRel` provides GF(2) linear relations as a reference semantics.
- The `circuits-axioma` executable witnesses bimonoid laws, `Process`
  semantics, `Body` conversions, centrality, and shared-medium scheduling.

*Removed / merged*

- `Circuit.Loop` is retired; use `Circuit.Trace`.
- `Circuit.Ends` is replaced by `Circuit.Poles`; `Circuit.Ends.State.*`
  modules are gone.
- `Circuit.Fragment` and its bundled `SigBimonoid` are gone.
- `Circuit.Free`, `Circuit.Sym`, `Circuit.Algebra`, `Circuit.Classes`,
  `Circuit.Monoidal`, `Circuit.Strength`, `Circuit.Adjunction`,
  `Circuit.Signature`, `Circuit.Box`, `Circuit.Queue`, `Circuit.Loopd`, and
  `Circuit.Dup` are gone; their contents are merged or renamed as above.

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

- Structural semantics: `Circuit.Category.Category` → `Circuit.Traced.Channel`
  → `Circuit.Traced.Strength` → `Circuit.Traced.Traced`.
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

- `Circuit.Fragment` provides compositional signatures (`SigCompose`,
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
