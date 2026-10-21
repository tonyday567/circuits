# Revision history for circuits

## 0.3.0.0 — unreleased

Linear-logic refactor: multiplicative/additive/exponential connectives, the
factored machine core, polynomial interfaces, shared-medium scheduling, and
the move from `Loop` to `Trace`. A second consolidation then merged the
machine vocabulary into `Circuit.Machine` / `Circuit.Step`; the entries
below describe the tree as it stands.

*Machine core*

- `Circuit.Machine` hosts the factored machine: `Body` (init/commit/emit),
  `Step` (the one-tick arrow), `Moore`/`MooreT` (the channel sealed behind
  the body), and `Poles` (init/commit/emit ends). Runners `scan`, `fold`,
  `delay`, `register`, and `mealyToKnot` live here.
- Cells, bodies, Moore machines, and poles are all factorisations of the
  one `Step`/`Body` shape over a channel, under tensors `t t'`, in a base
  arrow `arr`.

*Free traced syntax*

- `Circuit.Trace` is the free traced monoidal category (constructors
  `base` and `yank`), replacing the old `Circuit.Loop`. It documents the
  Central Sliding side-condition (Benton–Hyland Def 3.2): the free normal
  form is sound over a premonoidal base only when structural maps are
  central.
- `Circuit.Syntax` is the generic substrate and its interpretation
  (`eval`, `run`, `Lift`).
- `Circuit.Net` is wiring with bimonoid rows; `melt` forgets wiring into
  `Trace`. Constructors carry the precise structural constraints:
  `Copy`/`Discard` require `CopyDiscard`, `Plus`/`Zero` require
  `MergeZero`.
- `Circuit.Stream` holds the neutral stream interface (`Uncons`, `Snoc`)
  used by stream runners.
- `Circuit.Span` (spans, `bodyFromSpan`/`spanFromBody`) and
  `Circuit.Pullback` (linear cotangent maps for reverse mode) fill the
  equipment ladder.

*Polynomial interfaces*

- `Circuit.Poly` promotes polynomial expressions to a kind, with the `Eval`
  GADT witnessing the value shape, position/direction families `Pos`/`Dir`,
  and the `PTensor` Dirichlet product.

*Connectives and scheduling*

- `Circuit.Linear` adds linear-logic classes: `Lolli` (internal hom) and
  `Exponential` with `Bang`/`WhyNot` modalities.
- `Circuit.Shared` gives shared-medium fusion (`sharedBy`) over a feedback
  channel, driven by a `Schedule` and `Pick` (`PickL`/`PickR`/`Both Bias`),
  receipt transcripts, and the `Stamped` boundary token.
- `Circuit.Tensor.superpose` fuses two independent-feedback bodies when the
  tensor matches.
- `Circuit.Bimonoid` splits the structural rules into `Copy`/`Discard`
  (`CopyDiscard`) and `Merge`/`Zero` (`MergeZero`).

*Structural ladder*

- `Circuit.Traced` is the structural class ladder: `Assoc`, `Slide`,
  `Strength`, `Yank`; instances for `(->)` and `K m` over the `(,)`,
  `Either`, and `These` tensors. `Unfold` lives here too: coiteration over a
  grammar, with `Nu` the run's output shape.

*Oracles*

- The `circuits-axioma` executable and its `Axioma.*` topic modules witness
  bimonoid laws, machine conversions, centrality, shared-medium scheduling,
  and polynomial poles.

*Removed / merged (cumulative over both consolidations)*

- `Circuit.Loop` is retired; use `Circuit.Trace`.
- `Circuit.Ends`, the intermediate `Circuit.Poles` module, and
  `Circuit.Equip` are retired; the surviving ends vocabulary is `Poles` in
  `Circuit.Machine` and the one-tick arrow in `Circuit.Step`.
- `Circuit.Channel` and `Circuit.System` are retired, with `SystemT` and
  `mooreSystem` superseded by the `Machine`/`Body` families.
- `Circuit.Moore` and `Circuit.Process` no longer exist as modules; the
  Moore machine and its process spellings live in `Circuit.Machine`.
  `Circuit.Par`, `Circuit.Optic`, `Circuit.Layer`, and `Circuit.Dagger`
  were withdrawn in the second consolidation.
- `Circuit.Fragment` and its bundled `SigBimonoid` are gone; free syntax is
  built from the generic substrate in `Circuit.Syntax` plus the signature
  modules `Circuit.Trace` and `Circuit.Net`.
- `Circuit.Rel` (finite relations, the two-grade reference semantics) moved
  to the sibling package `circuits-rel`, along with the `FinRel` topic of
  the oracle runner (now `circuits-rel-axioma`). The `Circuit` umbrella no
  longer re-exports it.
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
