# Revision history for circuits

## 0.3.0.0 — unreleased

Linear-logic refactor: multiplicative/additive/exponential connectives, the
factored machine core, polynomial interfaces, shared-medium scheduling, and
the move from `Loop` to `Trace`. A second consolidation merged the machine
vocabulary into `Circuit.Machine` / `Circuit.Step`. A final naming pass then
put the public vocabulary on canonical domain terms — operations are named
for what they do, laws keep their names (`yanking`, `sliding`, the trace
axioms) — and the entries below describe the tree as it stands.

*The naming pass, final vocabulary*

- Traced core: `Yank`/`yank` → `Trace`/`trace`; `Slide`/`slide` →
  `OuterSwap`/`outerSwap`; `Action` → `Symmetric`. The `TraceC` constraint
  synonym and the `FreeSMC` target-side constraint are removed — use `Trace`
  and `Symmetric` directly. `Circuit.Tensor.innerSwap` is a derived adjacent
  transposition (`braid .> outerSwap .> assoc'`).
- Free syntax: `Circuit.Trace`'s type synonym `Trace` → `FreeTrace` (the
  class owns `Trace` now); `SigYank`/`YankBody` → `SigTrace`; the
  cocartesian one-knot synonym `Step` → `Iteration` (`Circuit.Step.Step`,
  the one-tick arrow, keeps its name).
- Bimonoid: `Merge.plus` → `merge`, `MergeT.plusT` → `mergeT`,
  `SigPlus` → `SigMerge` (with `SigMergeZero` parallel to `MergeZero`); the
  dagger family `transpose`/`mirrorNet`/`mirrorSMC` → `dagger`/`daggerNet`/
  `daggerSMC`. `Poly.dagger` is a separate, qualified operation.
- Machines: `Step.run` → `Step.step` (qualified access and pattern matching;
  the `Cell`/`FoldBody` step fields keep their names); `register` →
  `feedback`; `Poles.compose` → `pipe`; the body bundles are `FoldBody`,
  `TheseBody`, `EitherBody`, `LensBody`, `ProfunctorBody` with their
  fuse/unfuse and lens-bridge names spelled out.
- Polynomial/shared/linear: `Poly.Global` → `Constant` (`Point` remains the
  global-element constructor); `AlgShared` → `SharedTrace`;
  `BangWeaken.discardE` → `weaken`; `Linear.distL`/`distR` →
  `affineDistL`/`affineDistR`. `Circuit.Category.(<|)` is deleted (it
  duplicated `$`); `|>` and `<.` stay.
- The `Circuit` umbrella exports the categorical `dagger` (Poly's hidden
  there), exports `Point`, and no longer hides `run` — `Circuit.Syntax.run`
  stands alone as the fold.

*Machine core*

- `Circuit.Machine` hosts the factored machine: `Body` (init/commit/emit),
  `Step` (the one-tick arrow), `Moore`/`MooreT` (the channel sealed behind
  the body), and `Poles` (init/commit/emit ends). Runners `scan`, `fold`,
  `delay`, `feedback`, and `mealyToKnot` live here.
- Cells, bodies, Moore machines, and poles are all factorisations of the
  one `Step`/`Body` shape over a channel, under tensors `t t'`, in a base
  arrow `arr`.

*Free traced syntax*

- `Circuit.Trace` is the free traced monoidal category (`FreeTrace t arr`),
  replacing the old `Circuit.Loop`: signature `SigCompose :+: SigTrace`,
  constructors `Lift` and `trace`, and the `Knot` existential normal form
  (`Wire`, `Iteration`). It documents the Central Sliding side-condition
  (Benton–Hyland Def 3.2): the free normal form is sound over a premonoidal
  base only when structural maps are central.
- `Circuit.Syntax` is the generic substrate and its interpretation
  (`eval`, `run`, `Lift`).
- `Circuit.Net` is wiring with bimonoid rows; `melt` forgets wiring into
  `FreeTrace`: `melt :: (Symmetric w arr, Trace w arr) => Net w arr a b ->
  FreeTrace w arr a b`, with the law `run @Net = eval . melt` (same-tensor
  only; the cross-tensor spelling is not restored). Constructors carry the
  precise structural constraints: `Copy`/`Discard` require `CopyDiscard`,
  `Merge`/`Zero` require `MergeZero`. `daggerNet`/`daggerSMC` transpose
  nets built over `Dagger`.
- `Circuit.Stream` holds the neutral stream interface (`Uncons`, `Snoc`)
  used by stream runners.
- `Circuit.Span` (spans, `bodyFromSpan`/`spanFromBody`) and
  `Circuit.Pullback` (linear cotangent maps for reverse mode) fill the
  equipment ladder.

*Polynomial interfaces*

- `Circuit.Poly` promotes polynomial expressions to a kind, with the `Eval`
  GADT witnessing the value shape, position/direction families `Pos`/`Dir`,
  and the `PTensor` Dirichlet product. `Constant` introduces a constant
  position; `Point` remains the global-element constructor.

*Connectives and scheduling*

- `Circuit.Linear` adds linear-logic classes: `Lolli` (internal hom) and
  `Exponential` with `Bang`/`WhyNot` modalities; weakening is `weaken`, and
  the one-way affine distributors are `affineDistL`/`affineDistR` (unlike
  the invertible arrow-generic `Tensor.distl`/`distr`).
- `Circuit.Shared` gives shared-medium fusion (`sharedBy`) over a feedback
  channel, driven by a `Schedule` and `Pick` (`PickL`/`PickR`/`Both Bias`),
  receipt transcripts, and the `Stamped` boundary token; the free syntax is
  `SharedTrace`.
- `Circuit.Tensor.superpose` fuses two independent-feedback bodies when the
  tensor matches.
- `Circuit.Bimonoid` splits the structural rules into `Copy`/`Discard`
  (`CopyDiscard`) and `Merge`/`Zero` (`MergeZero`), and hosts the free
  dagger category (`Dagger`, `dagger`): the interlock that dualises the
  laws (fwd copy = bwd merge).

*Structural ladder*

- `Circuit.Traced` is the structural class ladder: `Assoc`, `OuterSwap`,
  `Strength`, `Trace`; instances for `(->)` and `K m` over the `(,)`,
  `Either`, and `These` tensors. `Unfold` lives here too: coiteration over
  a grammar, with `Nu` the run's output shape.

*Oracles*

- The `circuits-axioma` executable and its `Axioma.*` topic modules witness
  bimonoid laws, machine conversions, centrality, shared-medium scheduling,
  and polynomial poles — including the new structural pins: per-tensor
  outerSwap involution and decomposition, braid involution at `(,)` /
  `Either` / `These` / `K m`, and the derived `innerSwap` involution and
  decomposition (nondegenerate: distinct values in all three positions).

*Removed / merged (cumulative over both consolidations)*

- Retired names and where they went: `Yank`/`yank` → `Trace`/`trace`;
  `Slide`/`slide` → `OuterSwap`/`outerSwap`; `Action` → `Symmetric`;
  free-syntax `Trace` → `FreeTrace`; `SigYank`/`YankBody` → `SigTrace`;
  `TraceC`/`FreeSMC` removed; `plus`/`plusT`/`SigPlus` →
  `merge`/`mergeT`/`SigMerge`; `transpose`/`mirrorNet`/`mirrorSMC` →
  `dagger`/`daggerNet`/`daggerSMC`; `Step.run` → `Step.step`;
  `register` → `feedback`; `Poles.compose` → `pipe`; `FBody`/`TBody`/
  `SBody`/`LBody`/`PBody` → `FoldBody`/`TheseBody`/`EitherBody`/`LensBody`/
  `ProfunctorBody`; `Global` → `Constant`; `AlgShared` → `SharedTrace`;
  `discardE` → `weaken`; `distL`/`distR` → `affineDistL`/`affineDistR`;
  `(<|)` deleted. The phantom guide names `sift`, `freeze`, `enrich`, and
  `lower` never had source referents; their documentation claims are
  removed, not preserved. `melt`, in contrast, was restored with a real
  referent (see `Circuit.Net`).
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
