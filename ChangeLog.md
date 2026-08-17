# Revision history for circuits

## 0.3.0.0 — unreleased

Linear-logic refactor: multiplicative/additive/exponential connectives, the
knot-body category, polynomial interfaces, and close certification.

*SepChu (separated-extensional subcategory)*

- `OChu` object constraints now require `ChuSeparated` and `ChuExtensional`.
  `SepChu` is a synonym for this reading.
- Object-level negation `ChuONeg`, double-negation maps `dnUnitChu` /
  `dnCounitChu`.
- Associator `assocChu` / `assocChuInv` and slide `slideChu`, with a
  `Channel` instance for `ChuOTensor`. Pentagon checked on `ChuTwo`.

*Lolli (internal hom)*

- `Lolli t arr` with associated `LolliT`, methods `lolli` / `eval` /
  `curry` / `uncurry`. Instances for `(->)` (function space) and `OChu`
  (`ChuOLolli` = `A⊥ ⅋ B`). Curry/uncurry inverse and shape `(2,4)` vs
  compact `(4,2)` checked on `ChuTwo`.

*Exponentials*

- `Exponential t arr` with `Bang` / `WhyNot`, `copyE` / `discardE` /
  `derelict` / `introduce`. Cartesian collapse `!A ≅ A`. Chu construction
  `!A = (A⁺, A⁺ → r, eval)` and `?A = (!A⊥)⊥`. Oracles on `ChuTwo`:
  comonoid laws, I-point bijection, `Hom(I,?A)` cardinality, introduce
  injective on I-points, and a falsifier that pointwise `?`-merge is not
  a tensor morphism.
- ⅋-monoid on `?A`: `mergeWhyNotParChu` (`?A ⅋ ?A → ?A`),
  `zeroWhyNotParChu` (`⊥ → ?A`), par unitors, associator, and `swapParChu`.
  Oracles on `?ChuTwo`: morphism laws, left/right unit, commutativity,
  associator inverse, associativity.
- Composite `ChuObj` constructors (`tensorChuObj`, `parChuObj`,
  `bangChuObj`, additives, unitors) leave unused carriers as `error`.
  Pairing is the payload; `chuPos` / `chuNeg` of a composite are bottom.

*Thread (knot-body category)*

- New module `Circuit.Thread` introduces `Thread t arr s a b`, the category
  `arr (t s a) (t s b)` that `Loop.Knot` wraps before tracing.
- `SArr s` is its cartesian instance (`Thread (,) (->) s`).
- `Circuit.Poly.SystemT` is now parameterised by tensor and base arrow:
  `SystemT t arr s p = Thread t arr s (Dir p) (Pos p)`.
- Renamed in `Circuit.Ends`: `Body` → `Thread`, `SomeBody` → `SomeThread`,
  `processToBody` → `processToThread`, `bodyToLoop` → `threadToLoop`,
  `bodyToSArr` → `threadToSArr`, `sArrToBody` → `sArrToThread`.

*Machine pointing*

- `Circuit.Process.Machine` is now a pointed coalgebra: it stores an initial
  state @s@, an observation @arr s (Pos p)@, and a step @System arr s p@.
- Removed the old `arr (Dir p) s` injector.
- Replaced `processToMachine` with `mooreMachine` for building a pointed
  monomial machine from a seed/step/extract triple.
- `machineToProcess` now interprets a pointed machine back into a
  first-input-seeded `Process`.
- `machineToEnds` no longer wraps the state in `Maybe`.

*Multiplicative disjunction and scheduling*

- `Circuit.Tensor.Shared` with `sharedBy` / `sharedKnotBy` implements the ⅋
  connective over a shared state channel.
- `Bias` / `Fire` / `Schedule` replace the old `LR`/`RL` schedule wording;
  `L` and `R` now emit partial `These` products and discard the gated body's
  input.
- `superpose` fuses two `Knot`s into one when the feedback tensor matches.

*Free syntax*

- `Circuit.Algebra.SigShared` gives the ⅋ connective in the à-la-carte
  signature.
- `Circuit.Algebra.SigMediate` gives the ? connective, with `Mediable` for
  direct evaluation.

*Exponential slice and linearity*

- `Circuit.Mediate` adds `LinearResidual`, `FlushableResidual`,
  `LinearityViolation`, `closeCertified`, and `closeCertifiedWith` for
  drain-vs-violation close semantics. Later in the cycle this was refactored:
  state `s` is primary, `medOwed :: s -> Bool` is the per-mediator debt
  predicate, and `medDraw :: s -> s -> Maybe Int` is the per-mediator
  overdraw check. `LinearResidual` and `Debt` became convenience sources for
  `medOwed` and `medDraw` respectively; `closeCertifiedWith` uses
  `not . medOwed m` as its empty test so strict and flush paths agree.
- `Circuit.Boundary.Linear` / `IsLinear` / `NotLinear` are compile-time marks
  for lossless payloads.

*Negation and dualising object*

- `Circuit.Ends.HasDual bot arr` parameterises ends by a dualising object;
  `()` and `Bool` instances live alongside the original interaction pairing.
- `copycat @Bool` is documented as the constant `False` strategy, not identity.

*Trace honesty*

- `Circuit.Loop` documents the Central Sliding side-condition
  (Benton–Hyland Def 3.2): the free traced monoidal normal form is sound over
  a premonoidal base only when structural maps are central.
- New axioma oracles witness centrality and Kleisli-IO sliding failure.

*Removed / merged*

- `Circuit.Ends.State` is merged into `Circuit.Ends`; stale
  `Circuit.Ends.State.*` references are updated.

### Kernel tidy

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
