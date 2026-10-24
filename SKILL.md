---
name: circuits
description: Free traced monoidal categories. FreeTrace (inspectable syntax), Hyper (final encoding), Net (wiring with bimonoid), Machine (cells, bodies and Moore machines over a channel), plus Poly/Shared polynomial machinery.
---

# circuits — field guide

A free traced monoidal category over any base arrow. The library has one
common shape and three views of it:

- `Step t t' ch ch' arr i o` / `Body t t' ch ch' arr i o` — the one-tick
  morphism and its factored init/commit/emit form, threading a channel `ch`
  alongside a payload under tensors `t t'` in a base arrow `arr`. Cells,
  Moore machines, and poles are all factorisations or wrappers of this
  shape.
- `FreeTrace t arr a b` — the inspectable initial/free syntax for traced
  monoidal categories (`Lift` + `trace`).
- `Hyper` / `HyperA arr` — the final coinductive encoding over `(->)` and
  `K m`.
- `Net w arr a b` — inspectable wiring with bimonoid rows; `melt` forgets
  it into `FreeTrace`.

## module map

Recommended reading order for the source (core concepts first):

```
Circuit.Category    — Local 'Category' class, 'K' Kleisli and 'CoK'
                      co-Kleisli newtypes, local 'Comonad' class, and
                      composition/application helpers (.>), (|>), (<.).
Circuit.Traced     — Structural class ladder: Assoc, OuterSwap, Strength,
                      Trace. Instances for (->) and K m; (,), Either, These
                      tensors. Left = feedback/continue, Right = exit for
                      Either trace. Unfold lives here too: coiteration over
                      a grammar, Nu the run's output shape; the Either
                      corner is the codiagonal correspondence with trace,
                      and the partial grammars Maybe :. (,) and Maybe :.
                      Either serve the tape-driven runners.
Circuit.Tensor      — Tensor/Symmetric classes, braiding, innerSwap (derived
                      adjacent transposition), cartesian/cocartesian
                      plumbing, and superpose (fused parallel composition).
Circuit.Trace       — Free traced monoidal category syntax (FreeTrace,
                      SigTrace, Knot, Wire, Iteration).
Circuit.Net         — Free SMC with bimonoid rows (Copy/Discard/Merge/Zero);
                      hosts the symmetric-monoidal layer (SMC, SigPar,
                      SigSwap, daggerSMC); melt, daggerNet, widen.
Circuit.Syntax      — à-la-carte substrate (Syntax, (:+:), eval/evalInto) and
                      the Layer tower: Layer class, unit/run/bind; Free.
Circuit.Hyper       — Hyperfunctions: final encoding, encode, observe, runHyper.
Circuit.Bimonoid    — Copy/Discard/Merge/Zero structural rules and the free
                      dagger category (Dagger, dagger): the interlock that
                      dualises the laws (fwd copy = bwd merge).
Circuit.Linear      — Linear-logic connectives: multiplicative disjunction
                      ⅋/Bot with affineDistL/affineDistR, Lolli (⊸),
                      Exponential (!/?) with weaken.
Circuit.Shared      — Shared-medium fusion (operational ⅋) and Schedule;
                      the free syntax is SharedTrace.
Circuit.Poly        — Polynomial functor category, lenses/prisms, netlist view.
Circuit.Step       — The machine tick: Step, one arrow from the grammared
                      source to the grammared target, shared by the machine
                      lane and the traced lane; its haddock carries the
                      runner-fit conditions (Moore-discipline, productivity)
                      and a worked example run both ways.
Circuit.Machine     — Machines over a channel: Cell (seed+step; Mealy on
                      the diagonal), Body (init/commit/emit), Moore/MooreT
                      (the Const-target corner and its proven Category),
                      MooreP/MealyP (polynomial interfaces), Poles (the
                      memoryless corner) with pipe, the bundles (FoldBody,
                      TheseBody, EitherBody, LensBody, ProfunctorBody) and
                      their fuses, the Moore pattern with delay/feedback,
                      scan/fold eliminators (unfolds at the partial
                      grammars), MergeNat, and the lens dictionary
                      (bodyAsLens/lensAsBody). Re-exports Step from
                      Circuit.Step.
Circuit.Pullback    — Linear cotangent maps for reverse-mode gradients.
Circuit.Stream      — Stream algebra/coalgebra helpers.
Circuit             — Umbrella re-export. This is the recommended import
                      (`import Circuit`) for almost all use.
```

## build and test

```bash
# Build
cd ~/haskell/circuits && cabal build all

# Axioma oracles
cabal run circuits-axioma -- all

# Doctests. cabal-docspec is currently a broken install on this machine;
# the substitute is doctest under cabal exec (needs a successful build
# first — it tests the last build):
cabal exec doctest -- -XLambdaCase -XDataKinds -XTypeApplications \
  -XScopedTypeVariables -XTypeOperators -XGADTs -XTypeFamilies \
  $(ls src/Circuit/*.hs src/Circuit.hs)

# Single module doctests
cabal exec doctest -- src/Circuit/Hyper.hs

# Lint / format checks
hlint .
ormolu --mode check $(find src app -name '*.hs')
```

CI runs `hlint`, `ormolu`, `cabal build all`, `cabal check`, and the
doctest battery on GHC 9.10, 9.12, and 9.14.

## notation

Unicode symbols are used in prose and narrative cards as mathematical
notation — not Haskell identifiers. The canonical API uses lowercase names:
`lift`, `observe`, `encode`, `push`, `run`, `runHyper`, `runEither`,
`trace`, `strength`, `melt`, `merge`, `feedback`, `pipe`, etc. Every name
in this list is a live export; guide text does not keep names that lack a
source referent.

Type-level vocabulary: `(:~>)` (arrow homomorphism), `Cat2`.

Symbols appear in two places only: the notation table (`other/symbols.md`)
and axiom blocks. Everywhere else — prose, proof steps, explanations,
type signatures, code — use names. This boundary prevents churn.

## conventions

- **Language**: GHC2024.
- **Trace direction**: `Left` = feedback (continue), `Right` = exit. The
  `Trace Either (->)` instance iterates until `Right`. The
  `Trace (,) (->)` instance ties a lazy knot.
- **Category composition**: Use `(.)` from `Control.Category`, not `Prelude`.
  Import `Prelude hiding (id, (.))`.
- **Use the right elimination form**:
  - `run` interprets any `Layer` value into its base or target category. For
    example, `run someFreeTrace` folds a `FreeTrace` into the underlying
    `arr`, and `run someNet` folds a `Net` — the law is `run @Net = eval .
    melt`, melting to `FreeTrace` and evaluating there.
  - `bind h` folds a free construction into a different target category,
    mapping base arrows with `h :: arr :~> arr'`.
  - `encode :: FreeTrace (,) (->) a b -> Hyper a b` is the common case of
    `bind lift`, folding functions into `Hyper`.
  - `runHyper :: Hyper a a -> a` ties the self-referential knot on `Hyper`.
  - `observe :: Hyper a b -> (a -> b)` extracts a plain function from `Hyper`.

## gotchas

### run vs runHyper vs observe

`run` is overloaded by the `Layer` class. `run someFreeTrace` folds a
`FreeTrace` into any `Trace t arr`; `run someNet` folds a `Net` with the
same answer as `eval (melt someNet)` — `melt :: (Symmetric w arr, Trace w
arr) => Net w arr a b -> FreeTrace w arr a b` is the forgetting map and its
law is `run @Net = eval . melt`.

`runHyper` takes a `Hyper a a`. `observe` extracts `Hyper a b -> (a -> b)`.
They are different elimination forms on different types. If an example calls
`run` on something built with `Hyper`, it needs `runHyper` or `observe` (or
`run` if the value is already a `FreeTrace` containing `Hyper` arrows).

### .md cards cannot be loaded directly in cabal repl

GHCi only recognizes `.hs` and `.lhs` files. `.md` cards are narrative
documents with fenced code blocks — not literate Haskell. Paste code blocks
directly into `cabal repl`. For multiline blocks use `:{` / `:}`.

Doctests in markdown: the doctest battery only targets `.hs` library
modules. Doctests in `.md` cards serve as paste-and-verify assertions for
repl sessions — not automated tests.

### either blindness

`Trace Either (->)` uses `Left` = feedback (continue), `Right` = exit.
User-facing code often uses the opposite convention — `Left` = result
(done), `Right` = continue (next state). See `while.md` in
`circuits-examples` for an `Either` iteration type and the `swapRL` bridge.

When a `FreeTrace` body behaves strangely — exiting immediately when it
should loop, or looping forever when it should exit — check which branch
you're returning. The convention is fixed by the class, not configurable.

### pointing: two discharges

A stateful run needs an initial carrier value exactly where no input
supplies one. `Body` discharges pointing through the input (`init :: arr i
ch`); `Cell` keeps the seed explicit as the `seed` leg (`arr (Unit t) ch`).
Do not collapse the pair: input discharge agrees with an explicit seed only
when the body never reads its initial state, which is why `delay` and
`feedback` exist as explicit wiring.

### wrong tensor

`FreeTrace` is parametric in the tensor `t`. `(,)` and `Either` have
different loop semantics but identical GADT constructors. The compiler
won't stop you from using the wrong one — you'll get a puzzling type error
deep inside a `FreeTrace` or `run`.

Pin the tensor explicitly with a type annotation:
`:: FreeTrace (,) (->) Int Int` or `:: FreeTrace Either (->) Int Int`.
The annotation also resolves overlapping `Trace` instances for `(->)`.

### extra dependencies for example cards

Some cards require packages not in circuits' dependency tree. The card
declares this at the top. Start repl with `-b`:

```bash
cabal repl -b yaya     # for yaya.md in circuits-examples
```

The dependency lives in the command, not in circuits.cabal.

## example authoring

New example cards live in the `circuits-examples` repository. A good card:

- **Repl-verifiable.** Paste code blocks into `cabal repl` and they work.
  Verify before committing — `run` where `runHyper` or `observe` belongs is
  a type error.
- **Pleasant to read.** Not a wall of code. Break up large blocks with
  narrative sections.
- **Pleasant to copy/paste.** The reader should want to grab a block and play.
- **Not too long.** Can be as short as ~12 lines. If it's sprawling, split it.
- **Not too polished.** A few rough edges encourage participation.

Solid examples to learn from: `parser.md`, `while.md`, `pipes.md`.

## sibling libraries

- **circuits-rel** — finite relations, the reference semantics in two
  grades (explicit relations and GF(2) linear relations). Formerly
  `Circuit.Rel` in core; moved out with its `circuits-rel-axioma` oracle
  runner.
- **circuits-parser** — `FreeTrace Either (->)` with `These` output for
  backtracking parsers.
- **circuits-meter** — one-line performance metering.
- **circuits-diff** — backpropagation as transpose (pullbacks).
