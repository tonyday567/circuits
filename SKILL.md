---
name: circuits
description: Free traced monoidal categories. Trace (inspectable syntax), Hyper (final encoding), Net (wiring with bimonoid), Body (knot-body category), and the Layer tower, plus Process/System/Poles/Shared polynomial machinery.
---

# circuits — field guide

A free traced monoidal category over any base arrow. The library has one
common shape and three views of it:

- `Body t ch arr a b = arr (t ch a) (t ch b)` — a morphism that threads an
  ambient channel `ch` alongside a payload, under a tensor `t`, in a base
  arrow `arr`. Loops, processes, systems, and poles are all specialisations
  or wrappers of this shape.
- `Trace t arr a b` — the inspectable initial/free syntax for traced
  monoidal categories (`base` + `yank`).
- `Hyper` / `HyperA arr` — the final coinductive encoding over `(->)` and
  `K m`.
- `Net w arr a b` — inspectable wiring with bimonoid rows; `melt` forgets
  it into `Trace`.

## module map

Recommended reading order for the source (core concepts first):

```
Circuit.Category    — Local 'Category' class, 'K' Kleisli newtype, and
                      composition/application helpers (.>), (|>), (<|).
Circuit.Traced     — Structural class ladder: Assoc, Slide, Strength, Yank.
                      Instances for (->) and K m; (,), Either, These tensors.
                      Left = feedback/continue, Right = exit for Either yank.
Circuit.Tensor      — Tensor/Action classes, braiding, cartesian/cocartesian
                      plumbing, and superpose (fused parallel composition).
Circuit.Body        — The knot-body category: Body t ch arr a b.
Circuit.Trace       — Free traced monoidal category syntax (Trace, base, yank).
Circuit.SMC         — Free symmetric monoidal category over a wiring tensor.
Circuit.Net         — Free SMC with bimonoid rows (Copy/Discard/Plus/Zero);
                      melt, mirror, widen, sift.
Circuit.Layer       — Layer tower: unit, run, bind, lower; Free and freeze.
Circuit.Syntax      — Generic à-la-carte substrate: Syntax, (:+:), eval.
Circuit.Hyper       — Hyperfunctions: final encoding, encode, observe, runHyper.
Circuit.Dagger      — Dagger category, transpose, bimonoid interlock.
Circuit.Bimonoid    — Copy/Discard/Merge/Zero structural rules.
Circuit.Par         — Multiplicative disjunction ⅋, Bot, linear distributors.
Circuit.Linear      — Linear-logic connectives: Lolli, Exponential (!/?).
Circuit.Shared      — Shared-medium fusion (operational ⅋) and Schedule.
Circuit.Process     — Process base arrow (Moore machine), scan/fold, mealy,
                      delay/register, Body conversions.
Circuit.Moore       — Moore machines over polynomial interfaces.
Circuit.Poly        — Polynomial functor category, lenses/prisms, netlist view.
Circuit.Channel — Poly-indexed Moore channels.
Circuit.Poles       — Bi-polar channel ends (Out/In), boxes, copycat, race.
Circuit.Pullback    — Linear cotangent maps for reverse-mode gradients.
Circuit.FinRel      — Finite linear relations over GF(2), reference semantics.
Circuit.Stamped     — Occurrence-token values.
Circuit.Stream      — Stream algebra/coalgebra helpers.
Circuit             — Umbrella re-export. This is the recommended import
                      (`import Circuit`) for almost all use.
```

## build and test

```bash
# Build
cd ~/haskell/circuits && cabal build all

# Axioma oracles
cabal run circuits-axioma

# Doctests (requires cabal-docspec)
cabal-docspec

# Single module doctests
cabal-docspec -m Circuit.Hyper

# Lint / format checks
hlint .
ormolu --mode check $(find src app -name '*.hs')
```

CI runs `hlint`, `ormolu`, `cabal build all`, `cabal check`, and
`cabal-docspec` on GHC 9.10, 9.12, and 9.14.

## notation

Unicode symbols are used in prose and narrative cards as mathematical
notation — not Haskell identifiers. The canonical API uses lowercase names:
`lift`, `observe`, `encode`, `push`, `run`, `runHyper`, `runEither`,
`trace`, `strength`, `melt`, `enrich`, `lower`, etc.

Type-level vocabulary: `(:~>)` (arrow homomorphism), `Cat2`.

Symbols appear in two places only: the notation table (`other/symbols.md`)
and axiom blocks. Everywhere else — prose, proof steps, explanations,
type signatures, code — use names. This boundary prevents churn.

## conventions

- **Language**: GHC2024.
- **Trace direction**: `Left` = feedback (continue), `Right` = exit.
  The `Yank Either (->)` instance iterates until `Right`. The
  `Yank (,) (->)` instance ties a lazy knot.
- **Category composition**: Use `(.)` from `Control.Category`, not `Prelude`.
  Import `Prelude hiding (id, (.))`.
- **Use the right elimination form**:
  - `run` interprets any `Layer` value into its base or target category. For
    example, `run someTrace` folds a `Trace` into the underlying `arr`, and
    `run someNet` folds a `Net` via `melt` into `Trace` and then `run`.
  - `bind h` folds a free construction into a different target category,
    mapping base arrows with `h :: arr :~> arr'`.
  - `encode :: Trace (,) (->) a b -> Hyper a b` is the common case of
    `bind lift`, folding functions into `Hyper`.
  - `runHyper :: Hyper a a -> a` ties the self-referential knot on `Hyper`.
  - `observe :: Hyper a b -> (a -> b)` extracts a plain function from `Hyper`.
  - `lower :: (Layer f, Category arr) => (f arr :~> arr') -> (arr :~> arr')`
    is the left direction of the hom-set isomorphism.

## gotchas

### run vs runHyper vs observe

`run` is overloaded by the `Layer` class. `run someTrace` folds a `Trace` into
any `Yank t arr`; `run someNet` folds a `Net` via `melt` into `Trace` and
then `run`.

`runHyper` takes a `Hyper a a`. `observe` extracts `Hyper a b -> (a -> b)`.
They are different elimination forms on different types. If an example calls
`run` on something built with `Hyper`, it needs `runHyper` or `observe` (or
`run` if the value is already a `Trace` containing `Hyper` arrows).

### .md cards cannot be loaded directly in cabal repl

GHCi only recognizes `.hs` and `.lhs` files. `.md` cards are narrative
documents with fenced code blocks — not literate Haskell. Paste code blocks
directly into `cabal repl`. For multiline blocks use `:{` / `:}`.

Doctests in markdown: `cabal-docspec` only targets `.hs` library modules.
Doctests in `.md` cards serve as paste-and-verify assertions for repl
sessions — not automated tests.

### either blindness

`Yank Either (->)` uses `Left` = feedback (continue), `Right` = exit.
User-facing code often uses the opposite convention — `Left` = result
(done), `Right` = continue (next state). See `while.md` in
`circuits-examples` for an `Either` iteration type and the `swapRL` bridge.

When a `Trace` body behaves strangely — exiting immediately when it should
loop, or looping forever when it should exit — check which branch you're
returning. The convention is fixed by the class, not configurable.

### wrong tensor

`Trace` is parametric in the tensor `t`. `(,)` and `Either` have different
loop semantics but identical GADT constructors. The compiler won't stop you
from using the wrong one — you'll get a puzzling type error deep inside a
`Trace` or `run`.

Pin the tensor explicitly with a type annotation:
`:: Trace (,) (->) Int Int` or `:: Trace Either (->) Int Int`.
The annotation also resolves overlapping `Yank` instances for `(->)`.

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

- **circuits-parser** — `Trace Either (->)` with `These` output for
  backtracking parsers.
- **circuits-io** — `Trace (Kleisli IO) Either` with delimited continuations
  for resource-bracketed IO loops, producer/consumer channels, and the
  circuits-io frontier.
- **circuits-meter** — one-line performance metering.
- **circuits-ad** — backpropagation as transpose.

