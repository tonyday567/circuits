---
name: circuits
description: Free traced monoidal categories. Loop GADT (Lift/Knot normal form), Hyper (final encoding), Net (inspectable wiring), and the Layer tower. For reading, building, extending, and debugging.
---

# circuits — field guide

A free traced monoidal category over any base arrow. Two canonical
representations: `Loop` (initial, inspectable GADT) and `Hyper` (final,
coinductive). `Net` keeps wiring inspectable with monoidal and bimonoid
rows. `Circuit.Layer` unifies the folds out of each layer.

## module map

Recommended reading order for the source (core concepts first):

```
Circuit.Category    — Local 'Category' class with 'Ob' object constraints,
                      'Discrete', and composition helpers (.>), (|>), (<|).
Circuit.Channel     — Structural semantics chain: Channel, Strength,
                      Traced, plus all base instances for (->) and
                      Kleisli m (lazy knot, Either iteration, Kleisli IO
                      via delimited continuations).
Circuit.Loop        — Loop GADT (Lift, Knot) in normal form, its
                      Category/Channel/Strength/Traced instances, and the
                      Layer witness.
Circuit.Tensor      — Braided, Cartesian and Cocartesian structure over
                      the standard tensors, plus ambient / ambientBy state
                      threading and the Tensor/Action classes.
Circuit.Hyper       — Hyper a b (final encoding), invoke, runHyper, lift,
                      observe, base, push, encode, encodeEither, runEither,
                      flatten.
Circuit.Net         — Net GADT: Lift, Compose, Par, Swap, Copy, Discard,
                      Plus, Zero, Knot. enrich, melt, transpose.
Circuit.Layer       — Layer tower. unit, run, bind, lower; (:~>).
Circuit.Algebra     — Change-of-base algebras for modular circuit syntax.
Circuit.Dagger      — CopyDiscard, MergeZero, Bimonoid, Dagger, transpose.
Circuit.Ends        — Channel ends (Out, In, Ends), boxes, queues.
Circuit.Free        — Free category: Lift, Compose.
Circuit.Sym         — Free symmetric monoidal category: Lift, Compose, Par,
                      Swap.
Circuit             — Umbrella re-export. This is the recommended import
                      (`import Circuit`) for almost all use. Submodules are
                      available when you need to be very precise about scope.
Circuit.Discrete    — Discrete discharge kit: compD, assocD, assocD',
                      braidD, strengthD, traceD.
```

## diagrams

The API structure is drawn in `other/circuits-dag.md` and as standalone HTML
charts in `other/circuits-class.html` and `other/circuits-module.html`.

- **Class relationships** — `other/circuits-class.html`
- **Module view** — `other/circuits-module.html`

Solid arrows are enrichment; thick magenta dashed arrows are the `Layer`
`Law` constraints; other dashed arrows are free construction / consumption.
`Ends`, `Hyper`, and `Dagger` are omitted from the core class diagram but
appear in the module view.

## build and test

```bash
# Build
cd ~/haskell/circuits && cabal build

# Doctests (requires cabal-docspec)
cabal-docspec

# Single module doctests
cabal-docspec -m Circuit.Hyper

# Lint / format checks
hlint .
ormolu --mode check $(find src -name '*.hs')
```

CI runs `hlint`, `ormolu`, `cabal build all`, `cabal check`, and
`cabal-docspec` on GHC 9.10, 9.12, and 9.14.

## notation

Unicode symbols are used in prose and the narrative cards as mathematical
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
  The `Traced Either (->)` instance iterates until `Right`. The
  `Traced (,) (->)` instance ties a lazy knot.
- **Category composition**: Use `(.)` from `Control.Category`, not `Prelude`.
  Import `Prelude hiding (id, (.))`.
- **Use the right elimination form**:
  - `run` interprets any `Layer` value into its base category. For example,
    `run someLoop` folds a `Loop` into the underlying `arr`.
  - `bind h` folds a free construction into a different target category,
    mapping base arrows with `h :: arr :~> arr'`.
  - `encode :: Loop (,) (->) a b -> Hyper a b` is the common case of
    `bind lift`, folding functions into `Hyper`.
  - `runHyper :: Hyper a a -> a` ties the self-referential knot on `Hyper`.
  - `observe :: Hyper a b -> (a -> b)` extracts a plain function from `Hyper`.
  - `lower :: (Layer f, Category arr) => (f arr :~> arr') -> (arr :~> arr')`
    is the left direction of the hom-set isomorphism.

## gotchas

### run vs runHyper vs run on Net

`run` is overloaded by the `Layer` class. `run someLoop` folds a `Loop` into
any `Traced t arr`; `run someNet` folds a `Net` via `melt` into `Loop` and
then `run`.

`runHyper` takes a `Hyper a a`. `observe` extracts `Hyper a b -> (a -> b)`.
They are different elimination forms on different types. If an example calls
`run` on something built with `Hyper`, it needs `runHyper` or `observe` (or
`run` if the value is already `Loop (,) Hyper`).

### .md cards cannot be loaded directly in cabal repl

GHCi only recognizes `.hs` and `.lhs` files. `.md` cards are narrative
documents with fenced code blocks — not literate Haskell. Paste code blocks
directly into `cabal repl`. For multiline blocks use `:{` / `:}`.

Doctests in markdown: `cabal-docspec` only targets `.hs` library modules.
Doctests in `.md` cards serve as paste-and-verify assertions for repl
sessions — not automated tests.

### either blindness

`Traced Either (->)` uses `Left` = feedback (continue), `Right` = exit.
User-facing code often uses the opposite convention — `Left` = result
(done), `Right` = continue (next state). See `while.md` in
`circuits-examples` for an `Either` iteration type and the `swapRL` bridge.

When a `Loop` body behaves strangely — exiting immediately when it should
loop, or looping forever when it should exit — check which branch you're
returning. The convention is fixed by the class, not configurable.

### wrong tensor

`Loop` is parametric in the tensor `t`. `(,)` and `Either` have different
loop semantics but identical GADT constructors. The compiler won't stop you
from using the wrong one — you'll get a puzzling type error deep inside a
`Loop` or `run`.

| if you wanted | but wrote | symptom |
|-------------|----------|---------|
| iteration loop | `Traced (,) (->)` | `Left`/`Right` not in scope inside Loop body |
| lazy knot | `Traced Either (->)` | lazy knot needs pair pattern `(a, b)`, got `Either` |

Pin the tensor explicitly with a type annotation:
`:: Loop (,) (->) Int Int` or `:: Loop Either (->) Int Int`.
The annotation also resolves overlapping `Traced` instances for `(->)`.

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

- **circuits-parser** — `Loop Either (->)` with `These` output for
  backtracking parsers.
- **circuits-io** — `Loop (Kleisli IO) Either` with delimited continuations
  for resource-bracketed IO loops, producer/consumer channels, and the
  circuits-io frontier.
- **circuits-meter** — one-line performance metering.
- **circuits-ad** — backpropagation as transpose.
