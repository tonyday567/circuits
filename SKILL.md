---
name: circuits
description: Free traced monoidal categories. Trace GADT (Lift/Knot normal form), Hyper (final encoding), Net (inspectable wiring), and the Layer tower. For reading, building, extending, and debugging.
---

# circuits — agent field guide

A free traced monoidal category over any base arrow. Two canonical
representations: `Trace` (initial, inspectable GADT) and `Hyper` (final,
coinductive). `Net` keeps wiring inspectable with monoidal and bimonoid
rows. `Circuit.Layer` unifies the folds out of each layer.

Start here: `other/01-marks-and-stacks.md` (five marks, six axioms, one
Fibonacci), then follow the Prev/Next chain through the narrative arc.

## narrative arc

Read in order. Each builds on the last.

```
01-marks-and-stacks               five marks, six axioms, the stack language
02-knot-and-fix                   how axiom 4 forces a GADT and a load-bearing pattern match
03-hyper-buries-the-knot          final encoding where feedback dissolves into the type
04-tensors                        (,) vs Either — simultaneous vs sequential
05-no-remorse-once-removed        Mendler case is viewl; performance story
06-some-more-knots                making stuff: parsers, pipes, loops, agents, metering
axioms                            equational proofs (appendix)
symbols                           notation table
```

## module map

Recommended reading order for the source (core concepts first):

```
Circuit.Category    — Local 'Category' class with 'Ob' object constraints,
                      'Discrete', and composition helpers.
Circuit.Trace       — Trace GADT (Lift, Knot), the Traced class, the
                      Strength superclass, channel ends, and base
                      instances: (,) lazy knot, Either iteration, Kleisli
                      IO via delimited continuations, cellIO helper.
Circuit.Monoidal    — Monoidal superclass (associator + braiding) for traced
                      categories.
Circuit.Tensor      — Braided, Cartesian and Cocartesian structure over the
                      standard tensors, plus ambient / ambientBy state
                      threading.
Circuit.Hyper       — Hyper a b (final encoding), invoke, runHyper, lift, observe,
                      base, push, encode, encodeEither, runEither, flatten.
Circuit.Net         — Net GADT: Lift, Compose, Par, Swap, Copy, Discard,
                      Plus, Zero, Knot. enrich, melt, transpose.
Circuit.Layer       — Layer tower. unit, run, bind, lower; Cat2, (:~>).
Circuit.Algebra     — change-of-base algebras for modular circuit syntax (optional).
Circuit.Dagger      — WireMonoid, Comonoid, Bimonoid, Dagger, transpose.
Circuit.Free        — Free category: Lift, Compose.
Circuit.Mon         — Free symmetric monoidal category: Lift, Compose, Par,
                      Swap.
Circuit             — umbrella re-export. This is the recommended import
                      (`import Circuit`) for almost all use. Submodules are
                      available when you need to be very precise about scope.
```

`Hyper` imports `Circuit.Trace` for the GADT constructors. `Traced` depends
only on `GHC.Exts` (prompt#/control0#) under GHC.

## build and test

```bash
# Build
cd ~/haskell/circuits && cabal build

# All doctests
cabal-docspec

# Single module doctests
cabal-docspec -m Circuit.Hyper

```

Example cards now live in the `circuits-examples` repository. They are
markdown with fenced Haskell blocks, validated by pasting into `cabal repl`.

## notation

Unicode symbols are used throughout the narrative and examples as
mathematical notation — not Haskell identifiers.  See
[other/symbols.md](other/symbols.md) for the full table, axioms, and
worked examples.

The canonical API uses lowercase names: `lift`, `observe`, `encode`,
`push`, `run`, `runHyper`, `runEither`, `trace`, `strength`, `melt`,
`enrich`, `lower`, etc.

Type-level vocabulary: `Cat2`, `(:~>)` (arrow homomorphism).

Symbols appear in two places only: the notation table (`other/symbols.md`)
and axiom blocks. Everywhere else — prose, proof steps, explanations,
type signatures, code — use names. This boundary prevents agent churn.

## conventions

- **Language**: GHC2024, extensions declared per module.
- **Trace direction**: `Left` = feedback (continue), `Right` = exit.
  The `Traced Either (->)` instance iterates until `Right`. The `Traced (,) (->)`
  instance ties a lazy knot.
- **Category composition**: Use `(.)` from `Control.Category`, not `Prelude`.
  Import `Prelude hiding (id, (.))`.
- **Use the right elimination form**:
  - `run` interprets any `Layer`: use `run @Free`, `run @(Trace t)`, or
    `run @(Net t)`. `run @(Trace t)` is polymorphic in the target arrow:
    it works for any `Traced t arr`, including `arr = (->)` and `arr = Hyper`.
  - `encode :: Trace (,) (->) a b -> Hyper a b` is not a separate
    primitive: it is `bind lift`, the `Layer (Trace (,))` fold that sends
    the base arrow `(->)` into `Hyper` via `lift :: (->) :~> Hyper`.
  - `runHyper :: Hyper a a -> a` ties the self-referential knot on `Hyper`.
  - `observe :: Hyper a b -> (a -> b)` extracts a plain function from `Hyper`.
  - `lower :: (Layer f, Category arr) => (f arr :~> arr') -> (arr :~> arr')`
    is the left direction of the hom-set isomorphism.

## gotchas

### run vs runHyper vs run @Net

`run` takes any `Layer`: `run @Free`, `run @(Trace t)`, `run @(Net t)`.
`run @(Trace (,))` folds into any `Traced (,) arr`, so it can interpret
directly into `Hyper` when the source is `Trace (,) Hyper`. `encode`
handles the common case where the source is `Trace (,) (->)` and the
target is `Hyper`; under the hood it is just `bind lift`.

`runHyper` takes a `Hyper a a`. `observe` extracts `Hyper a b -> (a -> b)`.
They are different elimination forms on different types. If an example calls
`run` on something built with `Hyper`, it needs `runHyper` or `observe`
(or `run @(Trace (,))` if the value is already `Trace (,) Hyper`).

### .md cards cannot be loaded directly in cabal repl

GHCi only recognizes `.hs` and `.lhs` files. `.md` cards are narrative
documents with fenced code blocks — not literate Haskell. Paste code
blocks directly into `cabal repl`. For multiline blocks use `:{` / `:}`.

Doctests in markdown: `cabal-docspec` only targets `.hs` library modules.
Doctests in `.md` cards serve as paste-and-verify assertions for repl
sessions — not automated tests.

### either blindness

`Traced Either (->)` uses `Left` = feedback (continue), `Right` = exit.
User-facing code often uses the opposite convention — `Left` = result
(done), `Right` = continue (next state). See `while.md` in `circuits-examples`
for an `Either` iteration type and the `swapRL` bridge.

When a `Trace` body behaves strangely — exiting immediately when it should
loop, or looping forever when it should exit — check which branch you're
returning. The convention is fixed by the class, not configurable.

### wrong tensor

`Trace` is parametric in the tensor `t`. `(,)` and `Either` have
different loop semantics but identical GADT constructors. The compiler
won't stop you from using the wrong one — you'll get a puzzling type
error deep inside a `Trace` or `run`.

| if you wanted | but wrote | symptom |
|-------------|----------|---------|
| iteration loop | `Traced (,) (->)` | `Left`/`Right` not in scope inside Trace body |
| lazy knot | `Traced Either (->)` | lazy knot needs pair pattern `(a, b)`, got `Either` |

Pin the tensor explicitly with a type annotation:
`:: Trace (,) (->) Int Int` or `:: Trace Either (->) Int Int`.
The annotation also resolves overlapping `Traced` instances for `(->)`.

### extra dependencies for example cards

Some cards require packages not in circuits' dependency tree. The
card declares this at the top. Start repl with `-b`:

```bash
cabal repl -b yaya     # for yaya.md in circuits-examples
```

The dependency lives in the command, not in circuits.cabal.

## example authoring

New example cards live in the `circuits-examples` repository. A good card:

- **Repl-verifiable.** Paste code blocks into `cabal repl` and they work.
  Verify before committing — `run` where `runHyper` or `observe` belongs is a
  type error.
- **Pleasant to read.** Not a wall of code. Break up large blocks with
  narrative sections.
- **Pleasant to copy/paste.** The reader should want to grab a block and play.
- **Not too long.** Can be as short as ~12 lines. If it's sprawling, split it.
- **Not too polished.** A few rough edges encourage participation.

Solid examples to learn from: `parser.md`, `while.md`, `pipes.md`.

## sibling libraries

- **circuits-parser** — `Trace (->) Either` with `These` output for
  backtracking parsers. Working, fast, a dependency of `chart-svg`.
- **circuits-io** — `Trace (Kleisli IO) Either` with delimited
  continuations for resource-bracketed IO loops, producer/consumer
  channels, and the circuits-io frontier.
- **circuits-meter** — one-line performance metering.
- **circuits-ad** — backpropagation as transpose.
