---
name: circuits
description: Free traced monoidal categories. Circuit GADT, Hyper (final encoding), Trace, and Channel (compact closed on Hyper). For reading, building, extending, and debugging.
---

# circuits — agent field guide

A free traced monoidal category over any base arrow. Two representations:
Circuit (initial, inspectable) and Hyper (final, coinductive). Plus
compact closed structure on Hyper for bidirectional communication.

Start here: `other/01-marks-and-stacks.md` (five marks, six axioms, one Fibonacci),
then follow the Prev/Next chain through the six-chapter narrative arc.

## narrative arc

Read in order. Each builds on the last.

```
01-marks-and-stacks               five marks, six axioms, the stack language
02-a-knot-needs-a-mendler          how axiom 6 forces a GADT and a load-bearing pattern match
03-hyper-buries-the-knot           final encoding where feedback dissolves into the type
04-holding-hands-or-taking-turns   (,) vs Either — simultaneous vs sequential
05-no-remorse-once-removed         Mendler case is viewl; performance story
06-follow-the-knots                parsers, pipes, IO, agents; the compact closed frontier
axioms                             equational proofs (appendix)
```

## module map

Dependency order — read source in this sequence:

```
Circuit.Hyper    — Hyper a b, invoke, run, base/push/lift/lower.
                   Profunctor/Category/Functor/Applicative/Monad instances.
                   encode (⇨), encodeEither, runEither, flatten.
Circuit.Traced   — Trace class. (,) lazy knot, Either iteration,
                   Kleisli IO via delimited continuations (GHC primops).
Circuit.Circuit  — Circuit GADT: Lift, Compose, Knot. reify, push,
                   operators (↑, ↮, ⊙, ⊲).
Circuit           — umbrella re-export. Import this for casual use;
                    import submodules directly for precision.
```

Hyper imports Circuit for the GADT constructors. Traced depends only on
`GHC.Exts` (prompt#/control0#).

## build and test

```bash
# Build
cd ~/haskell/circuits && cabal build

# All doctests
cabal-docspec

# Single module doctests
cabal-docspec -m Circuit.Hyper

# Test an example card compiles
cabal repl
# then paste code blocks from examples/*.md in order
```

Example cards are markdown with fenced Haskell blocks. They are NOT
compiled by `cabal build` — they're validated by pasting into `cabal repl`
or via `cabal-docspec`.

## symbols

| symbol | name | meaning |
|--------|------|---------|
| `↬` | Hyper | type synonym: `a ↬ b = Hyper a b` |
| `↮` | Knot | feedback loop constructor |
| `↪` | trace | close the feedback loop |
| `↩` | untrace | open the feedback loop |
| `⇨` | encode | encode Circuit into Hyper |
| `⇸` | invoke | apply Hyper to continuation |
| `⊲` | push | prepend function onto Circuit/Hyper |
| `⥁` | run | close Hyper's self-referential loop |
| `○` | base | constant continuation (ignore feedback) |
| `↑` | lift | embed function into Hyper |
| `↓` | lower | observe Hyper with constant continuation |
| `⊙` | compose | sequential composition |

`↬` is the only symbol used at the type level. All others are value-level.

## conventions

- **Language**: GHC2024, extensions declared per module.
- **Trace direction**: `Left` = feedback (continue), `Right` = exit.
  The `Trace (->) Either` instance iterates until `Right`. The `Trace (->) (,)`
  instance ties a lazy knot.
- **Category composition**: Use `(.)` from `Control.Category`, not `Prelude`.
  Import `Prelude hiding (id, (.))`.
- **Use `reify` for Circuit, `run` for Hyper**. `reify :: Circuit arr t x y -> arr x y`
  interprets a Circuit to a plain arrow. `run :: Hyper a a -> a` ties the
  self-referential knot. They are not interchangeable — calling `run` on a
  Circuit is a type error. This is the most common bug in example cards.

## gotchas

### run vs reify

`run` takes a `Hyper`; `reify` takes a `Circuit`. They are different
elimination forms on different types. If an example calls `run` on something
built with `Knot` or `Lift`, it needs `reify` (or `encode` then `run`).

### .md cards cannot be loaded directly in cabal repl

GHCi only recognizes `.hs` and `.lhs` files. `.md` cards are narrative
documents with fenced code blocks — not literate Haskell. Paste code
blocks directly into `cabal repl`. For multiline blocks use `:{` / `:}`.

Doctests in markdown: `cabal-docspec` only targets `.hs` library modules.
Doctests in `.md` cards serve as paste-and-verify assertions for repl
sessions — not automated tests.

### either blindness

`Trace (->) Either` uses `Left` = feedback (continue), `Right` = exit.
User-facing code often uses the opposite convention — `Left` = result
(done), `Right` = continue (next state). See `examples/while.md`'s
`Step s r` type and the `swapRL` bridge.

When a Knot body behaves strangely — exiting immediately when it should
loop, or looping forever when it should exit — check which branch you're
returning. The convention is fixed by the class, not configurable.

### wrong tensor

`Circuit` is parametric in the tensor `t`. `(,)` and `Either` have
different loop semantics but identical GADT constructors. The compiler
won't stop you from using the wrong one — you'll get a puzzling type
error deep inside a `Knot` or `reify`.

| if you wanted | but wrote | symptom |
|-------------|----------|---------|
| iteration loop | `Circuit (->) (,)` | `Left`/`Right` not in scope inside Knot body |
| lazy knot | `Circuit (->) Either` | lazy knot needs pair pattern `(a, b)`, got `Either` |

Pin the tensor explicitly with a type annotation:
`:: Circuit (->) (,) Int Int` or `:: Circuit (->) Either Int Int`.
The annotation also resolves overlapping `Trace (->)` instances.

### extra dependencies for example cards

Some cards require packages not in circuits' dependency tree. The
card declares this at the top. Start repl with `-b`:

```bash
cabal repl -b yaya     # for yaya.md
```

The dependency lives in the command, not in circuits.cabal.

## example authoring

New example cards go in `examples/`. A good card:

- **Repl-verifiable.** Paste code blocks into `cabal repl` and they work.
  Verify before committing — `run` where `reify` belongs is a type error.
- **Pleasant to read.** Not a wall of code. Break up large blocks with
  narrative sections.
- **Pleasant to copy/paste.** The reader should want to grab a block and play.
- **Not too long.** Can be as short as ~12 lines. If it's sprawling, split it.
- **Not too polished.** A few rough edges encourage participation.

Solid examples to learn from: `parser.md`, `while.md`, `elgot-abacus.md`,
`pipes.md`.

## sibling libraries

- **circuits-parser** — `Circuit (->) Either` with `These` output for
  backtracking parsers. Working, fast, a dependency of `chart-svg`.
- **circuits-io** — `Circuit (Kleisli IO) Either` with delimited
  continuations for resource-bracketed IO loops, producer/consumer
  channels, and the compact closed frontier.
