---
name: circuits
description: Free traced monoidal categories. Circuit GADT, Hyper (final encoding), Trace, and Channel (compact closed on Hyper). For reading, building, extending, and debugging.
---

# circuits — agent field guide

A free traced monoidal category over any base arrow. Two representations:
Circuit (initial, inspectable) and Hyper (final, coinductive). Plus
compact closed structure on Hyper for bidirectional communication.

Start here: `other/01-stack-language.md` (5-minute orientation), then
the module haddocks top-to-bottom.

## module map

Dependency order — read in this sequence:

```
Circuit.Hyper    — standalone. Hyper a b, invoke, run, base/push/lift/lower.
                   Profunctor/Category/Functor/Applicative/Monad instances.
Circuit.Traced   — Trace class. (,) lazy knot, Either iteration,
                   Kleisli IO via delimited continuations (GHC primops).
Circuit.Circuit  — Circuit GADT: Lift, Compose, Knot. lower/reify,
                   toHyper (flattening), toHyperE (structure-preserving Either).
Circuit.Channel  — Producer/Consumer/Channel type aliases over Hyper.
                   unit/glue (compact closed), yield/accept, prod/cons.
Circuit          — umbrella re-export. Import this for casual use;
                   import submodules directly for precision.
```

Hyper has zero circuit deps. Traced adds `GHC.Exts` (prompt#/control0#).
Circuit imports both. Channel imports Hyper only.

## build and test

```bash
# Build
cd ~/haskell/circuits && cabal build

# All doctests
cabal-docspec

# Single module doctests
cabal-docspec -m Circuit.Hyper

# Test an example card compiles
cabal repl -b circuits
# then :load examples/channel-basics.md
```

Example cards are markdown with fenced Haskell blocks. They are NOT
compiled by `cabal build` — they're validated via `cabal-docspec` or
manual `cabal repl`. Add new cards to the `◊` section of the loom
(`~/mg/loom/circuits.md`).

## symbols

Non-negotiable. The old names will not compile.

| symbol | name | meaning |
|--------|------|---------|
| `↬` | Hyper | type synonym: `a ↬ b = Hyper a b` |
| `↮` | Knot | postfix Loop constructor |
| `↪` | trace | close the feedback loop |
| `↩` | untrace | open the feedback loop |
| `⇸` | invoke | apply Hyper to continuation |
| `⊲` | push | push function onto Circuit/Hyper |
| `⥁` | run | close Hyper's self-referential loop |
| `○` | base | constant continuation (postfix) |
| `↑` | lift | embed function into Hyper (postfix) |
| `↓` | lower | extract function from Circuit/Hyper (postfix) |

`↬` is the only symbol used at the type level. All others are value-level.

## conventions

- **Language**: GHC2024, extensions declared per module.
- **Trace direction**: `Left` = feedback (continue), `Right` = exit.
  The `Trace (->) Either` instance iterates until `Right`. The `Trace (->) (,)`
  instance ties a lazy knot.
- **Knot, not Loop**: The GADT constructor is `Knot`. The symbol `↮` is its
  postfix form. `Loop` does not exist in the current API.
- **Channel names**: `yield` not `doneP`. `accept` not `doneC`. `glue` not
  `counit` or `withQ`. `prod`/`cons` unchanged from Kidney & Wu.
- **Category composition**: Use `(.)` from `Control.Category`, not `Prelude`.
  Import `Prelude hiding (id, (.))`.
- **Profunctor dep**: `profunctors` package is a dependency for the `Profunctor`
  instance on `Hyper`. Not used elsewhere in the library.

## gotchas

### toHyper flattens Knots

```haskell
toHyper (Knot f) = Hyper.lift (trace f)  -- applies trace, wraps result
toHyperE f       -- preserves Either-loop structure in Hyper
```

Use `toHyperE` + `runEither` when you need the feedback structure preserved.
Use `toHyper` when you want the flattened function.

### Channel accumulator types must match

```haskell
glue :: Consumer m a -> Producer m a -> a
```

Both sides share message type `m` and accumulator type `a`. The producer's
`yield` and consumer's `accept` must agree on `a`.

### ByteString IsString trap

`Data.ByteString.Char8` truncates multi-byte UTF-8 (codepoint mod 256).
Use `Text` with `decodeUtf8` at boundaries. The parser module uses
`Uncons ByteString Char` — verify the ByteString is ASCII or Latin-1.

### Category Hyper uses Control.Category

```haskell
import Control.Category ((.), id)
import Prelude hiding (id, (.))
```

Forgetting this gives confusing type errors about `Hyper` not being a
`Category` — it is, just not `Prelude`'s.

### prompt/control0 are internal

`newPromptTag`, `prompt`, `control0`, `PromptTag` are NOT exported from
`Circuit.Traced`. They're GHC primops used internally by the
`Trace (Kleisli IO) Either` instance. The user-facing API is `trace`/`↪`.

### .md cards cannot be loaded directly in cabal repl

GHCi only recognizes `.hs` and `.lhs` files. `.md` cards are narrative
documents with fenced code blocks — not literate Haskell.

**To verify code blocks in an .md card:**

Extract the fenced blocks, wrap in a module, compile:

```python
import re
blocks = re.findall(r'```haskell\n(.*?)```', content, re.DOTALL)
code = "module Test where\nimport Circuit.Hyper ...\n\n"
for b in blocks:
    # strip imports/LANGUAGE (already at top)
    code += '\n'.join([l for l in b.split('\n')
              if not l.startswith('import ') and not l.startswith('{-#')])
    code += '\n\n'
# write to /tmp/test.hs, then: cabal repl
```

**For the user:** open `cabal repl`, paste each fenced block in order.
Multiline blocks work when pasted directly into an interactive GHCi
session. Use `:{` / `:}` if pasting over a pipe/heredoc.

**Doctests in markdown:** the technology isn't mature. `cabal-docspec`
only targets `.hs` library modules. `doctest` + `markdown-unlit` can
extract but fails because prose text leaks into the compiler. For now,
doctests in .md cards serve as paste-and-verify assertions for repl
sessions — not automated tests.

### extra dependencies for example cards

Some cards require packages not in circuits' dependency tree. The
card declares this at the top. Start repl with `-b`:

```bash
cabal repl -b these    # for coroutine-hyper.md
cabal repl -b yaya     # for yaya.md
```

The dependency lives in the command, not in circuits.cabal.

## example authoring

New example cards go in `~/haskell/circuits/examples/`. Pattern:

```markdown
# card-name ⟜ one-line summary

Prose introduction — what this demonstrates.

## first section

Fenced Haskell block with imports and definitions.

```haskell
import Circuit.Channel
...

## second section

More code. Use `$setup` blocks for shared state if needed.
```

Reference cards to steal from:
- `channel-basics.md` — the pattern: prose, fenced blocks, doctest-style outputs
- `stable-marriage.md` — longer form with multiple code sections
- `repl-pure.md` — Lift, Knot, Compose all in one card
- `two-loops.md` — includes a "composition trap" section showing what NOT to do

Cards are NOT compiled by `cabal build` — they're validated by pasting
code blocks into `cabal repl` (see gotcha above). Doctests in comments
serve as paste-and-verify assertions. For cards needing extra deps, use
`cabal repl -b <dep>` as declared at the top of the card.

## downstream

### circuits-parser (`~/haskell/circuits-parser/`)

Parser combinators over `Circuit (->) Either`. `Uncons` typeclass decomposes
streams. Depends on circuits, harpie, clock, deepseq.

**Harpie dep is suspect.** `Circuit.Parser.Token` imports `Harpie.Array`
for vocabulary storage. This pulls in a large dependency for an array type.
Consider replacing with `Data.Array` or `Data.Vector`.

**Consumer repos on parser-fix branches:**
markup-parse, huihua, mtok, dotparse, web-rep, hcount. These migrated from
flatparse/mpar/regex-applicative to circuits-parser. Not yet merged to main.

### circuits-perf (`~/haskell/circuits-perf/`)

Bare clock primitives: `nanos`, `once`, `times`, `warmup`. Currently
standalone — no circuits dep. Should depend on circuits for the
measurement-as-plugin pattern (see `examples/perf.md`).

### circuits-io (`~/haskell/circuits-io/`)

IO combinators on Circuit.Channel. Five stub modules (File, Socket, Server,
Time, Async). Fill from box library residual — the old `box` library's
Emitter/Committer map onto Channel's Producer/Consumer.

## reference files

| file | what |
|------|------|
| `other/01-stack-language.md` | entry point, five marks, six axioms |
| `other/03-circuit.md` | free object, universal property |
| `other/04-hyper.md` | final encoding, Kan characterization |
| `other/circuit-categorical.md` | categorical shopping list (partial) |
| `other/symbols.md` | symbol dictionary |
| `examples/channel-basics.md` | idiomatic Channel usage |
| `examples/stable-marriage.md` | concurrent coroutines |
| `~/mg/loom/circuits.md` | active workspace, task tracking |
| `~/haskell/circuits-io/examples/` | box prototypes (Emitter/Committer) |
