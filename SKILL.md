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
Circuit.Hyper    — Hyper a b, invoke, run, base/push/lift/lower.
                   Profunctor/Category/Functor/Applicative/Monad instances.
                   encode (⇨), encodeEither, runEither, flatten.
Circuit.Traced   — Trace class. (,) lazy knot, Either iteration,
                   Kleisli IO via delimited continuations (GHC primops).
Circuit.Circuit  — Circuit GADT: Lift, Compose, Knot. lower/reify,
                   push, operators (↑, ↮, ⊙, ⊲, ↓).
Circuit          — umbrella re-export. Import this for casual use;
                   import submodules directly for precision.
```

Hyper imports Circuit for the GADT constructors. Traced adds `GHC.Exts` (prompt#/control0#).

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

| symbol | name | meaning |
|--------|------|---------|
| `↬` | Hyper | type synonym: `a ↬ b = Hyper a b` |
| `↮` | Knot | postfix Loop constructor |
| `↪` | trace | close the feedback loop |
| `↩` | untrace | open the feedback loop |
| `⇨` | encode | encode Circuit into Hyper |
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
- **Category composition**: Use `(.)` from `Control.Category`, not `Prelude`.
  Import `Prelude hiding (id, (.))`.

## gotchas

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

### wrong tensor

`Circuit` is parametric in the tensor `t`. `(,)` and `Either` have
different loop semantics but identical GADT constructors. The compiler
won't stop you from using the wrong one — you'll get a puzzling type
error deep inside a `Knot` or `reify`, often mentioning mismatched
`Either` vs `(,)` constructors.

| if you wanted | but wrote | symptom |
|-------------|----------|---------|
| iteration loop | `Circuit (->) (,)` | `Left`/`Right` not in scope inside Knot body |
| lazy knot | `Circuit (->) Either` | lazy knot needs pair pattern `(a, b)`, got `Either` |

The doctest convention: pin the tensor explicitly with a type annotation.
`:: Circuit (->) (,) Int Int` or `:: Circuit (->) Either Int Int`.
The annotation also resolves the overlapping `Trace (->)` instances.

### either blindness

`Trace (->) Either` uses `Left` = feedback (continue), `Right` = exit.
User-facing code often uses the opposite convention — `Left` = result
(done), `Right` = continue (next state). See `examples/while.md`'s
`Step s r` type and the `swapRL` bridge.

When a Knot body behaves strangely — exiting immediately when it should
loop, or looping forever when it should exit — check which branch you're
returning. The convention is fixed by the class, not configurable.

The convention is also visible in the `encodeEither` / `runEither`
combinators and the `Control0` wrapper in `Circuit.Traced`.

## example authoring

New example cards go in `~/haskell/circuits/examples/`.

### structure

A card is a mini-readme: what this is, usage, the guts of what you want to
showcase, a few more examples. Top-to-bottom verifiable in a repl.

```markdown
# card-name ⟜ one-line summary

Prose introduction — what this demonstrates and why.

## first section

Fenced Haskell block with imports and definitions.

```haskell
import Circuit.Channel
...

## second section

More code. Use `$setup` blocks for shared state if needed.
```

### quality

- **Repl-verifiable.** Paste code blocks into `cabal repl` and they work.
- **Pleasant to read.** Not a wall of code. Break up large blocks from the
  testing phase into narrative sections.
- **Pleasant to copy/paste.** The reader should want to grab a block and play.
- **Not too long.** Can be as short as ~12 lines. If it's sprawling, split it.
- **Not too polished.** A few rough edges encourage participation. The card
  isn't a publication — it's a living artifact that evolves.

### r&d stretch

Cards beyond pure examples — looser, sketchier, more about a path of discovery
or intention than a finished demonstration. Some are easter eggs: a card that
makes you think "a circuit is isomorphic to pipes that easily?"

### validation

Cards are NOT compiled by `cabal build` — they're validated by pasting
code blocks into `cabal repl` (see gotcha above). Doctests in comments
serve as paste-and-verify assertions. For cards needing extra deps, use
`cabal repl -b <dep>` as declared at the top of the card.

