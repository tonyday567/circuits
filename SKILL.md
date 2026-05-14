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

Cards are NOT compiled by `cabal build` — they're validated by pasting
code blocks into `cabal repl` (see gotcha above). Doctests in comments
serve as paste-and-verify assertions. For cards needing extra deps, use
`cabal repl -b <dep>` as declared at the top of the card.

