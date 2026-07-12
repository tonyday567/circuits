<p align="center"><strong>⟴ circuits</strong></p>

A small Haskell library that makes feedback first-class. Two constructors — a plain arrow (`Arr`) and a feedback loop (`Knot`) — plus composition that fuses as you build. The rest falls out.

It's off the beaten track but absolutely core Haskell: traced monoidal categories, hyperfunctions, and wiring diagrams, packaged so you can paste examples into GHCi.

## what is it?

`Trace t arr a b` is the free traced monoidal category over a base arrow `arr`, with feedback tensor `t`. In plain English: a circuit is either a base arrow or a feedback loop, and composing circuits already applies the trace axioms, so every value is in normal form (at most one `Knot`, at the top).

```haskell
import Circuit
import qualified Circuit.Trace as T
import Control.Arrow (Kleisli (..))
import Control.Category ((>>>))
import Data.Bool (bool)
import System.IO (IOMode (ReadMode), hClose, hGetLine, hIsEOF, openFile)

openf :: T.Trace Either (Kleisli IO) FilePath Handle
openf = T.Arr (Kleisli (\fp -> openFile fp ReadMode))

countLines :: T.Trace Either (Kleisli IO) Handle (Handle, Int)
countLines = T.Knot (Kleisli step)
  where
    step (Left (h, n)) = hIsEOF h >>= bool
      (hGetLine h >> pure (Left (h, n + 1)))
      (pure (Right (h, n)))
    step (Right h) = pure (Left (h, 0))

pipeline :: T.Trace Either (Kleisli IO) FilePath Int
pipeline = openf >>> countLines >>> T.Arr (Kleisli (\(h, n) -> hClose h >> pure n))

-- paste into ghci:  runKleisli (run pipeline) "readme.md"
```

The handle is a visible wire, not a closure. In `Kleisli IO`, the `Either` loop runs in constant stack via GHC's delimited-continuation primops.

## two tensors

The feedback tensor is the first type argument:

| tensor | feedback | behaviour |
|--------|----------|-----------|
| `Either` | `Left` = continue, `Right` = exit | loops that terminate |
| `(,)` | lazy self-reference | streams, sharing, coinduction |

Same `Knot` constructor. Different tensor, different universe.

```haskell
import Circuit
import qualified Circuit.Trace as T

-- Lazy streaming with (,):
powers :: T.Trace (,) (->) () [Integer]
powers = T.Knot (\(ns, ()) -> (1 : map (*2) ns, take 5 ns))
run powers ()  -- [1,2,4,8,16]

-- Iteration with Either:
step :: Int -> Either Int Int
step n = if n < 5 then Left (n + 1) else Right n

countToFive :: T.Trace Either (->) Int Int
countToFive = T.Arr (either step step)
run countToFive 0  -- 5
```

## the tower

The library layers free constructions over a base arrow:

- `Free` — the free category (lift and compose).
- `Trace t` — `Free` plus feedback (`Knot`). Every value is already in normal form; the `Category` instance performs the sliding axiom.
- `Net t` — `Trace` plus inspectable wiring: parallel composition, copy, discard, add, zero. Transposition over a `Dagger` base swaps wiring rows.
- `Hyper` — the final, coinductive encoding. Convert with `encode` / `observe`.

Each layer is a `Layer` in the free-forgetful adjunction; `run` is the canonical fold.

## what's new in 0.2

Trace collapsed to normal form: two constructors, laws in the instances, one call to the base arrow's `trace` per circuit. Net keeps wiring inspectable for metering, transposition, and (eventually) `circuits-ad`.

## install

Add `circuits` to your `build-depends`. GHC 9.10+ (tested with 9.14) and MicroHs. One dependency beyond base: `profunctors`.

## examples

Every file in `examples/` is a card: a short, paste-into-GHCi walkthrough with YAML front matter (`name`, `description`, `tags`).

### structural choice

`examples/` is not a secondary dump for outdated material — it is the *development surface* of the library.

- **Stable cards** document API that is exported and supported.
- **Experimental cards** grow ideas that are not yet in the API. They are leads for future work, not maintenance contracts.
- When an experimental card matures, it gets promoted into `src/` and the public API. Until then it lives in `examples/` where it can be read, copied, and improved without breaking anyone.

This is gradual API design: develop in the open, promote only what is fully spec'd, and keep dead ends visible but clearly marked. If you want to explore an extension, contribute a card.

### the cards

| category | cards | what they cover |
|---|---|---|
| **core** | `setup.md`, `circuit.md`, `traced.md`, `while.md`, `reader-monad.md` | imports, the `Trace` GADT, the `Traced` class, loops, monadic escape hatches |
| **hyper** | `hyper.md`, `hyper-chain.md`, `encode-either.md`, `lift-trace-commute.md` | the final `Hyper` encoding and the lemmas that connect it to `Trace` |
| **narrative** | `marks-and-stacks.md`, `knot-and-fix.md`, `hyper-buries-the-knot.md`, `tensors.md` | the story arc: from hyperfunctions to traced categories and back |
| **state** | `state.md`, `ambient.md`, `debug-trace.md` | visible, ambient, and hidden state patterns |
| **io** | `resource-io.md` | resource lifecycles as Either-trace loops |
| **advanced** | `proarrow.md`, `proequip.md`, `tambara.md`, `pca.md` | equipment, free Tambara → optics, PCA as dagger + `Optic (,)` residual (experimental) |

For the word-count pipeline with stopwatch/interval metering, see the [circuits-meter](https://github.com/tonyday567/circuits-meter) readme.

## companion libraries

| library | what it adds |
|---------|-------------|
| [circuits-parser](https://github.com/tonyday567/circuits-parser) | parsing as a circuit |
| [circuits-io](https://github.com/tonyday567/circuits-io) | sockets, queues, servers |
| [circuits-meter](https://github.com/tonyday567/circuits-meter) | one-line performance metering |
| [circuits-ad](https://github.com/tonyday567/circuits-ad) | backpropagation as transpose |

## thanks

Built on [Launchbury, Krstic & Sauerwein (2013)](https://doi.org/10.4204/eptcs.129.9) and [Kidney & Wu (2026)](https://doi.org/10.1145/3776649). The `Hyper` type is theirs; the normal form that makes it inspectable is ours.

LLMs and agents helped with category theory, coding, refactoring, and documentation.

<br>

[![Hackage](https://img.shields.io/hackage/v/circuits.svg)](https://hackage.haskell.org/package/circuits)
[![build](https://github.com/tonyday567/circuits/actions/workflows/haskell-ci.yml/badge.svg)](https://github.com/tonyday567/circuits/actions/workflows/haskell-ci.yml)
