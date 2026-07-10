<p align="center"><strong>⟴ circuits</strong></p>

A small Haskell library that makes feedback first-class. Two constructors — a plain arrow (`Arr`) and a feedback loop (`Knot`) — plus composition that fuses as you build. The rest falls out.

It's off the beaten track but absolutely core Haskell: traced monoidal categories, hyperfunctions, and wiring diagrams, packaged so you can paste examples into GHCi.

## what is it?

`Trace t arr a b` is the free traced monoidal category over a base arrow `arr`, with feedback tensor `t`. In plain English: a circuit is either a base arrow or a feedback loop, and composing circuits already applies the trace axioms, so every value is in normal form (at most one `Knot`, at the top).

```haskell
import Circuit
import Control.Arrow (Kleisli (..))
import Control.Category ((>>>))
import Data.Bool (bool)
import System.IO (IOMode (ReadMode), hClose, hGetLine, hIsEOF, openFile)

openf = Arr (Kleisli (\fp -> openFile fp ReadMode))
     -- Trace Either (Kleisli IO) FilePath Handle

countLines = Knot (Kleisli step)
  where
    step (Left (h, n)) = hIsEOF h >>= bool
      (hGetLine h >> pure (Left (h, n + 1)))
      (pure (Right (h, n)))
    step (Right h) = pure (Left (h, 0))
     -- Trace Either (Kleisli IO) Handle (Handle, Int)

pipeline = openf >>> countLines >>> Arr (Kleisli (\(h, n) -> hClose h >> pure n))
     -- Trace Either (Kleisli IO) FilePath Int

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
-- Lazy streaming with (,):
powers = Knot (\(ns, ()) -> (1 : map (*2) ns, take 5 ns))
run powers ()  -- [1,2,4,8,16]

-- Iteration with Either:
step n = if n < 5 then Left (n + 1) else Right n
trace (either step step) 0  -- 5
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

All example cards live in `examples/`:

- `circuits.md` — imports and a minimal file-reading pipeline.
- `circuit.md` — the `Trace` GADT and `run`.
- `traced.md` — the `Traced` class and the bracket pattern.
- `hyper.md` / `hyper-chain.md` — the final encoding and composition.
- `encode-either.md` — why `Traced Hyper Either` is not an instance.
- `lift-trace-commute.md` — the traced-functor lemma that makes `encode` work.
- `marks-and-stacks.md` / `knot-recovers-fix.md` / `hyper-buries-the-knot.md` / `holding-hands-or-taking-turns.md` — the narrative arc, now in `examples/`.
- `while.md` — `while`/`until`/`for` on `Either`.
- `resource-io.md` — acquire/loop/release with `Trace Either (Kleisli IO)`.
- `state.md` / `ambient.md` / `debug-trace.md` — visible, ambient, and hidden state.
- `reader-monad.md` — the explicit escape hatch when you need monadic `do`.
- `effects.md` — how circuits sit alongside ReaderT/Bluefin/effectful.
- `proarrow.md` / `proequip.md` — categorical bridges (advanced).
- `words.md` — word-count pipeline; the metering version lives in `circuits-meter`.

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
