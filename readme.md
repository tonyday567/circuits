<p align="center"><strong>⟴ circuits</strong></p>

A small Haskell library for wiring functions together. Three pieces — lift a function, compose two circuits, tie a feedback loop — and the rest falls out.

It's off the beaten track but absolutely core Haskell. A paean to some underappreciated infrastructure, built by an aging coder with perhaps too much time on his hands.

## what can it do?

Count the lines in a file. Every step is explicit — open, loop, close — and the handle is a visible wire, not a closure:

```haskell
import Circuit
import Control.Arrow (Kleisli(..), runKleisli)
import Control.Category ((>>>))
import Data.Bool (bool)
import System.IO (Handle, IOMode(ReadMode), hClose, hGetLine, hIsEOF, openFile)

openf = Lift (Kleisli (\fp -> openFile fp ReadMode))
       -- Trace (Kleisli IO) t FilePath Handle

countLines = Trace (Kleisli step)
  where
    step (Left (h, n)) = hIsEOF h >>= bool
      (hGetLine h >> pure (Left (h, n + 1)))
      (pure (Right (h, n)))
    step (Right h) = pure (Left (h, 0))
       -- Trace (Kleisli IO) Either Handle (Handle, Int)

pipeline = openf >>> countLines >>> Lift (Kleisli (\(h, n) -> hClose h >> pure n))
         -- Trace (Kleisli IO) Either FilePath Int

-- paste into ghci:  runKleisli (realise pipeline) "readme.md"
```

Three constructors. `Lift` wraps a plain function. `Compose` (written `>>>`) sequences them. `Trace` ties feedback — `Left` continues the loop, `Right` exits.

## two flavours of feedback

The magic is in the second type argument — the **tensor**:

| tensor | feedback | behaviour |
|--------|----------|-----------|
| `Either` | `Left` = continue, `Right` = exit | loops that terminate |
| `(,)` | lazy self-reference | streams, sharing, coinduction |

Same `Trace` constructor. Different tensor, different universe. The library treats both uniformly — the axioms that make feedback well-behaved hold for either choice.

```haskell
-- Lazy streaming with (,):
powers = Trace (Lift (\(ns, ()) -> (1 : map (*2) ns, take 5 ns)))
realise powers ()  -- [1,2,4,8,16]

-- Iteration with Either:
step n = if n < 5 then Left (n + 1) else Right n
trace (either step step) 0  -- 5
```

## what's new in 0.2

**Net** adds four structural rows: parallel composition, copy, discard, addition, and zero. Where `Trace` dissolved these into opaque `Lift` calls, `Net` keeps them inspectable — wiring you can read backwards. The contravariant channel is what makes `transpose` (running a computation in reverse) structural rather than hand-rolled.

This is the piece that will eventually power circuits-ad's one-line backpropagation reveal. For now it's here to play with.

## install

```bash
cabal build circuits
```

Compiles on GHC 9.10+ and MicroHs. One dependency beyond base: `profunctors`.

## read more

The examples directory has walkthroughs: state management, parsers, streaming, resource handling, the word-count pipeline with metering. The `other/` directory is the narrative arc — six chapters from "marks and stacks" through to the Mendler identity and the triangle proof.

If you want to see what circuits looks like when compiled to a single combinator and rendered as a mandala: **[Tea-Leaf Fingerprints](https://tonyday567.github.io/posts/fingerprints/)**.

## companion libraries

| library | what it adds |
|---------|-------------|
| [circuits-parser](https://github.com/tonyday567/circuits-parser) | parsing as a circuit |
| [circuits-io](https://github.com/tonyday567/circuits-io) | sockets, queues, servers |
| [circuits-meter](https://github.com/tonyday567/circuits-meter) | one-line performance metering |
| [circuits-ad](https://github.com/tonyday567/circuits-ad) | backpropagation as transpose |

## thanks

Built on [Launchbury, Krstic & Sauerwein (2013)](https://doi.org/10.4204/eptcs.129.9) and [Kidney & Wu (2026)](https://doi.org/10.1145/3776649). The `Hyper` type is theirs; the GADT that makes it inspectable is ours.

LLMs and agents helped with category theory, coding, refactoring, and documentation.

<br>

[![Hackage](https://img.shields.io/hackage/v/circuits.svg)](https://hackage.haskell.org/package/circuits)
[![build](https://github.com/tonyday567/circuits/actions/workflows/haskell-ci.yml/badge.svg)](https://github.com/tonyday567/circuits/actions/workflows/haskell-ci.yml)
