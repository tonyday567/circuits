<p align="center"><strong>⟴ circuits</strong></p>

A small Haskell library that makes feedback first-class. Two constructors — a plain arrow, and a knot — plus composition that fuses as you build. The rest falls out.

It's off the beaten track but absolutely core Haskell. A paean to some underappreciated infrastructure, built by an aging coder with perhaps too much time on his hands.

## what can it do?

Count the lines in a file. Every step is explicit — open, loop, close — and the handle is a visible wire, not a closure:

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

Two constructors. `Arr` wraps a plain arrow. `Knot` ties a feedback loop through the tensor. Composition (written `>>>`) is not a constructor — it *fuses*: `pipeline` above is a single `Knot` by the time you've typed it. Every circuit is always in normal form — at most one knot, at the top, over one base arrow — because the trace axioms are performed by the `Category` instance, not promised by documentation.

In `Kleisli IO`, the loop above runs in **constant stack** via GHC's delimited-continuation primops (`prompt#`/`control0#`) — the file can be as long as it likes.

## two flavours of feedback

The magic is in the tensor — the first type argument:

| tensor | feedback | behaviour |
|--------|----------|-----------|
| `Either` | `Left` = continue, `Right` = exit | loops that terminate |
| `(,)` | lazy self-reference | streams, sharing, coinduction |

Same `Knot` constructor. Different tensor, different universe. The library treats both uniformly — the axioms that make feedback well-behaved hold for either choice.

```haskell
-- Lazy streaming with (,):
powers = Knot (\(ns, ()) -> (1 : map (*2) ns, take 5 ns))
run powers ()  -- [1,2,4,8,16]

-- Iteration with Either:
step n = if n < 5 then Left (n + 1) else Right n
trace (either step step) 0  -- 5
```

## the tower

Each layer of the library is a free construction over the one below, and one class captures them all:

```haskell
class FreeLayer f where
  type Lawful f arr' :: Constraint
  unit         :: Category arr => arr :~> f arr
  rightAdjunct :: Lawful f arr' => (arr :~> arr') -> (f arr :~> arr')

-- rightAdjunct h . unit = h       (β)
-- rightAdjunct unit    = id       (η)
```

`Free` adds composition, `Trace` adds feedback, `Net` adds wiring. Every interpreter in the library is `rightAdjunct` at some layer; `realise = rightAdjunct id` recovers `runFree`, `run`, and `weave`. For `Trace`, the η law holds *definitionally* — check it by `case`, not by doctest. Under the hood this is the free traced monoidal category over your base arrow, with the trace axioms performed by construction.

## what's new in 0.2

**Trace collapsed to normal form.** Two constructors, laws in the instances, one call to the base arrow's `trace` per circuit — in `run`, at the very end. There is no interpreter with a special case, because there is nothing left to normalize.

**Net** keeps the wiring inspectable where `Trace` fuses it: two monoidal rows (`Par`, `Swap`) and four bimonoid rows (`Copy`, `Discard`, `Plus`, `Zero`), with feedback whose body is itself a `Net`. Because every wiring row is self-dual over a `Dagger` base, running a circuit backwards is a constructor swap — `Copy ↔ Plus`, `Discard ↔ Zero` — not a program transformation. This is the piece that will eventually power circuits-ad's one-line backpropagation reveal. For now it's here to play with.

## install

Add `circuits` to your `build-depends`. GHC 9.10+ (tested with 9.14) and MicroHs. One dependency beyond base: `profunctors`.

## read more

The examples directory has walkthroughs pitched at wherever you're coming from: parsers, effects, state, optics, relations, pipes, resource handling. The `other/` directory is the narrative arc — seven chapters from "marks and stacks" through free-plus-knot.

For the word-count pipeline with stopwatch/interval metering, see the [circuits-meter](https://github.com/tonyday567/circuits-meter) readme.

If you want to see what circuits looks like when compiled to a single combinator and rendered as a mandala: **[Tea-Leaf Fingerprints](https://tonyday567.github.io/posts/fingerprints/)**.

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
