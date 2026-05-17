<p align="center"><strong>⟴ circuits</strong></p>

## Add Feedback, Keep Structure

> The free traced monoidal category is the smallest thing you can add to a
> category to get feedback. Not a library of combinators — a single GADT and
> a single coinductive type, connected by one triangle.
>
> — What we learned building it

<br>

## ⚙️ Install

```
cabal install circuits
```

GHC 9.10+, `base`, `profunctors`, `these`.

## 📡 Usage

```haskell
import Circuit.Traced (trace)

-- Fibonacci via knot-tying
>>> take 5 (trace (\(fibs, ()) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs)) () :: [Integer])
[0,1,1,2,3]

-- Iteration with Either
>>> let step n = if n < 3 then Left (n + 1) else Right n in trace (either step step) (0 :: Int)
3
```

Five operations on one type:

```
↑  lift     embed a plain arrow
↓  lower    observe hyperfunction
⊙  compose  sequential composition
⊲  push     prepend a function
⥁  run      tie the knot
```

Two tensors, two notions of time:

| Tensor  | Semantics                                    | Trace      |
|---------|----------------------------------------------|------------|
| `(,)`   | Simultaneous — lazy knot, DP tables, streams | `unsecond` |
| `Either`| Sequential — iteration, parsers, pipes       | `unright`  |

## 🧭 Pitch

circuits is a rethink of how to interact with a compiler and arrange code
pipelines — circuits — in ways that are intentional and clear.

Within the context of the Kidney–Wu hyperfunctions paper, we propose the
free traced monoidal category. `Circuit` is the initial encoding — a GADT
with visible constructors, interpreted by `reify`. `Hyper` is the final
encoding — a coinductive type where feedback dissolves into the structure
itself. The triangle `reify = lower . encode` connects them.

## 📦 Sibling libraries

**circuits-parser** — `Circuit (->) Either` with `These` output for
backtracking parsers. Fast, working, a dependency of `chart-svg`.

**circuits-io** — `Circuit (Kleisli IO) Either` with delimited
continuations: file I/O, sockets, servers, timing, async. Home of
`Circuit.Channel`'s Producer/Consumer framework and the compact closed
frontier.

**circuits-perf** — performance measurement and R&D. `perf-bench` compares
delimited continuation trace against IORef control groups. Results on Apple
Silicon M3, GHC 9.14, `-O2`:

| benchmark          | per-iteration | ratio    |
|--------------------|---------------|----------|
| clock overhead     | 125ns         | —        |
| whileM_ (IORef)    | 8ns           | baseline |
| trace-delim        | 18ns          | 2.25×    |

1000 iterations: whileM_ = 8µs, trace-delim = 18µs. The delimited
continuation overhead is ~10ns per step — a handful of instructions plus
a closure allocation.

## 📖 Read

`other/01-marks-and-stacks.md` — the full story: five marks, six axioms.
Follow the Prev/Next chain through six chapters from the GADT to the
self-dual frontier.

`examples/` — 12 cards: lazy knot-tying, parsers, pipes, Elgot iteration,
delimited continuations. Paste code blocks into `cabal repl`.

<br>

[![Hackage](https://img.shields.io/hackage/v/circuits.svg)](https://hackage.haskell.org/package/circuits)
[![build](https://github.com/tonyday567/circuits/actions/workflows/haskell-ci.yml/badge.svg)](https://github.com/tonyday567/circuits/actions/workflows/haskell-ci.yml)
