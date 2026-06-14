<p align="center"><strong>⟴ circuits</strong></p>

## first-class feedback

circuits builds off of a simple premise; create a datatype, Circuit, with three tags or constructors:

**Lift** ⟜ embeds a plain function.

**Compose** ⟜ composes two lifted functions

**Knot** ⟜ ties a feedback loop where the body is itself a Circuit, making loop wiring inspectable before closing.

In every case, the tags delay a final closing of ordinary functions: Lift delays function application, Compose function composition, and Knot function feedback. A Circuit can then be rearranged, measured, substituted, annotated — or left open to further transformation before it runs.

This is the sense in which the library treats feedback as first-class.

semantics
##

If you interpret these three tags carefully, Circuit comes with a very nice set of axioms that formally are captured by the notion of a traced category.

The semantics of these constructors can be seen in reify:

``` haskell
↘ (↑ f)       =  f                   — a lifted function just runs
↘ (↮ k)       =  ↪ k                 — a knot traces the channel closed
↘ (↮ f ⊙ g)   =  ↪ (f . ↩ (↘ g))     — g slides inside the loop
↘ (f ⊙ g)     =  ↘ f . ↘ g           — composition interprets both sides

Where: ↑ = Lift, ↮ = Knot, ⊙ = Compose, ↘ = reify, ↪ = trace, ↩ = untrace.

```

There is another semantic interpretation — encode into a hyperfunction:

``` haskell
encode (Lift f)      = lift f
encode (Compose f g) = encode f . encode g
encode (Knot f)      = trace (encode f)    -- Hyper's Trace instance, not the base arrow's
```

The `trace` in the Knot case is Hyper's own `Trace` instance. Where `Trace (->) (,)` ties a lazy knot with a single `let` binding, `Trace Hyper (,)` ties a coinductive one: the feedback value cycles through Hyper continuations rather than a recursive thunk. The knot remains structural — it can still be composed, rearranged, encoded further — rather than collapsing to a plain function.

``` haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

Under encode, the tags dissolve. What remains is a single coinductive type where every value carries its own continuation — the feedback channel that Knot surfaced becomes structural in the type itself. The two interpretations meet at the triangle: `lower . encode = reify`.

The final encoding seems to provide very strong guarantees: O(1) amortised composition with no left-nesting penalty; a structural guarantee that sliding holds; and efficient coinductive feedback. That's the hope at least.

From another perspective, circuits is a paean to some underappreciated pearls in the Haskell infrastructure. The lazy-knot of loop and the engineering that caters for it kind of got buried in the arrows side-pocket. And applying delimited continuation primitives so readily and clearly is a reward of sticking with the boring nature of static typing. By doing nothing but delay stuff, and keeping arrow scheduling open, application space can encompass parsing, streaming, performance metering & process wiring. 

## ⚙️ Install

```
(m)cabal build circuits
```

Compiles on MicroHS & GHC 9.10+ with `base` & `profunctors`

## 📡 Usage

```haskell
import Circuit
import System.IO
import Control.Arrow

-- Fibonacci via knot-tying
>>> take 5 (trace (\(fibs, ()) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs)) () :: [Integer])
[0,1,1,2,3]

-- Open, read, close as explicit circuit stages
>>> :{
let step (Left (h, acc)) = hIsEOF h >>= \eof ->
      if eof then pure (Right (h, acc))
      else hGetLine h >>= \line -> pure (Left (h, line : acc))
    step (Right h) = pure (Left (h, []))
    pipeline = Lift (Kleisli (\fp -> openFile fp ReadMode))
             >>> Knot (Kleisli step)
             >>> Lift (Kleisli (\(h, ls) -> hClose h >> pure (length ls)))
:}

>>> runKleisli (reify pipeline) "readme.md"
149
```

The Either tensor gives you iteration for free — `Left` continues, `Right` exits. Both the Handle and the accumulator ride the feedback channel as explicit state. For the full word-count pipeline with frequency analysis, metering, and a mermaid diagram, see the **[words](https://github.com/tonyday567/words)** repo.

## 📊 why circuits

With circuits-meter, timing is a one-liner. Here's the word-count pipeline:

```mermaid
flowchart TD
    A["FilePath"] --> B["openf"]
    B --> C["Handle"]
    C --> D{"hIsEOF ?"}
    D -->|"no"| E["hGetLine"]
    E --> F["words"]
    F --> G["map toLower"]
    G --> H["filter (not . null)"]
    H --> I["foldl' insertCount"]
    I --> J["Left (acc, Handle)"]
    J -.->|"feedback"| D
    D -->|"yes"| K["Right (Handle, Map)"]
    K --> L["hClose + fmtTable"]
    L --> M["String"]
```

Each component can be metered independently — the circuit structure makes the insertion points obvious. The full runnable source is in the **[words](https://github.com/tonyday567/words)** repo.

## 📦 Application

circuits is being developed alongside:

**[circuits-parser](https://github.com/tonyday567/circuits-parser)** — presents a parser as `newtype Parser f a = Parser { circuit :: Circuit (->) Either f (These a f) }` for a wide variety of `f` and `a`, with `runParser` as `reify . circuit`.

**[circuits-io](https://github.com/tonyday567/circuits-io)** — uses `Circuit (Kleisli m) Either` with `m` as `STM` and `IO` to orchestrate file I/O, sockets, queues, servers, timings and (a)synchronicity.

**[circuits-meter](https://github.com/tonyday567/circuits-meter)** — circuit measurement and performance, taking advantage of channel provision via `ambient`.

## 📖 Read

[Kidney & Wu (2026)](https://doi.org/10.1145/3776649) — hyperfunctions as communicating continuations; the producer-consumer decomposition that Hyper unifies.

["Coroutining Folds with Hyperfunctions"](https://doi.org/10.4204/eptcs.129.9) — Launchbury, Krstic & Sauerwein (2013). The original hyperfunction axiom system that circuits builds on.

`other/` — the narrative arc: notation, marks and stacks, the Knot derivation, the triangle proof, tensor choice, the Mendler case, and worked examples. The long version of what this readme sketches.

`examples/` — cards: parsers, pipes, Elgot iteration, delimited continuations. Paste code blocks into `cabal repl`.

## Contributing

We welcome contributions of any persuasion or fancy. New contributors should open an issue and say hi.

LLM policy

LLMs and agents have been used in the development of this library, including category theory, coding, generation, refactoring, documentation and narrative.

what we prefer
  ⟜ all code must compile, have and pass doctests, and be reviewable.
  ⟜ do not submit code where intent is opaque, or that is difficult to read, understand, test and reason about.
  ⟜ respects a library style of supplying comments, annotation and examples that form an integral whole together with the code submitted.

<br>

[![Hackage](https://img.shields.io/hackage/v/circuits.svg)](https://hackage.haskell.org/package/circuits)
[![build](https://github.com/tonyday567/circuits/actions/workflows/haskell-ci.yml/badge.svg)](https://github.com/tonyday567/circuits/actions/workflows/haskell-ci.yml)
