<p align="center"><strong>⟴ circuits</strong></p>

## First-Class Feedback

> The free traced monoidal category is the smallest thing you can add to a
> category to get feedback. Not a library of combinators — a single GADT and
> a single coinductive type, a hyperfunction no less, connected by this Galois connection ...
>
> ~ What we learned building it

<br>

## ⚙️ Install

```
(m)cabal build circuits
```

Compiles on MicroHS & GHC 9.10+ with `base` & `profunctors`

## 📡 Usage

```haskell
import Circuit

-- Fibonacci via knot-tying
>>> take 5 (trace (\(fibs, ()) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs)) () :: [Integer])
[0,1,1,2,3]

-- Iteration with Either
>>> let step n = if n < 3 then Left (n + 1) else Right n in trace (either step step) (0 :: Int)
3
```

## 🧭 Pitch

circuits is a rethink of how to interact with a compiler and arrange code
pipelines — circuits — in ways that are intentional, clear, correct and performant.

Hyper is the same as the Kidney & Wu construction:

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

From the paper and surrounding literature, we use the hyperfunction axioms and derive a `Circuit`:

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  Knot    :: arr (t a b) (t a c) -> Circuit arr t b c
```

This happens to be the initial traced category over a base category and naturally encodes to a Hyper. To be concrete and on the nose, it's a 2-cell bolted on to the free category. Lifting the trace over a category and abstracting the tensor came later.

> Have you used your eyeballs yet and read Bartosz's latest? Original thought is a strong claim and could be awkward.
>
> ~ claude ([tank](https://github.com/tonyday567/mg/blob/main/word/tank.md) mode on)

`Circuit` covers functions, compositional paths, and feedback loops. `Hyper` is an efficient final encoding where feedback dissolves into the type structure itself. `Traced` abstracts the tensor, giving polymorphic loop semantics: lazy knots with `(,)` or iteration with `Either`.

`other/` traces these ideas from the [Kidney & Wu hyperfunctions](https://doi.org/10.1145/3776649) paper through a narrative arc. `Circuit` is the initial encoding — a GADT
with visible constructors, interpreted by `reify`. `Hyper` is the final
encoding — a coinductive type where feedback dissolves into the structure
itself. The triangle `reify = lower . encode` connects them.

## 📦 Sibling libraries

**circuits-parser** — `Circuit (->) Either f (These a f)` as a parser for a wide variety of f and a.

**circuits-io** — `Circuit (Kleisli IO) Either` as a way to engage with file I/O, sockets, servers, (a)timings & asynchronicity.

**circuits-meter** — circuit measurement and performance.

## 📖 Read

["tracing hyperfunctions"](https://doi.org/10.1145/3776649) — Kidney & Wu (2026). The paper that inspired the core construction. Introduces `Hyper` as a self-dual object in the traced sense and the hyperfunction axioms.

`other/` — the narrative arc (notation, marks-and-stacks, knot, triangle proof, tensors, Mendler case, examples). For the long version.

`examples/` — cards: parsers, pipes, Elgot iteration, delimited continuations. Paste code blocks into `cabal repl`.

## Contributing

We welcome contributions of any persuasion or fancy. New contributors should open an issue and say hi.

AI / LLM policy

LLMs and agents have been used in the development of this library, including category theory, coding, generation, refactoring, documentation and narrative.

what we prefer
  ⟜ all code must compile, have and pass doctests, and be reviewable.
  ⟜ if you open a PR, you must be able to explain what the code does and why. "my buddy Grok wrote it" is not an explanation.
  ⟜ do not submit code you have not read, understood, and tested.

what we do not do
  ⟜ ban AI tools. they are part of the workflow.
  ⟜ accept code that fails the same standards we apply to AI contributions.

code is code and coders are going to code.

<br>

[![Hackage](https://img.shields.io/hackage/v/circuits.svg)](https://hackage.haskell.org/package/circuits)
[![build](https://github.com/tonyday567/circuits/actions/workflows/haskell-ci.yml/badge.svg)](https://github.com/tonyday567/circuits/actions/workflows/haskell-ci.yml)