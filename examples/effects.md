# effects — ReaderT, three-layer cake, Bluefin, effectful, and circuits

**Context:** A low-key comparison of how `Circuit` and `circuits-io` sit alongside the dominant ReaderT + three-layer style, and the two leading "analytic" effect systems (Bluefin, effectful). No advocacy. Just where the models touch, where they pull apart, and what initial construction changes about layer responsibilities.

**Reader:** Someone maintaining a ReaderT-style app who is curious whether circuits can be used in a few hot spots without forcing an architecture change.

---

## The reference idioms

### ReaderT design pattern (Snoyman 2017)

- Main application type is `ReaderT Env IO` (or newtype).
- `Env` carries config + mutable cells (`IORef`, `TVar`).
- Avoid deep stacks, `StateT`/`WriterT`/`ExceptT` in the primary path.
- `Has*` classes (or lens) + mtl constraints for selective exposure.
- Mutable references are accepted for the things that truly need to survive exceptions and concurrency.

### Three-layer cake (Parsons 2018)

- **Layer 1** (`AppT`): the `ReaderT` orchestration / capability layer. Keep it tiny.
- **Layer 2**: thin domain mtl classes (`MonadLock`, `AcquireUser`, ...) for swappable external services. Not god classes.
- **Layer 3**: pure functional core — simple functions, data, small command types when effects must be described rather than performed.

The Gary Bernhardt "functional core, imperative shell" framing is explicitly claimed as the underlying model.

### Bluefin and effectful (2024–2026)

Both are "analytic" (IO under the hood) systems that reject deep MTL stacks:

- **Bluefin**: coroutines as plain functions (`a -> Eff e b`), `Stream`/`Consume` as the bidirectional case. Connect via `connectCoroutines` (MVar under the hood). Extremely lightweight. Strong emphasis on prompt resource finalisation for streams.
- **effectful**: `Eff es a` as `Env es -> IO a`. Static effects backed by `IORef`s in the environment. Dynamic effects via GADT operations + `localSeqUnlift` (a restricted delimited continuation). Dropped the freer queue machinery; kept the interface/interpretation split.

See also `reader-monad.md` for the explicit "when you need a monad" escape hatch that circuits itself recommends.

---

## Circuits as initial construction for feedback

`Trace t arr a b` (the GADT with `Arr` and `Knot`) is the *initial* object in the category of traced monoidal categories over the base arrow `arr`. `Hyper` is the corresponding *final* (coinductive) encoding.

This is a deliberate design choice visible from the narrative arc (the knot forcing the GADT in `02-a-knot-recovers-fix`).

Contrast with final tagless style (the Layer 2 mtl classes):

- Final tagless: the "program" *is* the host-language term using the class methods. Different instances supply different interpretations. There is no separate data value representing the program between writing it and running it.
- Circuits: you build an explicit value (`Trace` or `Hyper`). You can inspect it, transform Knot bodies, bracket it with meters, choose the tensor, rewrite it, or partially evaluate it *before* the single interpretation step (`run`).

The price is the explicit `Arr` / `run` (or `lift` / `lower`) boundary when you cross into or out of full monadic composition. See `reader-monad.md` for the exact pattern and the rationale (a `Monad` instance would erase the internal feedback distinctions).

---

## Opt-in service in an existing pipeline

The claim under test: can a ReaderT (or Bluefin/effectful) codebase treat circuits as a *service* for selected stretches — "Arr this bit, do the feedback / channel / measurement work, lower back out" — without dragging the rest of the architecture along?

The evidence from the existing machinery:

### 1. Any monad stack can be the base arrow

```haskell
type App = ReaderT Env IO

-- This is a perfectly legal base arrow
type AppArrow = Kleisli App

-- You can therefore write:
someStretch :: Trace Either AppArrow (Either s a) (Either s b)
someStretch = ...
```

`Trace Either (Kleisli m)` exists for any `Monad m`. `Trace (,) (Kleisli m)` exists when `m` has `MonadFix`. Your `App` monad (ReaderT + whatever) works as long as those constraints are satisfied at the use site.

### 2. Ambient state threading (invisible context)

`ambient` (and `ambientBy`) threads an extra state wire *past* the feedback channel so the inner circuit never sees it:

```haskell
import Circuit.Monoidal (ambient)

-- A pure increment that knows nothing about logging context
increment :: Trace (,) (->) Int Int
increment = Arr (+1)

-- Thread a log accumulator alongside without touching the payload logic
metered :: Trace (,) (->) ([String], Int) ([String], Int)
metered = ambient increment
```

This is the "plugin layer" pattern. The same mechanism is used by `circuits-meter` to bracket existing arrows with timing or space measurement without forcing the measured code to be aware of the meter.

See `Circuit.Meter` (`withMeter`, `meterA`, `meterAction`, `◅` / `▻`, `ambient` usage) for the full instrumentation design. The meter state rides on the `(,)` tensor via `ambient`; the original payload logic is wrapped with `Arr` and `run` recovers an ordinary arrow.

### 3. Explicit escape hatch when you need the monad

From `reader-monad.md`:

```haskell
stepC :: Trace (,) (->) Int Int
stepC = Arr $ \n ->
  let n'  = run incC n
      n'' = run doubleC n'
  in n''
```

You pay the `run` / `lower` cost only on the stretches that need full `do` notation, `local`, `catch`, or your Layer 2 classes. The rest of the circuit stays in the algebraic form.

### 4. Resource lifecycles as structure

`examples/resource-io.md` encodes acquire/use/release as a state machine on the `Either` feedback channel of a `Knot` over `Kleisli IO`. The `Right` exit path is the single place cleanup is allowed. This is an alternative to `bracket` / `ResourceT` that lives in the circuit layer rather than the ReaderT Layer 1.

You can still use ordinary `bracket` in the surrounding `App` code; the circuit fragment just guarantees its own internal resources.

### 5. Channels as first-class values

`circuits-io`'s `Producer` / `Consumer` (Ends) and `endsQueue` + queue strategies give you composable bidirectional channels before you `close` or `closeQueue` them. This is the same runtime mechanism (two parties + mutable cell) that Bluefin coroutines and effectful dynamic effects use, but exposed as values in the algebra rather than as operations inside a monad.

See `ends-effectful.md` for the detailed mapping (and the open design questions about an "effectful tensor").

---

## How initial construction flexes the three layers

In a classic three-layer ReaderT app, Layer 2 is where you pay the "swappable implementation" tax via mtl classes. The program is written against the interface; the top-level handler (or test) supplies the instance.

With circuits you can move some of that concern *into* the construction phase:

- A complex feedback or channel topology can be assembled, inspected, metered, or rewritten as a `Trace` value in Layer 3 (or a thin Layer 2) *before* any IO or ReaderT action runs.
- The "handler" for that fragment can be a `run` or a custom interpreter that only touches the Knot bodies it cares about.
- Concerns that would have required a new mtl class (or a capability record) can instead be expressed as combinators over the explicit representation (`withMeter`, `ambient`, queue strategies, `Step` processors, etc.).

This does not eliminate Layer 2. It gives you an additional place to locate concerns that benefit from having a data structure to operate on. The rest of the app (the parts where live dispatch against a class dictionary is the right granularity) can stay exactly as before.

"Por que no los dos?" is the practical answer. The functional core stays pure. The orchestration shell can remain a ReaderT `AppT` with whatever mtl or capability surface you already maintain. Selected stretches inside that shell become more structured and inspectable by opting into the traced algebra for as long as they need it, then returning to the normal flow via `run`.

---

## Quick compatibility table

| Aspect                        | ReaderT + 3-layer                  | Bluefin                          | effectful                          | circuits + circuits-io                  |
|-------------------------------|------------------------------------|----------------------------------|------------------------------------|-----------------------------------------|
| Primary effect style          | Env + mutable refs in ReaderT      | Coroutines as functions          | Env + IORefs + GADT ops + unlift   | Explicit traced values (Knot / Trace)   |
| Program representation        | Host terms (final tagless)         | Host terms + coroutine fns       | Host terms + GADT ops              | Trace (initial) or Hyper (final)        |
| Feedback / loops              | Manual recursion or StateT         | Coroutine yield/await            | Handled via unlift continuations   | First-class (Knot + Trace)              |
| Bidirectional channels        | MVar/TQueue + async                | Coroutine pairs + connect        | Dynamic effects + Env cells        | Producer/Consumer + endsQueue           |
| Resource safety               | bracket / ResourceT in Layer 1     | Prompt finalisation in streams   | Handler-managed                    | Structural (Right exit path on Either)  |
| Instrumentation / metering    | Manual wrappers                    | Effect composition               | Handler wrapping                   | meterA / withMeter / ambient (plugin)   |
| Escape to full monad          | You're already there               | `Eff` is the monad               | `Eff` is the monad                 | Explicit lower/run (reader-monad.md)    |
| Can host the others           | Yes (base for everything)          | Limited                          | Limited                            | Yes (Kleisli AppM as base arrow)        |
| Can be hosted inside the others | N/A                              | Via bridge (e.g. endsQueue)      | Via bridge                         | Yes — opt-in stretches                  |

---

## Quadratic slowdown — cross-library benchmark

The quadratic slowdown that affects `pipes` and `streaming` (see issues [#234](https://github.com/Gabriella439/pipes/issues/234) and [#109](https://github.com/haskell-streaming/streaming/issues/109)) is a pathology of free-monad interpretation: left-associated `>>=` chains force each bind to traverse the accumulated structure, giving O(n²) total cost.

The question for circuits: does sequential composition have the same problem?

**Answer: no.** `run` (and `runFree`) are structural folds (catamorphisms), not searches. Each sequential composition becomes one function composition `(.)` in the base arrow — O(1). For `Free`/`Net`, the `Compose` constructor maps directly to that `(.)`; for `Trace`, the constructor is absent and `(.)` is used directly. The quadratic slowdown is specific to free *monads* where `>>=` must find the next constructor by traversing the chain. Circuit's `(.)` just appends.

The `circuits-effects` project (`~/haskell/circuits-effects/`) contains a cross-library benchmark that builds left-skewed and right-skewed pipelines of N stages and measures execution time. Reproduced 2026-05-29, GHC 9.14.1, Apple M-series:

```
=== Cross-library: left-vs-right skew streaming ===
    library   size     left(us)      right(us)     ratio
    circuits    100      4.3          4.1          1.1
    bluefin     100      1.5          1.0          1.4
    effectful   100      4.0          1.6          2.5
    pipes       100      42           2.5          17         ← O(n²) visible

    circuits    1000     29           38           0.77
    bluefin     1000     630          9.6          66          ← see note
    effectful   1000     11           9.5          1.2
    pipes       1000     1,900        22           85

    circuits    10000    440          400          1.1
    bluefin     10000    180          95           1.9
    effectful   10000    140          89           1.6
    pipes       10000    370,000      220          1,700       ← O(n²) in full
```

At 10,000 stages: circuits 440µs, pipes 370,000µs — **840x difference**. Bluefin and effectful sit in the same 100–200µs range as circuits and are also linear (both wrap IO directly, no free structure to traverse).

The Bluefin @1000 left figure (630µs) is likely a warmup/GC artefact from the `unsafePerformIO` inside `runPureEff`; the @10000 numbers (180µs left, 95µs right) are more representative. Rerunning warms the allocation path and the ratio drops to ~2x.

**Why circuits is immune:** for the free encodings, `runFree (Compose f g) = runFree f . runFree g`. The `Trace` encoding has no `Compose` constructor at all; `run` interprets the already-composed base-arrow term. No search, no traversal of accumulated structure. The Hyper path (`lower . encode`) is 2–3x faster still because it avoids building intermediate function compositions, but `run` is already O(n).

The benchmark code lives in `Circuit.Effects.CrossBench.{Circuits,Bluefin,Effectful,Pipes}` and is driven by `Circuit.Effects.CrossBench.benchAll`. It uses `circuits-meter` for the circuits-internal benchmarks and a simple `nanos`-based `timeIO` for the cross-library comparison so each library is measured the same way.

---

## Open questions (not conclusions)

- When is the `Arr`/`run` tax worth paying versus just writing the stretch in your native ReaderT/Bluefin/effectful style?
- Can a richer "effectful tensor" (carrying type-indexed Env-like state through the feedback channel) reduce the boundary cost for dynamic effects? (See the sketch in `ends-effectful.md`.)
- How much of a typical Layer 2 interface (`MonadFoo`) can be mechanically re-expressed as a small family of circuit combinators over a `Producer`/`Consumer` pair?

These are empirical questions that depend on the concrete workload. The machinery supports the "opt-in service" usage; whether any given codebase benefits is a measurement, not a foregone conclusion.

---

## References inside this repo

- `reader-monad.md` — the explicit escape hatch and why no `Monad` instance
- `resource-io.md` — structural resource lifecycles
- `state.md` — visible / ambient / hidden state mechanisms
- `optics.md` — traced structure as residual/context (lens-like)
- `pipes.md` — decomposition of an existing streaming abstraction
- `ends-effectful.md` (in the mg workspace) — the deepest existing comparison of Ends vs Bluefin coroutines vs effectful dynamic effects
- `circuits-effects` (`~/haskell/circuits-effects/`) — the cross-library benchmark project; source modules: `Circuit.Effects.{Co,Coroutine,Bench,CrossBench}`
- `Circuit.Monoidal` (`ambient`, `ambientBy`)
- `Circuit.Meter` (in the sibling `circuits-meter` package) — the canonical "plugin layer" demonstration

All example cards are intended to be pasted into `cabal repl` (with appropriate `-b` for extra dependencies) and verified.

---

*Low key. The goal is accurate description of the seams.*
