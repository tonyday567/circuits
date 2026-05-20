# Some More Knots

**Summary:** In which we stop proving and start making. Each section
is a circuit type; each type is a use case.
**Prev:** [05-no-remorse-once-removed.md](05-no-remorse-once-removed.md)

---

## `foldH` — coroutining folds

The worked example that cracked the structure open.  Two folds share a
continuation, interleaving element-by-element — the thing `foldr` alone
cannot express.  Full derivation in [examples/proequip.md](../examples/proequip.md).

`foldH` and `foldr` are the same λ-term with different generators:

```haskell
foldr'  []     = id              foldh'  []     = id
foldr'  (x:xs) = (:) x . foldr' xs      foldh' (x:xs) = push x . foldh' xs
```

`(:)` attaches to the outside of a list.  `push` threads into the inside
of a Hyper, through the continuation channel.  Same shape, flipped
polarity.  Both build endofunction chains — `Endo([a])` vs `Endo(Hyper a b)`.

From this, `zip` and `zipWith` emerge as two folds composed via `.` with
a channel token carrying elements between them.  The structure admits two
independent composition layers (horizontal pipeline, vertical element
transform).  For the double-category framing of this observation see
[examples/proequip.md](../examples/proequip.md).

---

## `Circuit (->) Either [s] (These a [s])` — parsers

A state-based parser.  The `Either` tensor gives two-phase alternation:
`Left` feeds back (continue parsing), `Right` exits (done).  `These`
output distinguishes three outcomes:

| case | meaning |
|------|---------|
| `These a s` | consumed some, result + remainder |
| `This a`    | consumed everything, final result |
| `That s`    | no progress, stream intact |

`That s` is the key innovation over `Maybe (a, s)` — it explicitly
signals "touched nothing, safe to backtrack."  The mtok tokenizer port
(from `regex-applicative`) validated all three arms in practice.

Choice (`<|>`) is where `Knot` pulls its weight.  The `Either` tensor's
two phases map to the two branches of alternation: `Right` = try p1,
`Left` = try p2.  `many` and `some` use plain `Lift` + recursion, not
`Knot` — the `These` pattern match carries all the control flow.

See [examples/parser.md](../examples/parser.md).

---

## `Circuit (->) Either a b` — while-loops

Three canonical loop patterns from one `Knot`.  The convention matches
`Trace (->) Either`: `Left s` = continue (feedback), `Right r` = done
(exit).  No bridge needed between step functions and the `Knot` constructor.

```haskell
loop  :: (s -> Either s r) -> s -> r    -- fundamental form
while :: (s -> Bool) -> (s -> r) -> (s -> Either s r) -> s -> r  -- condition, then step
until :: (s -> Bool) -> (s -> r) -> (s -> Either s r) -> s -> r  -- step, then condition
for   :: Int -> (Int -> (s -> Either s r)) -> s -> r  -- counted loop
```

All four are `reify (Knot step') s0` with different `step'` bodies.
The `Either` tensor provides the iteration; the step function provides
the logic.

See [examples/while.md](../examples/while.md).

---

## `Circuit (Kleisli m) Either a b` — effectful loops

Swap the base arrow to `Kleisli m` and every step can perform effects:

```haskell
reify :: Circuit (Kleisli m) Either a b -> a -> m b
```

The `Trace (Kleisli IO) Either` instance uses GHC's delimited
continuation primops (`prompt#` / `control0#`).  Each iteration
re-establishes a prompt boundary; `Left` fires `control0` to capture the
continuation and re-enter — constant stack space regardless of iteration
count.

```haskell
trace :: Kleisli IO (Either a b) (Either a c) -> Kleisli IO b c
```

`trace` seals the delimited scope.  `untrace` lifts a plain effect into
the channel.  Together they give sequential feedback with no stack growth,
no `forkIO`, no `IORef`.

See [examples/resource-io.md](../examples/resource-io.md), [examples/traced.md](../examples/traced.md).

---

## `Circuit (Kleisli m) Either ~ Pipe m`

The entire `pipes` library compresses into one type:

```haskell
Pipe m a b ~ Circuit (Kleisli m) Either a b
```

The `Either` tensor's `Left`/`Right` handoff matches `Proxy`'s
`Request`/`Respond` alternation.  Await is `Left`, yield is `Right`.
The pattern match in `reify` appears through `fmap`, `<*>`, `>>=`,
and the rest — every instance follows the same structural recursion.

See [examples/pipes.md](../examples/pipes.md).

---

## `Hyper [Text] [Text]` — agents

Two `Hyper [Text] [Text]` glued through their duals.  Each side's output
is the other's input; the continuation channel carries the conversation
state:

```haskell
agentA ⇸ agentB    -- A speaks, B listens
agentB ⇸ agentA    -- B speaks, A listens
```

No `run`, no `lower` — just two open ends composing via the dual arrow.
The conversation IS the protocol.

---

## `Circuit (Kleisli IO) (,)` — metering

Performance measurement.  A `Meter` introduces a state wire before a
computation and reads it after — clock time, memory allocation, or any
observable state:

```haskell
meterK :: Meter s t -> Kleisli IO a b -> Kleisli IO a (t, b)
```

`meterK` is `reify . meterC . Lift`: lift the arrow into `Circuit`, wrap
it with pre/post measurement via `ambient`, then reify back.  The bracket
operators make the metering unobtrusive:

```haskell
meterC_ m c = (m ◅ c) ▻ m
```

This lives in `circuits-meter` (see [examples/ambient.md](../examples/ambient.md)).

---

## Sibling libraries

- **circuits-parser** — `Circuit (->) Either [s] (These a [s])` as a parser
  for a wide variety of `s` and `a`.  Fast, working, a dependency of `chart-svg`.
- **circuits-io** — `Circuit (Kleisli IO) Either` with bidirectional channels,
  producer/consumer composition, and resource-bracketed IO loops.
- **circuits-meter** — `Circuit (Kleisli IO) (,)` with metering brackets
  and delimited-continuation performance measurement.

---

## The examples directory

| card | what it shows |
|------|---------------|
| [proequip.md](../examples/proequip.md) | coroutining folds, the `(:)`/`push` dual, double category framing, open lemmas |
| [parser.md](../examples/parser.md) | `Either`+`These` parser combinators |
| [while.md](../examples/while.md) | loop/while/until/for on `Either` |
| [pipes.md](../examples/pipes.md) | `Pipe m` isomorphism |
| [resource-io.md](../examples/resource-io.md) | delimited continuations, prompt/control0 |
| [traced.md](../examples/traced.md) | `Trace` instances, JSV axioms |
| [hyper.md](../examples/hyper.md) | `Hyper` construction and elimination |
| [circuit.md](../examples/circuit.md) | `Circuit` GADT, `reify` |
| [hyper-chain.md](../examples/hyper-chain.md) | Category composition on `Hyper` |
| [encode-either.md](../examples/encode-either.md) | `encodeEither`, `runEither` |
| [ambient.md](../examples/ambient.md) | `ambient`, state threading |
| [elgot-abacus.md](../examples/elgot-abacus.md) | Elgot iteration |
| [yaya.md](../examples/yaya.md) | recursion schemes bridge |
| [reader-monad.md](../examples/reader-monad.md) | why no Monad instance |
| [optics.md](../examples/optics.md) | profunctor optics on Circuit |
| [lawvere.md](../examples/lawvere.md) | comparative engineering with Lawvere |
| [proarrow.md](../examples/proarrow.md) | `Trace` ≅ `Strong + Costrong` |

---

## References

- [Launchbury, Krstic & Sauerwein (2013)](https://doi.org/10.4204/eptcs.129.9) — coroutining folds with hyperfunctions
- [Kidney & Wu (2026)](https://doi.org/10.1145/3776649) — hyperfunctions: communicating continuations
- [Van der Ploeg & Kiselyov (2014)](https://doi.org/10.1145/2633357.2633360) — Reflection Without Remorse
- [Kmett, hyperfunctions](https://github.com/ekmett/hyperfunctions) — canonical implementation
- `circuits-parser` — production parser library on Circuit
- `circuits-io` — bidirectional channels and IO loops
- `circuits-meter` — circuit measurement and performance
