# Follow the Knots

**Summary:** In which we follow the type signatures through parsers and
pipes and agents, and glimpse the compact closed frontier where two Hypers
talk to each other.
**Prev:** [05-no-remorse-once-removed.md](05-no-remorse-once-removed.md)

---

The library's reach is its real selling point. Not one thing — one
structure that ties many knots. Each section header is a type. Each type
is a use case.

---

## `Circuit (->) Either [s] (These a [s])`

A state-based parser. The `Either` tensor gives two-phase alternation:
`Left` feeds back (continue parsing), `Right` exits (done). `These`
output distinguishes three outcomes — consumed and succeeded, touched
nothing (safe to backtrack), consumed everything.

```haskell
↘ :: Circuit (->) Either [s] (These a [s]) → [s] → These a [s]
```

`↘` interprets the circuit: feed it a token stream, get a result or a
continuation. The `↮` constructor builds recursive grammars:

```haskell
expr :: Circuit (->) Either [Token] (These Expr [Token])
expr = ↮ (step . ↩ (↘ term))
```

The `circuits-parser` library ports `markup-parse` onto this foundation —
fast, working, a dependency of `chart-svg`. The mtok tokenizer refactor
confirmed the `These` three-arm pattern.

---

## `Circuit (Kleisli m) Either a b`

An effect. Where `Circuit (->) Either a b` is a pure state machine, swap
the base arrow to `Kleisli m` and every step can perform effects:

```haskell
↘ :: Circuit (Kleisli m) Either a b → a → m b
```

`↘` gives you `a → m b` — a function that runs the circuit, performing
effects at each `Left` iteration, returning `b` when the loop exits via
`Right`. The `↮` constructor wraps an effectful arrow:

```haskell
ioLoop :: Circuit (Kleisli IO) Either String ()
ioLoop = ↮ (Kleisli $ \case
  Right s | length s < 3 → pure (Left (s <> "!"))
  Right s                → pure (Right ())
  Left s                 → pure (Right ()))
```

---

## `Circuit (Kleisli IO) Either`

The `Trace (Kleisli IO) Either` instance uses GHC's delimited
continuation primops (`prompt#` / `control0#`). Each iteration
re-establishes a prompt boundary; `Left` fires `control0` to capture the
continuation and re-enter — constant stack space regardless of iteration
count.

```haskell
↪ :: Kleisli IO (Either a b) (Either a c) → Kleisli IO b c
```

`↪` seals the delimited scope. `↩` lifts a plain effect into the channel.
Together they give sequential feedback sympathetic to the GHC heap —
no stack growth, no `forkIO`, no `IORef`.

```haskell
>>> runKleisli (↘ ioLoop) "a"
()
```

---

## `Circuit (Kleisli m) Either ~ Pipe m`

The entire `pipes` library compresses into one type:

```haskell
Pipe m a b ~ Circuit (Kleisli m) Either a b
```

The `Either` tensor's `Left`/`Right` handoff matches `Proxy`'s
`Request`/`Respond` alternation. Await is `Left`, yield is `Right`.
The pattern match in `reify` appears through `fmap`, `<*>`, `>>=`,
and the rest — every instance follows the same structural recursion.

```haskell
↘ :: Pipe m a b → a → m b
```

---

## `Hyper [Text] [Text]`

An agent. Two `Hyper [Text] [Text]` glued through their duals. Each
side's output is the other's input; the continuation channel carries the
conversation state:

```haskell
agentA ⇸ agentB    -- A speaks, B listens
agentB ⇸ agentA    -- B speaks, A listens
```

No `⥁`, no `↓` — just two open ends composing via the dual arrow. The
conversation IS the protocol. Lib is the terminal object agents navigate
through: a shared surface where marks accumulate and state persists.

The conversation that produced this document is exactly this structure —
two Hypers in compact closed composition.

---

## The Compact Closed Frontier

The open question: does `⇨` carry duals through the coinduction? A
`Circuit` with a `Dual` constructor (flipping `a` and `b`) plus `↮`
should form a compact closed category when the base arrow is
`*`-autonomous. The triangle `↓ . ⇨ = ↘` holds for the traced structure.
Whether it holds for the dual structure — whether `⇦` leaks the duality —
is the knot on the other side of this story.

---

## References

- `circuits-parser` — `Circuit (->) Either` with `These` output
- `circuits-io` — `Circuit (Kleisli IO) Either` with delimited continuations
- `examples/parser.md` — the parser knot
- `examples/pipes.md` — the pipes isomorphism
