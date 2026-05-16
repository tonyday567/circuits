# Follow the Knots

**Summary:** In which we follow the knots through parsers and pipes and
agents, and glimpse the compact closed frontier where two Hypers talk
to each other.
**Prev:** [05-no-remorse-once-removed.md](05-no-remorse-once-removed.md)

---

The library's reach is its real selling point. Not one thing — one structure
that ties many knots. A natural home for makers: pick up a knot and make
something.

---

## Parsers

`Circuit (->) Either [s] (These a [s])` — the Either tensor gives genuine
two-phase alternation for backtracking; `These` output distinguishes "consumed
and succeeded" from "touched nothing, safe to backtrack" from "consumed
everything, done." The `Knot` constructor builds recursive grammars; the
Mendler case ensures left-recursive grammars are handled correctly.

The `circuits-parser` library ports `markup-parse` onto this foundation —
fast, working, a dependency of `chart-svg` and others. The mtok tokenizer
refactor confirmed the `These` three-arm pattern in practice. See
`examples/parser.md`.

---

## IO

`Circuit (Kleisli IO) Either a b` — the Either tensor gives sequential
feedback with a structural guarantee: the only way out is `Right`, so
every exit path must include resource release. The `Trace (Kleisli IO) Either`
instance uses GHC's delimited continuation primops (`prompt#`/`control0#`)
for constant stack space regardless of iteration count.

The `circuits-io` library builds on this for resource-bracketed IO loops,
producer/consumer channels via Emit/Commit, and the compact closed
frontier.

---

## Pipes

`Pipe m a b ~ Circuit (Kleisli m) Either a b`. The entire `pipes` library
compresses into one type parameterised over the monad. The Either tensor's
await/yield handoff matches the Proxy pattern's Request/Respond alternation.
The Mendler fold appears 13 times through `fmap`, `<*>`, `>>=`, and the rest —
every instance follows the same structural recursion. See `examples/pipes.md`.

---

## Agent & Lib

Two `Hyper [Text] [Text]` glued together through their duals. Each side's
output is the other's input; the continuation channel carries the conversation
state. No `run`, no `lower` — just two open ends composing via compact closure.

Lib is the terminal object Agents navigate through: a shared surface where
marks accumulate and state persists. A conversation such as the one that
produced this document is exactly this structure — two Hypers in compact
closed composition.

---

## Bidirectional Harness

The next engineering step: a harness where agents connect directly through
Hyper connections, with no intervening infrastructure like tmux. Two Hypers
composed compact-closed, each side driving the other's continuation. The
connection IS the protocol.

---

## The Compact Closed Frontier

The open question: does `encode` carry duals through the coinduction? A
Circuit with a `Dual` constructor (flipping `a` and `b`) plus `Knot` should
form a compact closed category when the base arrow is `*`-autonomous. The
triangle `lower . encode = lower` holds for the traced structure. Whether
it holds for the dual structure — whether `flatten` leaks the duality —
is the knot on the other side of this story.

---

## References

- `circuits-parser` — `Circuit (->) Either` with `These` output
- `circuits-io` — `Circuit (Kleisli IO) Either` with delimited continuations
- `examples/parser.md` — the parser knot
- `examples/pipes.md` — the pipes isomorphism
- `examples/resource-io.md` — bracketed resource lifecycle
