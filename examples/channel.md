⟝ channel-pattern

# Channel: Stepwise Communication via Hyperfunctions

## The spec

```
[1,2,3] -> emitSingles -> circuitTake 2 -> collectSingles -> [1,2]
```

Three components, each with internal state, communicating stepwise. Composable.

## Prior state

The initial attempt was to encode each component as a `Circuit` with `Loop`,
compose via `Compose`, and interpret via `lower`. Two Loops with different
feedback types (list threading vs count threading vs accumulation) compose
structurally — the Mendler case in `lower` handles `Loop`-on-left-of-`Compose`.
This works.

The Hyper encoding ran into a wall: `Hyper a b` is opaque. `lower` provides
a constant continuation, `run` ties the recursive knot. Neither gives stepwise
advancement — you either observe once or consume everything. A Hyper cannot
"pause" mid-computation and expose its internal state.

## Solution: Producer / Consumer duality

From Kidney and Wu, *Hyperfunctions: Communicating Continuations* (POPL 2026).

Two dual Hypers communicate via `invoke`:

```haskell
type Producer o a = (o -> a) ↬ a    -- produces messages of type o, result a
type Consumer i a = a ↬ (i -> a)    -- consumes messages of type i, result a
```

Constructors (Section 2.4, Eqs 10-11):

```haskell
prod :: o -> Producer o a -> Producer o a
𝜄 (prod o p) q = 𝜄 q p o           -- send message o, continue with p

cons :: (i -> a -> a) -> Consumer i a -> Consumer i a
𝜄 (cons f p) q i = f i (𝜄 q p)    -- receive message i, process with f, recurse
```

A producer and consumer run together via `𝜄` (invoke):

```
𝜄 :: Producer m a -> Consumer m a -> a
```

Each `prod` sends a message, each `cons` receives one. They alternate in
lockstep — one step per message. State is threaded not through mutable cells
but through the continuation chain: `prod` captures the rest of the producer
in `p`, `cons` captures the rest of the consumer in `p`, and `𝜄 q p` links
them together.

### emitSingles (Producer)

```haskell
emitSingles :: [a] -> Producer (Maybe a) [a]
emitSingles = foldr (\x p -> prod (Just x) p) (prod Nothing (doneP []))
```

Produces `Just x` for each element, then `Nothing` to signal done.
The accumulator `[a]` is the final result (empty list — elements are
collected by the consumer).

### collectSingles (Consumer)

```haskell
collectSingles :: Consumer (Maybe a) [a]
collectSingles = h
  where
    h = cons step h
    step mx acc = case mx of
      Just x  -> x : acc
      Nothing -> acc
```

Coinductive: `h = cons step h` is an infinite chain. It consumes as many
messages as the producer sends. When the producer terminates (via `doneP`),
the Consumer's base case propagates backward through the chain of `step`
applications, building the result.

The coinductive Consumer is the key insight that was missing earlier. A
finite Consumer (built from a list of known length via `foldr`, like the
zip example in the paper) can't handle an open-ended stream. The coinductive
`h = cons step h` can.

### Two-component pipeline

```haskell
pipeline2 :: [a] -> [a]
pipeline2 xs = emitSingles xs ⧅ collectSingles
```

Result: `pipeline2 [1,2,3] = [1,2,3]`. The producer emits three `Just`s
then `Nothing`; the consumer collects them. Stepwise communication via
`prod`/`cons` at each message boundary.

### circuitTake as a Channel

From Section 5.1, Shivers and Might's Channel type:

```haskell
type Channel r i o = (o -> r) ↬ (i -> r)
```

A Channel consumes `i`, produces `o`, result `r`. It's a single Hyper that
faces both directions — when invoked with its dual, it receives input and can
produce output.

```haskell
takeChannel :: Int -> Channel [a] (Maybe a) (Maybe a)
takeChannel n = go n
  where
    go 0 = Hyper $ \_ i -> case i of { Nothing -> []; Just _ -> [] }
    go k = Hyper $ \out i ->
      case i of
        Nothing -> []
        Just x  -> invoke out (go (k-1)) (Just x)
```

When `k > 0`: receives `Just x`, passes it through via `invoke out (go (k-1)) (Just x)`.
The `out` is the dual channel (connected to the consumer). The `go (k-1)` is the
continuation with decremented counter.

When `k == 0`: ignores input, returns `[]` — the empty accumulator. The consumer
never sees messages beyond the limit.

### Channel composition

The paper's composition: `Consumer o r ⊙ Channel r i o = Consumer i r` (Section 5.1).
In our Category instance:

```haskell
takeChannel . collectSingles :: Consumer (Maybe a) [a]
```

The Channel (consuming `Maybe a`, producing `Maybe a`) composed with the Consumer
(consuming `Maybe a`) yields a new Consumer that consumes `Maybe a` with the
Channel's counting logic interposed.

### Three-component pipeline

```haskell
pipelineChannel :: Int -> [a] -> [a]
pipelineChannel n xs = emitSingles xs ⧅ (takeChannel n . collectSingles)
```

Result: `pipelineChannel 2 [1,2,3] = [1,2]`. Compositional. Each component
can be built and tested independently, then composed via `.` and `⧅`.

## The stepwise Hyper pattern

The earlier exploration failed because `lower` provides a constant continuation
(`base a`) — state never advances. `run` ties the knot — consumes everything.

The Producer/Consumer pattern shows what WAS possible: **the continuation
varies per step**. Not by mutating a single continuation, but by building a
CHAIN of continuations linked through `invoke`. Each `cons` in the chain
processes one message and invokes the next. The "state" is distributed across
the chain, not stored in a cell.

This is the pattern the user described: "peel off a value, do something with it,
then add back in a new hyperfunction." The "add back" is `𝜄 q p` — invoking the
rest of the chain with the new state.

## Turn-based vs concurrent

The Producer/Consumer model is **turn-based** (coroutine-style). Producer and
Consumer alternate: producer sends, consumer receives, producer sends, etc.
This is the "taking turns" pattern — each side runs until it communicates,
then yields to the other.

### Stable marriage: the "both at once" pattern

From Allison (1983) via Kidney & Wu §5.3. Men and women are independent
coroutines. They communicate by message-passing: men propose, women accept
or jilt. Jilting is the concurrent moment — a woman's decision to jilt her
current fiancé wakes THAT man's coroutine, which resumes proposing. Control
transfers between coroutines: not A then B then C, but A triggers B triggers
C, with the order depending on who jilts whom.

The paper implements this with `MonadCont` (callCC) and `IORef` — first-class
continuations capture the "rest of the computation" and mutable references
track the current state of each coroutine.

A pure version (see `~/haskell/circuits/examples/stable-marriage.hs`) uses
explicit state machines with a scheduler that interleaves coroutine steps.
Each man and woman is a `Coro s i o` — a function from state and input to
(output, next state). The scheduler picks the next man to propose, sends
the proposal to the woman's coroutine, and handles jilting by adding the
jilted man back to the queue.

The trace from the paper's example:

```
Aaron proposes to Ciara; accepted
Barry proposes to Ciara; rejected
Barry proposes to Betty; accepted
Conor proposes to Ciara; accepted; jilts Aaron
Aaron proposes to Annie; accepted
```

Result: [(Annie, Aaron), (Betty, Barry), (Ciara, Conor)].

Key differences from the pipeline:

| Aspect | Pipeline (channel.md) | Stable marriage |
|--------|----------------------|-----------------|
| Direction | Data flows one way | Messages flow both ways |
| Components | Stages (producer→transform→consumer) | Peers (each man/woman is independent) |
| Order | Fixed (sequential) | Dynamic (depends on jilting) |
| Control | Each component yields after one message | Control jumps when jilted |
| State | In the continuation chain | Explicit (engagements, preference position) |

The paper's contribution: hyperfunctions (the `Channel` type `(o→r) ↬ (i→r)`)
can express BOTH patterns. The Producer/Consumer pair uses `invoke` for
lockstep communication. The `Co` monad (wrapping a Channel in a continuation
monad) adds `yield` and `send` for first-class coroutine control. The paper
shows these are sufficient for both turn-based pipelines and concurrent
stable marriage.

## What Circuit's Loop gives that Hyper's Producer/Consumer doesn't

Both achieve stepwise state threading with composable components. The
difference is in how the feedback channel is represented:

- **Circuit Loop**: The tensor `t` carries the protocol. `Either` distinguishes
  "continue" (Left) from "stop" (Right). `(,)` carries parallel state. `These`
  carries both. The `Trace` class provides the iteration semantics. The caller
  (`lower`) drives the loop via `trace`. One type, multiple tensors.

- **Hyper Producer/Consumer**: The protocol is embedded in the message type
  (`Maybe a` with Nothing as stop signal). The duality is structural —
  Producer and Consumer are mirror images via `invoke`. No separate `Trace`
  class; the iteration is in the chain of `cons`/`prod` constructors. Simpler
  types but less parametric — changing the protocol means changing the
  message type.

Circuit's Loop is more general (any tensor, any trace semantics). Hyper's
Producer/Consumer is more specific but also more direct — the pattern is
immediately visible in the types.

## Code

See `~/haskell/circuits/examples/spec-hyper.hs` for the full implementation
with Producer, Consumer, Channel, and all three pipeline variants.
