# mealy-agents ⟜ stateful agents as traced circuits

`Circuit (Mealy s) Either [Text] Text` is a natural model of an agent:
stateful, iterative, compositional. The state threads through every
constructor — `Lift`, `Compose`, `Knot` — and the `Either` tensor gives
agents the ability to "think" (loop internally) before responding.

---

## Mealy as a category

```haskell
newtype Mealy s a b = Mealy { runMealy :: s -> a -> (s, b) }

instance Category (Mealy s) where
  id = Mealy (\s a -> (s, a))
  Mealy f . Mealy g = Mealy (\s a -> let (s', b) = g s a in f s' b)
```

Composition threads state left-to-right. The state `s` is never lost;
it flows through the entire circuit.

## Trace (Mealy s) Either

```haskell
instance Trace (Mealy s) Either where
  trace (Mealy f) = Mealy (\s b -> go s (Right b))
    where
      go s x = case f s x of
        (s', Right c) -> (s', c)
        (s', Left a)  -> go s' (Left a)
  
  untrace (Mealy f) = Mealy (\s e -> case e of
    Left a  -> (s, Left a)
    Right b -> let (s', c) = f s b in (s', Right c))
```

The state threads through the while-loop. Each `Left` iteration updates
state before re-entering. This is `Circuit (Kleisli (State s)) Either`
without the monad overhead.

## Agent = Circuit (Mealy s) Either [Text] Text

An agent is a stateful circuit that:
- **takes turns** (`Either` tensor)
- **reads context** (`[Text]` input)
- **produces text** (`Text` output)
- **remembers state** (`Mealy s`)

```haskell
-- A counting agent: remembers how many messages it has seen
counterAgent :: Mealy Int (Either Int [Text]) (Either Int Text)
counterAgent = Mealy (\n x -> case x of
  Left 0  -> (n, Left 1)
  Left 1  -> (n + 1, Right ("Seen: " ++ show (n + 1)))
  Right _ -> (n, Left 0))
```

`Knot counterAgent` ties the thinking loop. The agent receives `[Text]`,
enters `Left 0` (start thinking), counts in state, then exits `Right`
with a response. The final state persists for the next invocation.

## What Knot means for agents

In `Circuit (Mealy s) Either`, `Knot` is not just a feedback channel —
it is an **internal monologue**. The agent can loop, reflect, update its
state, and only then produce output. The `Knot` constructor is the
agent's ability to think before speaking.

`Compose` chains agents sequentially: agent A speaks, agent B listens.
The state of each agent is independent (different `s` parameters), but
the conversation flows through the `Either` handoff.

## Why this pops out

| feature | Circuit (->) | Circuit (Mealy s) |
|---------|-------------|-------------------|
| feedback | pure, stateless | stateful |
| trace | lazy knot | while-loop with state threading |
| agent model | function pipeline | stateful actor |
| Knot meaning | stream tie | reflection / internal monologue |

The `Mealy` arrow is the minimal addition that turns `Circuit` from a
dataflow language into an agent language. State is explicit, composition
preserves it, and `Knot` gives agents time to think.

## Reference

- `examples/hyper-loop.md` — stepwise iteration in Hyper
- `examples/encode-either.md` — why Hyper can't host Either natively
- `other/06-follow-the-knots.md` — agents and the circuits-io frontier
