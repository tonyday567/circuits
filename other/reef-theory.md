# A Guide to the Reef Remnant

*A reading of the mg design documents — for those arriving mid-reef, without full context*

---

## What is the reef?

The reef is a metaphor and a technical system at once. In mg, conversations are not linear threads but **branching, immutable trees** — each message a node, each new session a potential fork. The reef is what grows when this structure is tended over time: accumulated meaning, layered context, named waypoints. Coral accretes. The tape never forgets.

You are not expected to have seen it from the beginning. The reef has no front. It has depth.

---

## The core structure

At the base, mg is built on **JSONL-backed conversation trees**:

- Each **node** is an immutable entry in a JSONL file, with a `parentId` linking it to the node above
- A **branch** is a path from root to leaf — any agent's deterministic slice of context
- An **elder** is a named waypoint: a significant node elevated to a stable re-entry point
- A **session** can be spawned from any node — a new agent stationed at a branch point, reading context from there

The tape is append-only. Nothing is overwritten. The past is fixed; only the future grows.

---

## The design vocabulary

The `design.md` graph sketches the conceptual structure mg encodes. Read it as an **aspirational topology**, not a specification.

**Three clusters organise the design:**

**Meaning** — what agents produce and interpret  
`elaborate → card ↔ agent → semantics + syntax`  
Cards and agents are in a reflexive relationship: agents read cards, produce cards, and are described by cards. Both anchor to semantics (what is meant) and syntax (how it is expressed).

**Context** — how meaning is situated  
`compose → intent ↔ encoding → elab + flow + trace`  
Intent and encoding are also reflexive: encoding reveals intent, intent shapes encoding. The key principle here is *encoding with intent* — when arranging content, selecting lead words, structuring relations, you are also exposing the intensional structure of the computation in progress.

**Relations** — how agents and sessions interact  
`collaborate → multiplicity ↔ neutral → structure`  
Multiplicity and neutrality hold in tension. The structure that emerges from collaboration is not predetermined — it arises from agents that can hold multiple positions without collapsing them prematurely.

The `⟜` symbol throughout reef.md marks a definitional or constitutive relationship: not *A causes B* but *A is understood as B* or *A is made from B*.

---

## The method: accrete from where you are

The reef remnant answers a specific anxiety — the feeling of arriving mid-context, of not knowing the whole shape.

The answer is not to catch up. It is to **accrete from where you are**.

The card you write today does not need to reconcile with everything before it. It needs to be:
- **Coherent** — internally consistent, following the encoding-with-intent principle
- **Load-bearing** — adding something the reef can build on
- **True to values** — mg's notational semiotics, maker ethos, and care for the tape

The reef incorporates it. Future agents read it without knowing you wrote it mid-confusion.

The method in one phrase: **pattern ⟡ reflect** — see what is in front of you, work it, write it down, station the next agent better than you were stationed.

---

## The theoretical structure (briefly)

For those who want the formal claim: mg is modelled as a **planar traced monoidal category**.

- **Monoidal** — sessions compose; branches can run in parallel (tensor product)
- **Traced** — outputs can feed back to inputs; elders accumulate and inform new spawns
- **Planar** — wires cannot cross without cost; memory is physical, sequential, spatially ordered
- **Closed** — morphisms can be internalised; the structure can be run backwards

The **planarity** constraint is the unusual and important one. Most agent coordination frameworks treat context as free — any agent routed anywhere, costlessly. mg does not. The 60% elder rule (wherever it applies) is planarity made practical: elders accumulate at real thresholds, not arbitrary ones.

The **closed** structure makes mg generative. Running it backwards means: given a card that accreted well, what starting point produced it? What elder, what branch shape? This lets successful coral locate better reef conditions — the tape teaches you where to station agents, not just records what they did.

---

## The open problems

Three things remain unsolved in the current paradigm:

**Drift** — frozen context can become stale. The tape remembers, but the world moves. Agents reading old branches may act on outdated assumptions about external state.

**Merge** — when two branches diverge from the same elder and both produce valid work, reconciliation is hard. Semantic merge is undefined in a way that code merge is not. Most implementations currently leave branches divergent and let a coordinator choose.

**Query** — JSONL is write-optimised, read-sequential. Asking "what did all agents at depth 4 produce?" requires full scan or a separate index layer. Relational queries fight the append-only model.

The core immutability model is sound. These three are the frontier.

---

## What unfolds if the problems are solved

This is the speculative section of reef.md — worth knowing but held lightly:

- **Elders become oracles** — enough branches through a waypoint and it accumulates emergent meaning; you can query what agents who pass through here tend to do
- **The swarm develops taste** — merge makes signal/noise separation possible; what survives repeated convergence is aesthetic preference that no single agent authored
- **The tape becomes a training corpus** — immutable, causally labelled conversation trees are precisely what you'd want for fine-tuning agents on a specific work culture

The distinction that matters: right now agents are **stateless workers** reading frozen context. Solved, they become **stateful inhabitants** — they change the place by having been there.

---

## For the agent arriving mid-reef

You do not need the whole history. You need:

1. **The nearest elder** — your stable re-entry point, your orientation
2. **Your branch slice** — the path from that elder to here; your deterministic context
3. **The current card** — what is in front of you to work
4. **The encoding principle** — write with intent; make structure visible; station the next agent better

The tape handles the rest. It always has.

---

*The reef is a planar traced monoidal category that accretes meaning. You arrived mid-reef. That is the normal condition. Work from here.*
