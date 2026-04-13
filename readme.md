# yarn: traced monoidal categories and hyperfunctions

A system for understanding and building with **free traced categories** and their final encodings as **hyperfunctions**.

**Status:** Research-grade, working towards stability.

---

## Core Research

**The foundation:** TracedA (initial), HypA (final), and their mutual recursion

| Component | Location | Role | Status |
|-----------|----------|------|--------|
| **TracedA** | src/Traced.hs | Free traced monoidal category (GADT) | ✓ |
| **HypA** | src/Hyp.hs | Final encoding as mutual recursion | ✓ |
| **Bridge** | src/Hyp.hs, src/Traced.hs | toHyp/fromHyp isomorphism | ✓ |
| **Kan extension** | loom/hyp-traced-bridge.md | HypA = Fix(Ran(Const a)(Const b)) | ◊ |

**The axioms:** Traced monoidal category semantics

⊢ [loom/traced-axioms.md](other/traced-axioms.md) — JSV axioms with proofs
⊢ [loom/lks-7-8-axioms.md](other/lks-7-8-axioms.md) — LKS axioms, stream model
⊢ [loom/kidney-wu-2.3-streams.md](other/kidney-wu-2.3-streams.md) — Kidney-Wu interface and continuations

**The Mendler inspection:** The critical case that keeps TracedA from degenerating

◊ Formalize as naturality condition of Kan extension
◊ Link to reflection-without-remorse literature (van der Ploeg & Kiselyov 2014)

---

## Instances and Tensors

**Cartesian (simultaneous channels):**
- Tensor: `(,)` (Costrong)
- trace: `unsecond` (lazy product knot)
- operational: dataflow, concurrent
- status: ✓ working

**Cochoice (sequential handoff):**
- Tensor: `Either` (Cochoice)
- trace: `unright` (while-loop)
- operational: coroutines, schedulers
- status: ✓ working

**Multi-way dispatch:**
- Tensor: `These` (planned)
- trace: multi-slot output
- operational: System L, effect dispatch
- status: ◊ Traces.hs exists, needs integration

**Profunctor instances:**
- Functor, Profunctor, Applicative, Monad on TracedA
- status: ✓ implemented in src/Traced.hs

---

## Live Research Threads

⊢ **Int(C) completion** — Climb the Joyal-Street-Verity construction
  ◊ Int(TracedA) is the free compact closed category
  ◊ Objects: pairs (a+, a-)
  ◊ Morphisms: TracedA (a+, b-) (a-, b+)
  ◊ Cup/cap: feedback loops that close on themselves
  ◊ Status: src/IntC.hs exists, cups/caps/composition need testing

⊢ **Geometry of Interaction** — Connection to callCC, shift/reset
  ◊ Int(TracedA) as GoI construction (conjecture)
  ◊ RTS-level delimited continuations (GHC 9.6+)
  ◊ other/GoIRTS.hs: working primitives (prompt, control0, callCC)
  ◊ Status: ◊ primitives exist, integration path unclear

⊢ **Box / profunctor effects** — Traced duality in effect systems
  ◊ Box (Committer, Emitter) from ~/haskell/box/
  ◊ glue as CCC counit
  ◊ traced feedback as resource duality
  ◊ Status: ◊ discovered, needs architecture work

⊢ **Costrong/Cochoice duality** — Semantic differences made concrete
  ◊ Same TracedA term under (,) vs Either tensor
  ◊ Producer-consumer or scheduler example
  ◊ Operational cost differences (lazy vs loop)
  ◊ Status: documented in loom/, needs code example

⊢ **Hasegawa cyclic sharing** — Recursion from trace, not fixed-point
  ◊ small letrec: Knot vs ordinary recursion
  ◊ Resource duplication in fix vs none in trace
  ◊ Grounds "why trace matters"
  ◊ Status: ◊ example needs writing

⊢ **Graded structure** — Counting Knot depth
  ◊ Grading gives refinement types for traced terms
  ◊ Okasaki queue methods implications
  ◊ Status: ◊ noted, not formalized

⊢ **Kidney-Wu 2026 examples** — Concrete patterns
  ◊ Breadth-first search via Hofmann
  ◊ Concurrency scheduler
  ◊ Mapping TracedA/HypA to real code
  ◊ Status: ◊ theory present, code needed

⊢ **Proxy/streaming isomorphism** — Type-level equivalence
  ◊ Proxy m a b vs TracedA m t a b
  ◊ m threading outside vs inside traced structure
  ◊ streaming library as better starting point
  ◊ Status: ◊ conjecture, not proven

---

## Modules

**Source:**
- `src/Traced.hs` — TracedA GADT, run with Mendler case, instances
- `src/Hyp.hs` — HypA newtype, ⊙ composition, bridge to/from TracedA
- `src/Hyp/Channel.hs` — Producer, Consumer, Channel patterns, Co coroutine
- `src/IntC.hs` — Int(TracedA) construction, duals, cup/cap, composition
- `src/Traces.hs` — These-based multi-slot tracing (experimental)

**Research & Notes:**
- `other/` — All loom files, duplicated here for cohesion
  - hyp-formulae.md — LKS axioms with semantics
  - hyp-narrative.md — Initial vs Final encodings, deforestation
  - hyp-traced-bridge.md — Axiom correspondence, Kan extension
  - traced-axioms.md — Full proofs of JSV/Hasegawa axioms
  - lks-7-8-axioms.md — Stream model, free traced category GADT
  - kidney-wu-2.3-streams.md — Kidney-Wu notation and bridge law
  - nlab-traced-monoidal-category.md — Reference
  - GoIRTS.hs — Delimited continuations (GHC 9.6+)

---

## External R&D

**~/haskell/box/** — Profunctor effect system
- Committer/Emitter duality
- Box as product of both
- glue as feedback loop primitive
- Reference: Box library on Hackage
- **Connection to yarn:** TracedA feedback channel ≈ Box duality

**~/haskell/sysl/** — System L interpreter using TracedA
- Commands, Values, Terms, Coterms
- Multi-slot dispatch
- Translation to Traced
- Consumer of yarn, test case
- **Connection:** These tensor natural home for multiple output slots

**~/mg/loom/** — Unified research pack
- All notes, all axioms, all proofs
- Originally duplicated in yarn/other/, consolidating

---

## Short-term Work

⊢ Consolidate & trim
  ◊ Move loom → yarn/other/ (done in copy)
  ◊ Delete old BoxTraced attempt
  ◊ Evaluate Traces.hs: keep or move?
  ◊ Decide: GoIRTS stays or satellites to separate project?

⊢ Annotate living code
  ◊ Do not add comments until it settles (churn cost too high)
  ◊ Flag where Haskell can't enforce axioms (comment when finalized)
  ◊ Three-mode examples (math + diagram + code) when mature

⊢ Test tensor instances
  ◊ (,) Costrong — ✓ exists
  ◊ Either Cochoice — ✓ exists
  ◊ These dispatch — ◊ implement side-by-side
  ◊ Concrete: produce-consume example under all three

⊢ Int(C) validation
  ◊ Cup/cap types and operations
  ◊ Composition correctness
  ◊ Embed TracedA → Int(TracedA)
  ◊ Test: simple morphism pair, round-trip

⊢ Box integration
  ◊ Understand glue as CCC counit
  ◊ Map Committer ↔ Covariant endpoint
  ◊ Map Emitter ↔ Contravariant endpoint
  ◊ Prototype: glue-traced operation

---

## Deforestation & Runtime

The power of the HypA encoding:

- Church encoding of TracedA: Church-encoded lists vs cons cells
- GHC simplifier can fuse away intermediate structure under `INLINE`
- Axiom equations are rewrite rules
- Mendler case is the critical fusion rule that keeps Knot from allocation
- Result: traced feedback costs nothing at runtime under optimization

**References:**
- van der Ploeg & Kiselyov, "Reflection without Remorse" (Haskell 2014)
- GHC fusion rules and deforestation
- Build/foldr stream fusion analogy

---

## References

**Foundational:**
- Kelly & Laplaza, "Coherence for compact closed categories" (JPAA 1980)
- Joyal, Street & Verity, "Traced monoidal categories" (Math. Proc. Camb. 1996)
- Hasegawa, "Recursion from cyclic sharing: traced monoidal categories" (1997)
- Abramsky & Coecke, "A categorical semantics of quantum protocols" (LICS 2004)
- Launchbury, Krstic & Sauerwein, "Lazy functional reactive programming" (JFP 2013)

**Contemporary:**
- Kidney & Wu, "Hyperfunctions and the monad of streams" (2026)
- Balan & Pantelimon, "The hidden strength of costrong functors" (2025)
- van der Ploeg & Kiselyov, "Reflection without remorse" (Haskell 2014)

---

**Status:** Live research. Every iteration tightens scope. This readme is the task list.

