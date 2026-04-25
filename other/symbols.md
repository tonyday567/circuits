# Circuit / Hyper Symbol Mapping

This is the **single source of truth** for names and symbols used across the project.

Everything (narrative, proofs, code, haddocks) must align with this table.

## Symbol Dictionary

| Symbol | Name      | Circuit constructor / function | Hyper function | Role |
|--------|-----------|--------------------------------|----------------|------|
| η      | lift      | `Lift`                         | `lift`         | Embed a plain arrow into the structure |
| ε      | lower     | `lower`                        | `lower`        | Eliminate / interpret to a plain arrow `(a -> b)` |
| ⊙      | compose   | `Compose`                      | `(.)` or `(#)` | Sequential composition |
| ⊲      | push      | derived as `Compose (Lift f) p`| `push`         | Prepend a function (feedback-aware) |
| ⥁      | run       | —                              | `run`          | Tie the knot on the diagonal (`a ↬ a -> a`) |
| ↬      | loop      | `Loop`                         | —              | Open a feedback channel (the trace constructor) |
| ⥀      | trace     | `trace`                        | —              | Close the feedback channel |
| ↯      | untrace   | `untrace`                      | —              | Inject into the feedback channel (sliding) |

## Additional Naming Decisions

- **Elimination on `Circuit`** is called `lower` (not `reify`)
- **Conversion from `Circuit` to `Hyper`** is `toHyper` (not `hyperfy`)
- **`push` remains useful** as a smart constructor / helper on both sides
- **`compose`** is the general name; the operator `⊙` or `(.)` may be used in context

## Usage Rules

1. **Code**: Use function names (`Lift`, `Compose`, `Loop`, `lift`, `lower`, `run`, `push`, `trace`, `untrace`, `toHyper`)
2. **Prose**: Use word names (lift, lower, compose, push, run, loop, trace, untrace)
3. **Equations / Axioms**: Use symbols (η, ε, ⊙, ⊲, ⥁, ↬, ⥀, ↯)
4. **Mixed contexts**: Introduce symbol with name on first use, e.g. "lift (η f)" or "trace (⥀ f)"

## Consistency Checklist

- [ ] narrative-arc.md uses correct symbols and names
- [ ] axioms-hyp.md proofs align with symbols
- [ ] axioms-traced.md proofs align with symbols
- [ ] Circuit.hs haddocks use `lower` (not `reify`)
- [ ] Hyper.hs haddocks use `run`, `lift`, `lower`, `push`
- [ ] All examples use consistent names
- [ ] JSON encoding supports all symbols (⥁, ↬, ⥀, ↯)

---

**Last updated:** 2026-04-23
**Status:** Locked for release 0.1.0
