# Some More Knots

<div align="center">

✦ · ✧ · ✦

*Our adventure concludes; the library works; the architecture stands; the making continues.*

**[⟵ Prev: No Remorse, Once Removed](05-no-remorse-once-removed.md)**

</div>

---

## Where We Are

The library has three GADT layers (`Free`, `Circuit`, `Net`), three
interpreters (`runFree`, `freeze`, `melt`), and two final encodings
(`Hyper` and `Queue`). The pieces fit.

The `other/` chapters trace the arc: from the five marks on `Hyper`
through the GADT construction, the triangle identity, the tensor
choice, the RwR analogy, to the applications below. The narrative
is honest about the evolutionary path — `Hyper` came first, `Free`
was discovered later, and some early claims ("Knot dissolves into
Hyper") have been refined.

---

## What's Built

### `foldH` — coroutining folds

Two folds share a continuation, interleaving element-by-element.
`foldr'` and `foldh'` are the same λ-term with different generators —
`(:)` attaches to the outside, `push` threads inside through the
continuation channel. Full derivation in `examples/proequip.md`.

### Parsers — `Circuit (->) Either [s] (These a [s])`

A state-based parser on the `Either` tensor. `These` distinguishes
three outcomes: consumed-some, consumed-everything, no-progress.
`<|>` uses `Knot` for alternation. Validated against `regex-applicative`.

### While-loops — `Circuit (->) Either a b`

`loop`, `while`, `until`, `for` — all `reify (Knot step') s0` with
different `step'` bodies. Four patterns, one constructor.

### Effectful loops — `Circuit (Kleisli IO) Either a b`

`Trace (Kleisli IO) Either` uses GHC's `prompt#`/`control0#` for
delimited continuations — constant stack regardless of iteration count.

### Pipes — `Circuit (Kleisli m) Either ~ Pipe m`

Await is `Left`, yield is `Right`. The `Either` tensor's handoff
matches `Proxy`'s `Request`/`Respond` alternation.

### Metering — `circuits-meter`

Performance measurement as a `Circuit`. A `Meter` introduces a state
wire before a computation and reads it after. Calibrated against
criterion — `ticksN` reproduces criterion's numbers within 10%.

### Sibling libraries

- **circuits-parser** — production parser library, dependency of `chart-svg`
- **circuits-io** — bidirectional channels, producer/consumer, resource-bracketed IO
- **circuits-meter** — circuit measurement with delimited-continuation timing
- **circuits-ad** — reverse-mode AD via `transpose` on `Net (Dagger Diff)`

---

## The Examples Directory

| card | what it shows |
|------|---------------|
| `lift-trace-commute.md` | `lift . trace = trace . lift` — the traced functor lemma |
| `circuits.md` | imports, three tags, minimal example |
| `words.md` | word-count pipeline with metering |
| `circuit.md` | `Circuit` GADT, `reify` |
| `hyper.md` | `Hyper` construction and elimination |
| `while.md` | loop/while/until/for on `Either` |
| `parser.md` | `Either`+`These` parser combinators |
| `pipes.md` | `Pipe m` isomorphism |
| `resource-io.md` | delimited continuations, prompt/control0 |
| `ambient.md` | `ambient`, state threading |
| `encode-either.md` | `encodeEither`, `runEither` |
| `elgot-abacus.md` | Elgot iteration |
| `proequip.md` | coroutining folds, double category framing |
| `optics.md` | profunctor optics on Circuit |
| `lawvere.md` | comparative engineering with Lawvere |

---

## References

- [Launchbury, Krstic & Sauerwein (2013)](https://doi.org/10.4204/eptcs.129.9) — coroutining folds with hyperfunctions
- [Kidney & Wu (2026)](https://doi.org/10.1145/3776649) — hyperfunctions: communicating continuations
- [Van der Ploeg & Kiselyov (2014)](https://doi.org/10.1145/2633357.2633360) — Reflection Without Remorse
- `circuits-parser` — production parser library on Circuit
- `circuits-io` — bidirectional channels and IO loops
- `circuits-meter` — circuit measurement and performance
