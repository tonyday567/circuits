⟝ lawvere

# What's Next for Circuit? Comparative Engineering with Lawvere

For Circuit's current structure see [proarrow.md](proarrow.md) — `Knot` as a 2-cell.
For Lawvere see the [lawvere repo](https://github.com/jameshaydon/lawvere)
(James Haydon, 2020) and `~/other/lawvere/`.
This card reads Lawvere as a **specification of what Circuit doesn't yet have**
and asks what structural extensions are natural next moves for Circuit.

---

## The Gap: Traced Monoidal ≠ Cartesian Closed

Circuit is a **free traced monoidal category**, represented by the `Trace` datatype. Its two constructors:

```haskell
data Trace t arr a b where
  Arr     :: arr a b -> Trace t arr a b
  Knot    :: arr (t a b) (t a c) -> Trace t arr b c
```

Lawvere's evaluator implements a **cartesian closed category**. Its `Expr`
type includes what Circuit explicitly lacks:

```haskell
data Expr
  = ...
  | Curry   Label Expr   -- a → (b ⇒ c)  from  a × b → c
  | UnCurry Label Expr   -- a × b → c    from  a → (b ⇒ c)
```

`Curry` and `UnCurry` are the exponential adjunction. Circuit has no
exponential object `a ⇒ b`, no `curry`/`uncurry` constructors. This is
not an oversight — it's a different categorical class. But it's also
the most natural structural extension.

Lawvere is *ahead* of Circuit in one dimension: it has exponentials.
Circuit is *ahead* of Lawvere in another: it has a proper trace constraint
(`Traced arr t`) and the Mendler case that enforces the sliding axiom — see
[proarrow.md](proarrow.md). Lawvere's `Fix` uses Haskell's `mfix`, which
assumes recursion without constraining it.

The productive question: **what structural 2-cells does Circuit need next,
and what does Lawvere's design tell us about what those look like?**

---

## Structural 2-Cells: Knot and Curry

From [proarrow.md](proarrow.md): `Knot` is a 2-cell in `Prof(Hask)` —
a `Cell f g h j` where `f = g = id`, `h = arr ∘ (t a)`, `j = Trace t arr`.
It transforms tensor-wrapped arrows into `Trace` arrows, modifying the
wiring by adding a feedback loop.

```haskell
-- Knot as a Cell (specialised):
--   Cell id id (arr ∘ (t a)) (Trace t arr)
Knot :: arr (t a b) (t a c) -> Trace t arr b c
```

The Mendler case in `run` is the naturality condition for this 2-cell —
`coact` commuting with profunctor composition.

**What about `Curry`?**

`Curry` is also a 2-cell, but of a different kind. Where `Knot`
transforms `arr → Trace` (changing the target category), `Curry`
transforms `Trace → Trace` while changing the object structure:

```haskell
-- Curry as a Cell candidate:
--   Cell (t a) (Exp a) (Trace t arr) (Trace t arr)
Curry :: Trace t arr (t a b) c -> Trace t arr b (Exp a c)
```

The domains differ:
- `Knot`: takes an `arr` morphism, returns a `Trace` morphism.
  Introduces a new wiring primitive (feedback).
- `Curry`: takes a `Trace` morphism, returns a `Trace` morphism.
  Introduces a new *object* constructor (`Exp`) and reshapes the
  domain/codomain.

`Knot` adds a **structural combinator** (trace). `Curry` adds both a
**structural combinator** (curry/uncurry) and a **new type constructor**
(`a ⇒ b`). The exponential object doesn't exist in the base category —
it's constructed by the free category, just as `Trace t arr a b` is a
new type of arrow not present in `arr`.

### What Adding Exponentials Would Look Like

A cartesian closed extension of Circuit:

```haskell
data ExpCircuit arr t a b where
  EArr      :: arr a b -> ExpCircuit arr t a b
  EKnot     :: arr (t a b) (t a c)
            -> ExpCircuit arr t b c
  -- sequential composition is (.) or (>>>)
  -- NEW: exponential adjunction
  ECurry    :: ExpCircuit arr t (t a b) c
            -> ExpCircuit arr t a (Exp b c)
  EUncurry  :: ExpCircuit arr t a (Exp b c)
            -> ExpCircuit arr t (t a b) c

-- The exponential object type
data Exp a b    -- internal hom, constructed by the free category
```

Or equivalently, keep `Trace` unchanged and add `Curry`/`Uncurry` as
a property of the `Traced` constraint or a new typeclass:

```haskell
class (Traced arr t) => Closed arr t where
  type Exp arr t a b
  curry   :: Trace t arr (t a b) c -> Trace t arr a (Exp arr t b c)
  uncurry :: Trace t arr a (Exp arr t b c) -> Trace t arr (t a b) c
```

The `run` function would need a `Closed` constraint in addition to
`Traced` — expanding the typeclass footprint of Circuit's runtime.

### Lawvere's Curry/UnCurry in Practice

In Lawvere's evaluator, `Curry` and `UnCurry` manipulate the record
structure directly:

```haskell
-- Lawvere.Eval
Curry lbl e ->
  let f = evalAr tops e
   in \case
        Rec r -> pure . VFun $ \v -> f (Rec (Map.insert lbl v r))
        _ -> panic "bad curry"

UnCurry lbl e ->
  let f = evalAr tops e
   in \case
        Rec r | Just v <- lkp lbl r -> do
          res <- f (Rec (Map.delete lbl r))
          case res of
            VFun ff -> ff v
            _ -> panic "bad uncurry"
        _ -> panic "bad uncurry"
```

`Curry` introspects the record: adds a field to produce a closure (`VFun`).
`UnCurry` does the reverse: extracts a field, applies the curried function.
Lawvere's `Val` type has `VFun Fun` for closures — the exponential object
is represented at the value level, not the type level.

Circuit would make this type-level: `Exp a b` would be a Haskell type,
not a `Val` constructor. The adjunction would be enforced by the `Closed`
typeclass rather than by pattern-matching on `VFun`.

---

## The Correspondence (Revised)

| Lawvere constructor | Circuit equivalent | What it is |
|---|---|---|
| `BinComp` | `(.)` / `(>>>)` | 1-cell composition |
| `Cone`, `Proj`, `Distr` | `dimap`, `rmap` on `Trace` | Product structure (via Profunctor) |
| `CoCone`, `Inj`, `Distr` | `dimap` on `Knot` with `Either` | Coproduct structure |
| `Fix` | `Knot` | **2-cell: trace** |
| `Curry`, `UnCurry` | *missing* | **2-cell: exponential** |
| `Lit`, `Top`, `EPrim` | `Arr` | Embed base arrow |
| CAM bytecode | `run` | Runtime / reification |
| `bill` REPL | GHCi + `run` | Interactive use |

---

## What's Ahead, What's Behind

**Circuit is ahead on trace.** The `Traced` constraint and the Mendler case
in `run` are properly axiomatised. Lawvere's `Fix` uses `mfix` — it assumes recursion works,
doesn't constrain it. Lawvere identified the need (Haydon's issue #16).
Circuit provides the mechanism.

**Lawvere is ahead on exponentials.** `Curry`/`UnCurry` are first-class
constructors. Circuit has no exponential object, no `curry`/`uncurry`.
Adding them would make Circuit cartesian closed — a strictly larger
categorical class than traced monoidal.

**The engine under both is a free category with structural 2-cells.**
`Knot` is the first 2-cell — the one that makes the category traced.
`Curry`/`Uncurry` would be the second — the one that makes it closed.
What others? What's the 2-cell for [distributive categories](https://ncatlab.org/nlab/show/distributive+category)?
For [linear logic](https://ncatlab.org/nlab/show/linear+logic)?
The design space opens from here. For evidence that the pattern generalises
beyond the Circuit-Lawvere pair, see [sysl examples](https://github.com/tonyday567/sysl)
— System L wired to Circuit, adding ⊸ and ⨟ to the ladder.

---

## Summary

1. Circuit is **traced monoidal**; Lawvere is **cartesian closed**. The gap is
   `Curry`/`UnCurry` — exponential adjunction.
2. `Knot` is a **2-cell** (trace cell), proven in [proarrow.md](proarrow.md).
   `Curry` is also a 2-cell candidate — `Cell (t a) (Exp a)` on `Trace`.
3. Adding exponentials to Circuit means either a new GADT (`ExpCircuit`)
   or a new typeclass (`Closed arr t`) with `type Exp` and `curry`/`uncurry`.
4. Circuit's `Traced` constraint is ahead of Lawvere's ad-hoc `mfix` recursion.
   Lawvere's `Curry`/`UnCurry` is ahead of Circuit — it has no equivalent.
5. The design direction: Circuit as a **free category with accumulating
   structural 2-cells** — trace, exponential, distribution, linear logic.
   Each 2-cell adds a constructor. Each requires a constraint. The engine is
   the same.

---

## References

- [Haydon, lawvere](https://github.com/jameshaydon/lawvere) — categorical
  programming language with effects; CAM compiler. Source at `~/other/lawvere/`.
- [Haydon, issue #16](https://github.com/jameshaydon/lawvere/issues/16) —
  the trace question; initial category inference.
- [Visscher, proarrow](https://github.com/sjoerdvisscher/proarrow/) —
  `Strong`/`Costrong` on profunctors; `SelfAction`.
- [Milewski, Profunctor Equipment](https://bartoszmilewski.com/2026/05/16/profunctor-equipment-in-haskell/) —
  `Cell f g h j` encoding for proarrow equipments.
- [proarrow.md](proarrow.md) — `Traced` ≅ `Strong + Costrong` under self-action;
  Knot as 2-cell.
- [Joyal, Street & Verity (1996)](https://doi.org/10.1017/s0305004100074338) —
  traced monoidal categories.
- `src/Circuit.hs` — `Arr`, `Knot`, `run`.
- `src/Circuit/Traced.hs` — `Traced` typeclass and instances.
- `~/other/lawvere/src/Lawvere/Expr.hs` — `Curry`, `UnCurry` constructors.
- `~/other/lawvere/src/Lawvere/Eval.hs` — `evalAr` on `Curry`/`UnCurry`.
- [nLab: cartesian closed category](https://ncatlab.org/nlab/show/cartesian+closed+category)
- [nLab: distributive category](https://ncatlab.org/nlab/show/distributive+category)
