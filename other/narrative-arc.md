A narrative arc for the circuits story.

**The hook.**  
The Fibonacci stream is the classic example that exposes the problem:

```haskell
fibs = Loop (\(fibs, i) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs !! i))
```

A naïve `lower` on `Compose (Loop …) …` produces the wrong answer on the second iteration. The fix is a single extra pattern match — the Mendler case — that makes the sliding axiom hold. Everything else follows from that.

⟜ situate in the language of a stack as described in Section 2.3 of KW.

```
⊙  ⟜  compose ⟜ `H b c -> H a b -> H a c`
⊲  ⟜  push ⟜ `(a -> b) -> H a b -> H a b`
⥁  ⟜  run ⟜ `H a a -> a`
η  ⟜  lift ⟜ `(a -> b) -> H a b`
ε  ⟜  lower ⟜  `H a b -> (a -> b)`
ε . η = id  ⟜ lift ⊢ lower form an adjunction.
```

⟜ show the axioms using `stack`.

```
(f ⊙ g) ⊙ h = f ⊙ (g ⊙ h)
f ⊙ η id = f = η id ⊙ f
η (f . g) = η f ⊙ η g
⥁ (η f) = f (⥁ (η f)) or ⥁ . η = fix
(f ⊲ p) ⊙ (g ⊲ q) = (f . g) ⊲ (p ⊙ q)
⥁ ((f ⊲ p) ⊙ q) = f (⥁ (q ⊙ p))
```

⟝ simplify

The fundamental axiom is the adjunction unit: `ε . η = id`. This forces `run (lift f) = fix f` as a derived consequence, not a primitive requirement [see other/hasegawa.md]. Therefore:

```
⥁      =  fix . ε   -- run as a compound (derived from adjunction)
ε . η  =  id         -- adjunction unit (fundamental)
fix (ε ((f ⊲ p) ⊙ q))  =  fix (f . ε (q ⊙ p))   -- sliding axiom
```

⟝ initial GADT

After substitution, the six axioms partition into three structural roles:

The free category: associativity, identity and functoriality of lift.

```
(f ⊙ g) ⊙ h = f ⊙ (g ⊙ h)
f ⊙ η id = f = η id ⊙ f
η (f . g) = η f ⊙ η g
```

A faithful embedding of an adjunction.

```
ε . η  =  id
```

Tracing

```
(f ⊲ p) ⊙ (g ⊲ q) = (f . g) ⊲ (p ⊙ q)
fix (ε ((f ⊲ p) ⊙ q))  =  fix (f . ε (q ⊙ p))
```

⟝ push is compound

Push = Compose . Lift

axiom 4: centrality

```
(f ⊲ p) ⊙ (g ⊲ q) = (f . g) ⊲ (p ⊙ q)
(η f ⊙ p) ⊙ (η g ⊙ q) = η (f . g) ⊙ (p ⊙ q)
(η f ⊙ p) ⊙ η g = η (f . g) ⊙ p
```

axiom 6 - Looping | Braiding | Tying knots.

```
⥁ ((f ⊲ p) ⊙ q) = f (⥁ (q ⊙ p))
fix (ε ((f ⊲ p) ⊙ q))  =  fix (f . ε (q ⊙ p))
fix (ε (η f ⊙ (p ⊙ q))) = fix (f . (q ⊙ p))
```

The sliding axiom of the trace in traced categories, in fixpoint form.

**Why Loop is forced.**
The naïve GADT (`Lift` + `Compose` only) satisfies axioms 1–5 but not 6. The fixpoint equation that appears has `η f` on the left and a swapped `q ⊙ p` on the right. Canceling `fix` is only valid when both sides share the same feedback type — witnessed by a tensor `t`. That is exactly what `Loop` carries.

The computational content is the Mendler case (directly analogous to `mcata` / `fold` + `mapFold` in the recursion-schemes literature):

```haskell
lower (Compose (Loop f) g) = trace (f . untrace (lower g))
```

We inspect one syntactic layer before recursing. This single extra pattern match turns sliding into a structural property of `lower` and prevents the degenerate model.

Solving for these axioms requires:

- an additional GADT, called `Loop`, which contains a tensored arrow where the tensor is hidden by the `Loop`.

```haskell
Loop :: arr (t a b) (t a c) -> Circuit arr t b c
```

- a way to implement our recast axiom 6.

```haskell
-- closing off the tensor
trace :: arr (t a b) (t a c) -> arr b c
-- providing a slippery non-hidden channel.
untrace :: arr b c -> arr (t a b) (t a c)

-- eliminates the tensor
lower (Loop k) = trace k

-- if a Loop appears on the left, slide the right one through the loop.
lower (Compose (Loop f) g) = trace (f . untrace (lower g))
```

⟝ Circuit

A `Circuit arr t a b` is the free traced monoidal category over base `arr` with tensor `t` (where `t` carries a `Trace` instance, i.e. costrong). When `arr = (->)` and `t = (,)` this is a **cartesian traced category** (symmetric monoidal + diagonals).

`lower` is the unique traced functor out of this free object. It interprets:

- `Lift`          → base arrow (strict monoidal functor)
- `Compose`       → sequential composition (category laws)
- `Loop k`        → the trace operator (feedback channel)
- Mendler case    → naturality in X / sliding axiom of the trace [see other/hasegawa.md and other/axioms-traced.md]

```
η   ⟜  Lift
ε   ⟜  lower
⊙   ⟜  compose
↬   ⟜  Loop
⥀   ⟜  trace
↯   ⟜  untrace
```

```
ε (η f)       =  f
ε (↬ f)       =  ⥀ f
ε (↬ f ⊙ g)   =  ⥀ (f . ↯ (ε g))
ε (f ⊙ g)     =  ε f . ε g
```

The composed semantic stack in lower:

```
ε (η f) =  f ⟜ **Coyoneda** — Lift as deferred function application, the free functor, `lower . Lift = id`
ε (f ⊙ g) =  ε f . ε g ⟜ **Free category** — Lift id as identity and Compose as deferred function composition.
ε (↬ f)       =  ⥀ ⟜ **Free traced category** with deferred choice of ⥀
ε (↬ f ⊙ g)   =  ⥀ (f . ↯ (ε g)) ⟜ deferred implementation of sliding.
```

**Categorical status (precise).**
The same structure appears when we name the constructors and their interpretations explicitly:

- `Lift`          → base arrow (strict monoidal functor)
- `Compose`       → sequential composition (category laws)
- `Loop k`        → the trace operator `trace k` (feedback channel)
- Mendler case    → naturality/sliding axiom of the trace (`trace (f . untrace g) = trace f . g`)

`Circuit arr t` is the **free traced monoidal category** generated by the base category `arr` with respect to the tensor `t`. This is why the six LKS axioms hold and why there is no degenerate model once `Loop` + the Mendler case are present.

⟜ The Hyper adjunction

Circuit is the **initial** (free, intensional) encoding; Hyper is the **final** (coinductive, extensional) encoding. A `Hyper` is a Church encoding of a `Circuit`:

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

The unique traced functor `toHyper :: Circuit (->) t a b -> Hyper a b` satisfies the triangle: when you eliminate a `Circuit` via `lower`, you get the same result as converting to `Hyper` and then eliminating via `lower`. This triangle identity shows that the two elimination paths (direct on `Circuit`, or via `Hyper`) produce the same output. Hyper gives you sliding "for free" in the resolution of the fixpoint because the continuation `Hyper b a` is the feedback channel — every composition threads it automatically. For the categorical foundations of this structure, see [other/kan-extension.md](kan-extension.md).

⟜ reflection without remorse

Hyper is like Codensity but also the stack language of GHC.

## circuits

Circuit is intensional ⟜ code with intent.

Initial objects are maximally flexible, highly compositional, statically represented.

⟝ traced axiom

```
⥀ (f . ↯ g) = ⥀ f . g
trace (f . untrace g) = trace f . g
```

How to slide into a trace.

⟝ Tensor as a useful abstraction

**Costrong / `(,)`:** feedback and output exist in parallel. Both sides progress lock-step. Suitable for dataflow, zipping, true concurrency.

**Cochoice / `Either`:** sequential handoff — taking turns. Only one participant acts per step. Suitable for coroutines, schedulers, state machines.

cochoice - taking turns
costrong - holding hands

KW describe an implementation of pipes with the `(,)` tensor rather than `Either` (which is what it is exactly).
