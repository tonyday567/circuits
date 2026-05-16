⟝ hyperfunctions

# Circuit.Hyper ⟜ Control.Monad.Hyper — A Comparative Analysis

Two libraries, same newtype, divergent designs. This card maps the shared
territory and the choices that separate them. For the operations, instances,
and capabilities of Circuit.Hyper itself, see `examples/hyper.md`.

## The Shared Core

Both libraries define the same type:

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

A hyperfunction from `a` to `b` is a function that, given a continuation from
`b` back to `a`, produces a `b`. The self-referential type wraps feedback into
the structure itself — the continuation carries the dual arrow, and composition
of hyperfunctions automatically threads feedback without explicit loop
constructs.

## The Divergence

| Aspect            | `Circuit.Hyper` (circuits)              | `Control.Monad.Hyper` (Kmett)         |
|-------------------|-----------------------------------------|---------------------------------------|
| **Encoding role** | Final object of traced monoidal cats    | Church encoding / final coalgebra     |
| **`run`**         | `invoke h (Hyper run)` — self-knot      | `invoke f id` — identity continuation |
| **Constant**      | `base`                                  | `pure`                                |
| **Embedding**     | `lift` (recursive)                      | `arr = fix . push`                    |
| **Observation**   | `lower`                                 | `project`                             |
| **Instances**     | Category, Profunctor, Functor           | + Arrow, ArrowKnot, Monad, Zip        |
|                   | Applicative, Monad                      | + ana, cata, unroll, roll, fold       |
| **Dep chain**     | base + profunctors                      | base + profunctors + adjunctions + …  |

## `run` — Two Different Operations

This is the deepest difference:

```haskell
-- circuits: self-referential knot
run :: Hyper a a -> a
run h = invoke h (Hyper run)

-- Kmett: invoke with identity continuation
run :: Hyper a a -> a
run f = invoke f id
```

In circuits, `run` ties the hyperfunction to itself — a true fixed point.
`run (lift (+1))` diverges because `(+1)` has no fixed point.

In Kmett, `run (arr f) ≡ fix f` — the hyperfunction is invoked with the
identity hyperfunction as its continuation, which unfolds the computation.
`run (arr (+1))` also diverges, but via a different mechanism.

The difference matters when the continuation is non-trivial. Consider a
hyperfunction that inspects its continuation:

```haskell
-- This hyperfunction asks: "what would my continuation do with 5?"
query :: Hyper Int Int
query = Hyper $ \k -> invoke k (base 5)
```

Under circuits `run`: `run query` = `invoke (Hyper run) (base 5)` = 5.
Under Kmett `run`: `run query` = `invoke (arr id) (base 5)` = `project id 5` = 5.
Same result here, but the operational paths differ.

## The fold/build Pattern

Kmett's library includes a classic fold/build fusion system adapted to
hyperfunctions:

```haskell
fold :: [a] -> (a -> b -> c) -> c -> Hyper b c
fold []     _ n = pure n
fold (x:xs) c n = push (c x) (fold xs c n)

build :: (forall b c. (a -> b -> c) -> c -> Hyper b c) -> [a]
build g = run (g (:) [])
```

This is Church encoding of lists via hyperfunctions. `fold` materialises a
list into a hyperfunction; `build` extracts a list by running the
hyperfunction with `(:)` as the combinator. The fusion law `fold . build ≡ id`
holds under "nice conditions" (the hyperfunction must be parametric).

In Circuit.Hyper, the same pattern is expressible directly:

```haskell
foldC :: [a] -> (a -> b -> c) -> c -> Hyper b c
foldC [] _ n = base n
foldC (x:xs) c n = push (c x) (foldC xs c n)

buildC :: (forall b c. (a -> b -> c) -> c -> Hyper b c) -> [a]
buildC g = run (g (:) [])
```

## The Philosophical Tension

Circuit.Hyper originally claimed "Hyper is invariant… does not admit Functor,
Applicative, or Monad instances." This is **nominally true** — the type
parameter `b` appears in both covariant and contravariant positions in the
unfolding of `invoke`. A strict language would indeed reject `Functor`.

Kmett's instances are **coinductively true** — they work because lazy
evaluation only forces finitely many layers. Each `fmap` application wraps
another coinductive layer rather than structurally transforming the type.

The `Circuit.Hyper` module now provides both perspectives:
- The Profunctor/Functor/Applicative instances for those who want the Kmett
  style
- The coinductive approach that treats observations as finite unfoldings

This reflects a broader pattern in the circuits library: **the initial
encoding (Circuit GADT) is the ground truth** — Functor, Applicative, Monad
are straightforward structural instances. **The final encoding (Hyper) is
the semantic reflection** — it compresses feedback into the type, and
instances become coinductive loops rather than structural recursion.

## References

- [Zip fusion with Hyperfunctions](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.36.4961&rep=rep1&type=pdf)
- [Categories of processes enriched in final coalgebras](https://link.springer.com/chapter/10.1007/3-540-45315-6_20)
- [Seemingly Impossible functional programs](http://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/)
- [Hyperfunctions by Donnacha Oisín Kidney](https://doisinkidney.com/posts/2021-03-14-hyperfunctions.html)
- Kmett, E. (2015). Control.Monad.Hyper
