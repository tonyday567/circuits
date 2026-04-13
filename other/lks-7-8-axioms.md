# Hyperfunctions Axiomatically & Stream Model (Launchbury, Krstic & Sauerwein)

**Source:** Launchbury, Krstic & Sauerwein — Sections 7 & 8

---

## 7 Hyperfunctions Axiomatically

Moving from explicit model-theoretic view to an axiomatic approach allows us to consider alternative models and more efficient implementations.

We regard `H a b` as describing the set (or CPO) of arrows in a hyperfunction category. We require the following operations:

```haskell
(#)    :: H b c -> H a b -> H a c
lift   :: (a -> b) -> H a b
run    :: H a a -> a
(<<)   :: (a -> b) -> H a b -> H a b
```

which must satisfy these conditions:

**Axiom 1** (Associativity)
```
(f # g) # h = f # (g # h)
```

**Axiom 2** (Identity)
```
f # self = f = self # f
```

where `self :: H a a` is defined by `self = lift id`

**Axiom 3** (Lift is Functor)
```
lift (f . g) = lift f # lift g
```

**Axiom 4** (Run is Fixed-Point)
```
run (lift f) = fix f
```

**Axiom 5** (Lifting with Prefix)
```
(f << p) # (g << q) = (f . g) << (p # q)
```

**Axiom 6** (Lift Equation)
```
lift f = f << lift f
```

**Axiom 7** (Run with Prefix)
```
run ((f << p) # q) = f (run (q # p))
```

### Derived Operations

These axioms make hyperfunctions into a category. The `lift` function is a functor from the base category into the hyperfunction category. We can define:

```haskell
invoke :: H a b -> H b a -> b
invoke f g = run (f # g)

base :: b -> H a b
base k = lift (const k)

mapH :: (a' -> a) -> (b -> b') -> H a b -> H a' b'
mapH r s f = lift s # f # lift r
```

`H` is contravariantly functorial in its first argument and covariantly in its second.

### Theorem 3: Lift is Faithful

```haskell
project :: H a b -> (a -> b)
project q x = invoke q (base x)
```

**Proof:** It suffices to show `project (lift f) = f`:

```
project (lift f) x
= invoke (lift f) (base x)
= run (lift f # base x)
= run ((f << lift f) # base x)          [by Axiom 6]
= f (run (base x # lift f))             [by Axiom 7]
= f (run (lift (const x) # lift f))
= f (run ((const x << base x) # lift f))
= f (const x (run (lift f # base x)))
= f x
```

Thus `lift` is faithful: if `lift f = lift g` then `f = g`.

---

## 8 A Stream Model for H

We now investigate alternative models for `H`. The elements behave like a stream of functions: initial work is performed, then remaining work is delayed and given to the continuation.

Work proceeds piece-by-piece with interruptions allowing interleaved computation.

### The L Model

```haskell
data L a b = (a -> b) :<<: L a b

invoke :: L a b -> L b a -> b
invoke fs gs = run (fs # gs)

(#) :: L b c -> L a b -> L a c
(f :<<: fs) # (g :<<: gs) = (f . g) :<<: (fs # gs)

self :: L a a
self = lift id

lift :: (a -> b) -> L a b
lift f = f :<<: lift f

base :: a -> L b a
base x = lift (const x)

(<<) :: (a -> b) -> L a b -> L a b
(<<) = (:<<:)

run :: L a a -> a
run (f :<<: fs) = f (run fs)
```

### Key Properties

**Model Behavior:** `run` is more naturally primitive than `invoke` in the L model (opposite of the function-space model H).

**Identity and Associativity:** Laws between `#` and `self` are straightforward via fixed-point induction and composition properties. (Contrast: the H model required challenging proofs.)

**Stream as Fixpoint:** The stream of functions acts like a fixpoint waiting to happen. Two scenarios:
1. Functions are interspersed with another stream (via `#`)
2. All functions are composed together (via `run`)

`run` ties the recursive knot and removes opportunities for further coroutining.

### Fold Behavior

The fold function (defined in terms of `<<` and `base`) behaves as:

```haskell
fold [x1, x2, x3] c n
= c x1 :<<: c x2 :<<: c x3 :<<: const n :<<: ...
```

The `...` indicates an infinite stream of `const n`. Fold converts a list into an infinite stream of partial applications of `c` to list elements.

### Optimization and Runtime

The stream is a temporary compile-time structure that aids compiler optimizations. Like the H model, L can be used for fold-build fusion, and stream structures are optimized away.

Any streams remaining after fusion can be removed by inlining the definition of `run`. With sufficient compiler cleanup, stream structures do not exist at runtime—their purpose is compile-time only.

### L as Initial Object

The L model is the simplest possible model of hyperfunctions. Formally, in the category of hyperfunction models, the L model is an initial object.

**Why it matters:** The L model captures something essential about using hyperfunctions to define zip. It expresses the "linear" behavior of fold as it traverses its input lists.
