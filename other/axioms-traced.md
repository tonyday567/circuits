# Traced Monoidal Category Axioms — Equational Record

**Reference:** https://ncatlab.org/nlab/show/traced+monoidal+category
**Definitions:** see `02-gadt.md` for the GADT and `lower`; see `src/Circuit/Traced.hs` for `Trace` instances.

We prove the axioms by showing `lower` of both sides agrees. Only the equational
moves are recorded here — narrative motivation lives in the arc docs (01–07).

---

## Axiom 1: Vanishing

**nlab form:**

```
(a) tr^I(f) = f                          for all f : A x I -> B x I
(b) tr^{XxY}(f) = tr^X(tr^Y(f))         for all f : A x X x Y -> B x X x Y
```

### Part (a): tracing over the unit does nothing

**With `t = (,)`, unit `I = ()`.**

A morphism `f : A x I -> B x I` is `f :: ((), a) -> ((), b)`, which under the unit isomorphism is some `g :: a -> b` in disguise: `f = \((), x) -> ((), g x)`.

In `Circuit` this is `Knot f`. We want `lower (Knot f) = lower (Lift g)`.

```haskell
lower (Knot f)
  = trace f                               -- lower definition
  = \b -> let (a, c) = f (a, b) in c     -- Trace (->) (,) definition
                                          -- a :: (), so a = ()
  = \b -> let ((), c) = f ((), b) in c
  = \b -> let ((), c) = ((), g b) in c   -- definition of f
  = \b -> g b
  = g
  = lower (Lift g)                          -- check
```

The lazy knot has nothing to tie — `()` is determined immediately, no recursion occurs. The trace degenerates to plain function application.

**With `t = Either`, unit `I = Void`.**

`Either Void a ≅ a` since `Left v` is uninhabited. A morphism `f :: Either Void a -> Either Void b` can only map `Right x` to `Right (g x)`.

```haskell
lower (Knot f)
  = trace f
  = \b -> go (Right b)
    where go x = case f x of
            Right c -> c
            Left v  -> absurd v    -- unreachable
  = \b -> case f (Right b) of
            Right c -> c           -- only case possible
  = \b -> g b
  = lower (Lift g)                   -- check
```

The while-loop terminates immediately — `Left` is unreachable. Same result by a different operational path.

---

### Part (b): nested channels trace in sequence

**With `t = (,)`.**

`f :: ((x, y), a) -> ((x, y), b)`, channel is `(x,y)`, payload is `a`.

**LHS** — trace over product channel `(x,y)` simultaneously:

```haskell
trace f a0 = let ((x,y), b) = f ((x,y), a0) in b
```

One lazy knot, ties `(x,y)` as a pair.

**RHS** — trace `y` first, then `x`. For `tr^Y`, reshape `f` to treat `y` as channel and `(x,a)` as payload:

```haskell
shuffle   :: (y, (x, a)) -> ((x, y), a)
shuffle   (y, (x, a))  = ((x, y), a)

unshuffle :: ((x, y), b) -> (y, (x, b))
unshuffle ((x, y), b)  = (y, (x, b))

f_Y :: (y, (x, a)) -> (y, (x, b))
f_Y = unshuffle . f . shuffle
```

Inner trace ties `y`:

```haskell
trace f_Y (x, a0)
  = let (y, (x', b)) = f_Y (y, (x, a0)) in (x', b)
  = let (y, (x', b)) = unshuffle (f ((x', y), a0)) in (x', b)
  -- if f ((x',y), a0) = ((x'',y'), b') then unshuffle gives (y', (x'', b'))
  -- y tied lazily, y' = y
  = (x', b')  where ((x', y), b') = f ((x', y), a0)
```

Outer trace ties `x`:

```haskell
trace (trace f_Y) a0
  = let (x, b) = trace f_Y (x, a0) in b
  = let (x, b) = (x', b') where ((x', y), b') = f ((x', y), a0) in b
  -- outer knot ties x = x'
  = b  where ((x, y), b) = f ((x, y), a0)
```

Which is exactly the LHS. Check.

Both sides find the same fixed point of `((x,y), b) = f ((x,y), a0)`. The LHS ties the pair in one step; the RHS ties `y` first then `x`. Lazy evaluation makes them the same knot.

Note: `shuffle` uses the symmetry of `(,)` — swapping `x` and `y`. This is an artifact of the left-channel convention in `Trace`, not a requirement of the axiom itself. Vanishing part (b) needs associativity of the tensor; it does not require braiding. Yanking (axiom 5) is the axiom that genuinely requires a braiding.

**With `t = Either`.**

`f :: Either (Either a b) c -> Either (Either a b) c`, channel is `Either a b`.

The `Either` trace runs a while-loop rather than tying a lazy knot. The state space is `Either a b`.

LHS: one loop over state space `Either a b`:

```haskell
trace f c0 = go (Right c0)
  where go x = case f x of
          Right c        -> c
          Left (Left a)  -> go (Left (Left a))
          Left (Right b) -> go (Left (Right b))
```

RHS: nested loops. Inner traces out `b`, outer traces out `a`. Using associativity `Either (Either a b) c ≅ Either a (Either b c)`:

- Inner loop: exits on `Right`, loops on `Left b`
- Outer loop: exits on `Right`, loops on `Left a`

Combined: equivalent to one loop over `Either a b` — same fixed point, two nested state machines vs one. Check.

The `(,)` and `Either` traces are operationally dual: coinductive lazy knot vs inductive while-loop. Vanishing holds for both by the same logical structure, reached by different computational paths.

---

## Axiom 2: Sliding

**nlab form:**

```
For f : A x X -> B x Y,  g : Y -> X:

tr^X((id_B x g) . f) = tr^Y(f . (id_A x g))
```

The channel type changes: `f` consumes channel `X` and produces channel `Y`. The morphism `g : Y -> X` bridges them back. Sliding says it does not matter which side of `f` you apply `g` on — inside the trace they produce the same knot.

### With `t = (,)`

`f :: (x, a) -> (y, b)`, `g :: y -> x`.

In the left-channel convention, `id x g` means `first g`.

**LHS:** apply `g` to the output channel, then trace over `X`:

```haskell
-- (first g) . f :: (x, a) -> (x, b)
trace ((first g) . f) a
  = let (x, b) = ((first g) . f) (x, a) in b
  = let (x, b) = let (y, b') = f (x, a) in (g y, b') in b
  = let (y, b) = f (x, a) ; x = g y in b
  = let (y, b) = f (g y, a) in b          -- substituting x = g y
```

**RHS:** apply `g` to the input channel, then trace over `Y`:

```haskell
-- f . (first g) :: (y, a) -> (y, b)
trace (f . (first g)) a
  = let (y, b) = (f . (first g)) (y, a) in b
  = let (y, b) = f (g y, a) in b
```

Both sides: `\a -> let (y, b) = f (g y, a) in b`. Check.

The lazy knot ties `y` to `g y` from the output of `f`. Moving `g` to the other side of `f` inside the trace reaches the same fixed point.

### With `t = Either`

`f :: Either x a -> Either y b`, `g :: y -> x`.

**LHS:** `trace ((left g) . f)` where `left g = first g` for `Either`:

```haskell
trace ((left g) . f) b
  = go (Right b)
    where go x = case f x of
            Right c -> c
            Left y  -> go (Left (g y))
```

**RHS:** `trace (f . (left g))`:

```haskell
trace (f . left g) b
  = go (Right b)
    where go y = case f (Left (g y)) of
            Right c -> c
            Left y' -> go (Left y')
```

Both implement the same state machine: each loop step applies `g` to the feedback channel. The fixed point is the same — `g` sliding past `f` does not change which states are reachable or where the loop exits. Check.

---

## Axiom 3: Tightening

**nlab form:**

```
For h : A -> B,  f : B x X -> C x X,  g : C -> D:

tr^X((g x id_X) . f . (h x id_X)) = g . tr^X(f) . h
```

External morphisms `h` and `g` act only on the payload — they never touch the channel `X`. Tightening says they can be pulled freely in or out of the trace.

### With `t = (,)`

In the left-channel convention, `h x id_X = second h` and `g x id_X = second g`.

`h :: a -> b`, `f :: (x, b) -> (x, c)`, `g :: c -> d`.

**LHS:** wrap `f` with external morphisms, then trace:

```haskell
-- (second g) . f . (second h) :: (x, a) -> (x, d)
trace ((second g) . f . (second h)) a
  = let (x, d) = ((second g) . f . (second h)) (x, a) in d
  = let (x, d) = (second g) (f (second h (x, a))) in d
  = let (x, d) = (second g) (f (x, h a)) in d
  -- second g (x, c) = (x, g c)
  = let (x, c) = f (x, h a) ; d = g c in d
  = let (x, c) = f (x, h a) in g c
  = g (let (x, c) = f (x, h a) in c)
  = g (trace f (h a))
```

**RHS:** trace first, then compose with external morphisms:

```haskell
(g . trace f . h) a
  = g (trace f (h a))
  = g (let (x, c) = f (x, h a) in c)
```

Same. Check.

The channel `x` is untouched by `h` and `g` throughout — they act only on the payload. So they pass freely through the trace.

### With `t = Either`

`h :: a -> b`, `f :: Either x b -> Either x c`, `g :: c -> d`.

`second h` maps `Right a` to `Right (h a)`, leaves `Left` alone.
`second g` maps `Right c` to `Right (g c)`, leaves `Left` alone.

**LHS:**

```haskell
trace ((second g) . f . (second h)) a
  = go (Right a)
    where go (Right a') = case f (Right (h a')) of
            Right c  -> g c
            Left x   -> go (Left x)
          go (Left x)  = case f (Left x) of
            Right c  -> g c
            Left x'  -> go (Left x')
```

**RHS:** `(g . trace f . h) a = g (trace f (h a))`:

```haskell
trace f (h a)
  = go' (Right (h a))
    where go' x = case f x of
            Right c -> c
            Left x' -> go' (Left x')
```

Then `g` applied to the result.

Both enter the loop at `Right (h a)`, loop on `Left` transitions in `f` unaffected by `h` or `g`, and exit when `f` returns `Right c` — at which point `g c` is returned. Check.

---

## Axiom 4: Strength

**nlab form:**

```
For g : A -> B,  f : C x X -> D x X:

tr^X(g x f) = g x tr^X(f)
```

`g` is completely independent of the channel — it acts on a separate part of the payload. Strength says the trace cannot see `g` at all; `g` passes through untouched.

### With `t = (,)`

`g :: a -> b`, `f :: (x, c) -> (x, d)`.

In the left-channel convention, `g x f` acts on payload `(a, c)` with channel `x`:

```haskell
g `par` f :: (x, (a, c)) -> (x, (b, d))
(g `par` f) (x, (a, c)) = let (x', d) = f (x, c) in (x', (g a, d))
```

`g` acts on `a` independently; `f` runs with the channel.

**LHS:** tensor then trace:

```haskell
trace (g `par` f) (a, c)
  = let (x, (b, d)) = (g `par` f) (x, (a, c)) in (b, d)
  = let (x, (b, d)) = let (x', d') = f (x, c) in (x', (g a, d')) in (b, d)
  = let (x', d') = f (x, c) ; b = g a ; d = d' in (b, d)
  -- x tied to x' by knot
  = (g a, let (x, d) = f (x, c) in d)
  = (g a, trace f c)
  = bimap g (trace f) (a, c)
```

**RHS:** trace then tensor:

```haskell
(g `par` trace f) (a, c) = (g a, trace f c) = bimap g (trace f) (a, c)
```

Same. Check.

`g` acts on `a` before the knot forms and after it resolves — it is invisible to the channel `x`. The lazy knot ties only the `c`/`d` side via `f`; the `a`/`b` side is a straight wire carrying `g`.

### With `t = Either`

`g :: a -> b`, `f :: Either x c -> Either x d`.

`g x f` for `Either`: `g` acts on `Right a`, `f` runs the loop on `Either x c`:

```haskell
g `par` f :: Either x (Either a c) -> Either x (Either b d)
(g `par` f) (Left x)           = Left x          -- channel feedback unchanged
(g `par` f) (Right (Left a))   = Right (Left (g a))
(g `par` f) (Right (Right c))  = case f (Right c) of
                                    Left x   -> Left x
                                    Right d  -> Right (Right d)
```

**LHS:** `trace (g `par` f) (a, c)` — loop enters at `Right (a, c)`, `g` is applied when the `a` part exits, `f` governs the loop on the `c`/channel side.

**RHS:** `(g x trace f) (a, c) = (g a, trace f c)` — `g` applied directly to `a`, `trace f` runs its loop on `c`.

Both produce the same result: `g` is a straight wire, the loop only involves `f` and the channel. `g` has no feedback path and cannot affect when or how the loop exits. Check.

---

## Next

⊢ Axiom 5: Yanking (requires braiding)

## Axiom 5: Yanking

**nlab form:**

```
Tr^X(swap_{X,X}) = id_X
```

where `swap : X x X -> X x X` is the braiding — it swaps the two copies of `X`. Yanking says that tracing a swap is the same as doing nothing. This is where braiding is genuinely required: without a swap morphism, the axiom cannot even be stated.

### With `t = (,)`

The braiding is `swap :: (x, x) -> (x, x)` from `Data.Tuple`.

```haskell
trace swap x
  = let (a, c) = swap (a, x) in c
  = let (a, c) = (x, a) in c
  -- lazy knot: a = x, c = a = x
  = x
  = id x                              -- check
```

The lazy knot resolves immediately: `a` is set to `x` from the first component of `swap (a, x) = (x, a)`, and `c = a = x`. One substitution, no recursion.

### With `t = Either`

The braiding for `Either` is `swapEither`:

```haskell
swapEither :: Either a b -> Either b a
swapEither (Left x)  = Right x
swapEither (Right x) = Left x
```

```haskell
trace swapEither x
  = go (Right x)
    where go y = case swapEither y of
            Right c -> c
            Left a  -> go (Left a)
```

Expanding:

```haskell
  go (Right x) -- swapEither (Right x) = Left x
    -> go (Left x) -- swapEither (Left x) = Right x, so return x
    = x
  = id x                              -- check
```

The while-loop runs exactly one step: `Right` becomes `Left` via swapEither, `Left` becomes `Right` and exits. Operationally different from `(,)` — a two-step state machine vs an immediate lazy substitution — but the same result.

### Why braiding is required

The other four axioms involve only the channel and payload structure — they hold in any monoidal category with a trace. Yanking requires a morphism `swap : X x X -> X x X` that is part of a braiding. In a non-braided monoidal category no such morphism is guaranteed to exist, so yanking cannot be stated, let alone proved.

For `(,)` and `Either` in Haskell, both are symmetric monoidal — swap exists and is involutive — so yanking holds. In a merely monoidal (non-braided) setting, a traced structure can still exist but will satisfy only the first four axioms.

---

## Summary

| Axiom      | What it says                              | Key mechanism               |
|------------|-------------------------------------------|-----------------------------|
| Vanishing  | Unit channel is a no-op; products nest    | Knot with nothing to tie    |
| Sliding    | Channel bridge commutes past f            | Same fixed point either side|
| Tightening | Payload morphisms pass through the trace  | Channel untouched by h, g   |
| Strength   | Independent payload wire is invisible     | Disjoint types, no contact  |
| Yanking    | Tracing a swap is identity                | Requires braiding            |

The `(,)` and `Either` instances are operationally dual throughout: lazy knot vs while-loop. Every axiom holds for both by the same logical structure, reached by different computational paths.

