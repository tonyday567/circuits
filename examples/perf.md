# perf ⟜ measurement as a Circuit plugin

Perf is a measurement layer that prepends to an existing Circuit pipeline.
Rather than wrapping computations in a monad transformer (as `PerfT` does),
it encodes measurement as a Circuit that composes with whatever you're
already running.

## concept

```
┌─────────────┐   ┌──────────────┐
│   Perf      │   │  Pipeline    │
│  measures   │◀──│  does work   │
│  passes thru│   │              │
└─────────────┘   └──────────────┘
     Compose
```

A measurement is `Circuit (Kleisli m) t a (measurement, a)` — it reads
the clock (or allocation counter, or convergence metric), passes the
value through unchanged, and accumulates observations. The `(,)` pairing
of measurement with value is the `(,)` tensor at the output level, not
the Circuit tensor (which handles loop control separately).

## composing with a pipeline

Given any Circuit computation:

```haskell
pipeline :: Circuit (Kleisli IO) t a b
```

Attach measurement by `Compose`:

```haskell
measured :: Circuit (Kleisli IO) t a ([Nanos], b)
measured = perf `Compose` pipeline
```

The `Compose` wires measurement after the pipeline: input `a` flows
through `perf` (clock read → pass through), then through `pipeline`
(actual work), then `perf` reads the clock again on the way out.

This is the insight that `PerfT` approximates with its `StateT` machinery,
but Circuit makes structural — measurement is just another layer in the
composition chain, not a monad transformer that wraps everything.

## a single measurement

Simplest form: `Lift` wraps a `Kleisli IO` function that timestamps in
and out:

```haskell
once :: Circuit (Kleisli IO) (,) a ([Nanos], a)
once = Lift (Kleisli $ \a -> do
  !t0 <- nanos
  let !b = a   -- pass through (pipeline runs between reads)
  pure ([0], b))
```

But this doesn't work because the pipeline hasn't run yet at this point.
The measurement needs to bracket the pipeline, not live inside it. Two
approaches:

**Split-phase measurement.** The perf layer is actually two layers —
a pre-read before the pipeline and a post-read after:

```haskell
pre  :: Circuit (Kleisli IO) t a (Nanos, a)
post :: Circuit (Kleisli IO) t (Nanos, b) ([Nanos], b)
measured = pre `Compose` pipeline `Compose` post
```

`pre` reads the clock, tags the value with a timestamp. `post` reads
the clock again, computes the delta, accumulates. The `(,)` tensor
threads the timestamp alongside the value through the pipeline.

**Bracket via Kleisli.** The measurement wraps the entire
`Kleisli IO a b`:

```haskell
measure :: Kleisli IO a b -> Kleisli IO a ([Nanos], b)
measure (Kleisli f) = Kleisli $ \a -> do
  !t0 <- nanos
  !b  <- f a
  !t1 <- nanos
  pure ([t1 - t0], b)
```

Then lift into Circuit:

```haskell
perf :: Kleisli IO a b -> Circuit (Kleisli IO) t a ([Nanos], b)
perf f = Lift (measure f)
```

This is the cleanest single-shot measurement. The pipeline runs inside
the bracket, and the Circuit is just the lifted function.

## repeated measurement via Loop

For n runs, we need feedback — accumulated `[Nanos]` threaded through
iterations. The `Either` tensor's Loop (via `whileK` pattern) is the
natural fit because measurement is IO:

```haskell
-- step :: (Int, [Nanos], a) -> IO (Either ([Nanos], a) (Int, [Nanos], a))
-- Right = continue, Left = done
times :: Int -> Circuit (Kleisli IO) Either a ([Nanos], a)
times n = Loop (Kleisli body)
  where
    body (Right a) =
      let s = (0, [], a)  -- initial state: count=0, no nanos, input=a
      in swapRL <$> step s
    body (Left s) = swapRL <$> step s

    step (k, ns, a)
      | k >= n    = pure (Left (reverse ns, a))
      | otherwise = do
          !t0 <- nanos
          -- pipeline runs here in the full composition
          !t1 <- nanos
          pure (Right (t1 - t0 : ns, k + 1, a))

    swapRL (Right s) = Left s    -- continue
    swapRL (Left r)  = Right r   -- exit
```

The `Either` tensor's two phases (`Right` = init, `Left` = feedback)
map to the measurement cycle. Each iteration reads the clock, runs
the pipeline (via composition), reads again, accumulates.

## why Loop holds its weight here

Something has to stop a pipeline to measure it. A pipeline is a
continuous composition — values flow through, tensors thread state.
Measurement means pausing that flow, observing, and resuming.

Loop provides exactly this boundary. The feedback channel IS the
pause: values enter, the loop body observes (reads clock, checks
convergence, counts iterations), then either feeds back (continue)
or exits (done). The tensor that carries the feedback determines
what "observation" means:

- `(,)` tensor — accumulate measurements alongside values, natural
  for timing where `([Nanos], a)` is the pair
- `Either` tensor — two-phase continue/exit, natural for fixed-count
  or convergence-based stopping

This is Loop pulling its weight: not as a replacement for recursion
(as recursion.md explored), but as the *architectural boundary*
between computation and observation. The measurement isn't inside
the pipeline — it's a separate layer that the pipeline flows through.

## (,) tensor for Kleisli IO

`Kleisli IO (a, b) (a, c)` is `(a, b) -> IO (a, c)` — a function
from pairs to IO of pairs. The `Trace` instance uses an `IORef` to
tie the feedback knot:

```haskell
instance Trace (Kleisli IO) (,) where
  trace (Kleisli f) = Kleisli $ \b -> do
    ref <- newIORef (error "feedback uninitialised")
    let a = unsafeInterleaveIO (readIORef ref)
    (a', c) <- f (a, b)
    writeIORef ref a'
    pure c
```

Not beautiful, but correct and localised. The `(,)` tensor for
measurement is unblocked — the pure-vs-IO distinction was a false
tension. `Kleisli m` already encodes the monadic effect in the
arrow; the tensor just threads the pair.

With this instance, the natural measurement encoding works:

```haskell
-- Loop over (,) tensor: feedback carries ([Nanos], Int)
times :: Int -> Circuit (Kleisli IO) (,) a ([Nanos], a)
times n = Loop (Kleisli body)
  where
    body ((ns, k), a)
      | k >= n    = pure ((ns, k), (reverse ns, a))
      | otherwise = do
          !t0 <- nanos
          -- pipeline runs here
          !t1 <- nanos
          pure ((t1 - t0 : ns, k + 1), ([], a))
```

The `(,)` tensor's lazy knot threads accumulated nanos through the
feedback channel. Each iteration reads the clock, accumulates a
delta, and either loops (k < n) or exits (k >= n).

## compile-time erasure

Like `StateT`'s `runStateT`/`evalStateT`/`execStateT`, the perf
layer should be optional — present in the type but erasable when
not needed.

The simplest erasure: don't compose it. If the perf layer isn't
in the `Compose` chain, it doesn't exist in the pipeline. Unlike
`PerfT` which wraps the entire computation in a transformer, the
plugin pattern is opt-in by construction.

For conditional measurement (compile-time flag), a phantom type
parameter distinguishes measured from unmeasured pipelines:

```haskell
data Measured = On | Off

-- When On:  Circuit (Kleisli IO) (,) a ([Nanos], a)
-- When Off: Circuit (Kleisli IO) (,) a a  (identity layer)
```

GHC can inline and eliminate the identity layer when `Off`. The
pattern mirrors `StateT`'s three eliminators — you choose at the
call site whether to extract measurements, values, or both.

## history: convergence and waiting

The same plugin pattern generalises beyond timing. A "history" layer
accumulates observations and signals when a convergence condition is
met — useful for numerical methods, gradient descent, or any iterative
algorithm where you want to stop when values stabilise.

```haskell
-- Accumulate the last k values, signal when delta < epsilon
converge :: Int -> Double -> Circuit (Kleisli IO) Either Double [Double]
converge k eps = Loop (Kleisli body)
  where
    body (Right x) = step (0, [x])
    body (Left (i, xs)) = step (i, xs)

    step (i, xs)
      | i >= k, converged (take k xs) eps = pure (Left xs)
      | otherwise = pure (Right (i + 1, x : xs))  -- x comes from pipeline
```

The history layer records the stream of values passing through the
pipeline and exits when the last `k` values are within `eps` of each
other. The `Either` tensor's `Right`/`Left` phases again provide the
loop control — `Right` signals "keep iterating," `Left` signals "done."

This unifies perf and convergence: both are Circuit layers that observe
the stream, accumulate state, and decide when to stop. The difference
is what they observe (nanoseconds vs values) and the exit condition
(fixed count vs convergence criterion).

## what's next

🟣 ⟜ implement `Trace (Kleisli IO) (,)` — unblock the natural tensor for measurement
🟣 ⟜ benchmark: compare `perf` layer overhead vs bare `tickForce`
🟣 ⟜ history example: gradient descent with convergence-based early exit
🟣 ⟜ port mtok's `tokenizeWithPerf` to the plugin pattern
