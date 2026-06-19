# lift . trace = trace . lift

The identity that makes `encode` factor through `freeze`.  If `lift :: (->) → Hyper`
commutes with `trace`, then dissolving `Knot` into `Lift (trace_arr ...)` (via `freeze`)
and lifting into Hyper (`encodeFree`) produces the same Hyper as encoding the `Knot`
directly via `trace_Hyper`.

```haskell
lift . trace_arr = trace_Hyper . lift
```

This is the **traced functor** condition — `lift` preserves the trace structure.

## the definitions

```haskell
-- Hyper construction: embed a plain function (self-referential)
lift :: (a -> b) -> Hyper a b
lift f = Hyper (\k -> f (invoke k (lift f)))

-- Hyper observation: supply the identity continuation
lower :: Hyper a b -> (a -> b)
lower h x = invoke h (Hyper (const x))

-- Base arrow trace: lazy knot
trace_arr :: ((a, b) -> (a, c)) -> (b -> c)
trace_arr f b = let (a, c) = f (a, b) in c

-- Hyper trace: lazy knot through invoke/cont
trace_Hyper :: Hyper (a, b) (a, c) -> Hyper b c
trace_Hyper body = Hyper $ \k ->
  let pair = invoke body cont
      cont = Hyper $ \_ ->
        let a_val = invoke k (Hyper (const (snd pair)))
         in (fst pair, a_val)
   in snd pair
```

## proof (behavioral, via lower)

Left side, `lift . trace_arr`:

```
lift (trace f) = Hyper (\k -> trace f (invoke k (lift (trace f))))

lower (lift (trace f)) x
  = trace f (invoke (Hyper (const x)) (lift (trace f)))
  = trace f x
  = let (a, c) = f (a, x) in c
```

Right side, `trace_Hyper . lift`:

```
trace (lift f) = Hyper $ \k ->
  let pair = invoke (lift f) cont
      cont = Hyper $ \_ ->
        let a_val = invoke k (Hyper (const (snd pair)))
         in (fst pair, a_val)
   in snd pair

lower (trace (lift f)) x
  -- substitute k = Hyper (const x):
  let pair = invoke (lift f) cont
      cont = Hyper $ \_ ->
        let a_val = invoke (Hyper (const x)) (Hyper (const (snd pair)))
         in (fst pair, a_val)
   in snd pair
  -- invoke (Hyper (const x)) h = x:
  = let pair = invoke (lift f) cont
        cont = Hyper $ \_ -> (fst pair, x)
     in snd pair
  -- invoke (lift f) cont = f (invoke cont (lift f)):
  = let pair = f (invoke cont (lift f))
     in snd pair
  -- invoke cont (lift f) = (fst pair, x):
  = let pair = f (fst pair, x)
     in snd pair
  -- let (a, c) = pair:
  = let (a, c) = f (a, x) in c
```

Both reduce to `let (a, c) = f (a, x) in c`.  Equal through `lower` — and for
the final encoding, behavioral equality IS equality.

## why it matters

`encode` can factor through `freeze` because of this identity:

```
old encode (Knot k) = trace_Hyper (encode k)           -- Hyper's trace
new encode (Knot k) = encodeFree (freeze (Knot k))     -- freeze dissolves Knot
                    = encodeFree (Lift (trace_arr (reify k)))
                    = lift (trace_arr (reify k))
                    = trace_Hyper (lift (reify k))     -- by lift.trace=trace.lift
                    = trace_Hyper (encodeFree (freeze ...))
                    = trace_Hyper (encode k)           -- by induction
```

`freeze` pushes `trace` into the base arrow; `lift` lifts it into Hyper.
The commutation ensures the round-trip agrees with calling `trace` directly in Hyper.

## categorical name

This is the **traced functor** condition (Hasegawa 1997, Joyal-Street-Verity 1996).
A functor `F` between traced monoidal categories is **traced** if `F(trace f) = trace(F f)`.
Here `F = lift :: (->) → Hyper`, and the condition is exactly `lift . trace = trace . lift`.

It's the same condition that makes `lower` a traced functor in the other direction:
`lower . trace_Hyper = trace_arr . lower`.  Both hold because `lift` and `lower`
form a traced adjunction between the initial and final encodings.
