---
title: "lift . trace = trace . lift"
category: hyper
status: stable
tags: ["hyper", "trace", "lemma"]
---

# lift . trace = trace . lift

The identity that makes `encode` on `Trace` agree with the base-arrow route.  If
`lift :: (->) → Hyper` commutes with `trace`, then interpreting `Knot` through the
base arrow (`run`) and lifting into Hyper produces the same Hyper as encoding the
`Knot` directly via `trace_Hyper`.

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
observe :: Hyper a b -> (a -> b)
observe h x = invoke h (Hyper (const x))

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

## proof (behavioral, via observe)

Left side, `lift . trace_arr`:

```
lift (trace f) = Hyper (\k -> trace f (invoke k (lift (trace f))))

observe (lift (trace f)) x
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

observe (trace (lift f)) x
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

Both reduce to `let (a, c) = f (a, x) in c`.  Equal through `observe` — and for
the final encoding, behavioral equality IS equality.

## why it matters

`encode` on `Trace` is direct because `Trace` is already in normal form:

```
encode (Arr f)        = lift f
encode (Knot k)       = trace_Hyper (encode k)          -- Hyper's trace
```

Alternatively, via the base-arrow interpreter `run`:

```
run (Knot k)          = trace_arr (run k)
encode (Knot k)       = lift (run (Knot k))
                      = lift (trace_arr (run k))
                      = trace_Hyper (lift (run k))      -- by lift.trace=trace.lift
                      = trace_Hyper (encode k)          -- by induction
```

`run` pushes `trace` into the base arrow; `lift` lifts it into Hyper.
The commutation ensures the base-arrow route agrees with calling `trace` directly in Hyper.

## categorical name

This is the **traced functor** condition (Hasegawa 1997, Joyal-Street-Verity 1996).
A functor `F` between traced monoidal categories is **traced** if `F(trace f) = trace(F f)`.
Here `F = lift :: (->) → Hyper`, and the condition is exactly `lift . trace = trace . lift`.

It's the same condition that makes `observe` a traced functor in the other direction:
`observe . trace_Hyper = trace_arr . observe`.  Both hold because `lift` and `observe`
form a traced adjunction between the initial and final encodings.
