---
name: two-files
description: Two independent file opens; par; swap; unitors; Trace () ()
tags: ['ends', 'io', 'par']
---

# two files

Swap two files as one program:

```haskell
Trace (,) (Kleisli IO) () ()
```

Independence is **`par`**. Wiring is **`runIn` / `runOut`**. Unit is **`openK ()`** + **unitors**.

---

## program

```haskell
unitl'
  >>> par (runIn outA inU1) (runIn outB inU2)   -- independent reads
  >>> swap
  >>> par (runOut inA outU1) (runOut inB outU2) -- cross writes
  >>> unitl
```

Two **`openFileEnds`**, two **`openK ()`**. Not a sequential copy.

---

## module

`Circuit.Ends.File`

- `openFileEnds path` → `(Out, In)` extrinsic free ends  
- `exchangeFiles a b` → `IO (Trace (,) (Kleisli IO) () ())`  
- `runExchange a b` → open, wire, **run once**

Also: `Tensor` / `Action` for `(,) (Kleisli m)` so `par` works on effectful Trace.

---

## check

```text
a="alpha" b="beta"  →  runExchange  →  a="beta" b="alpha"
```
