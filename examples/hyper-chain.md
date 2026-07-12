---
name: hyper-chain
description: Category composition on Hyper (and the Trace dual)
tags: ['hyper', 'composition', 'trace']
---
# hyper-chain ⟜ Category composition

The universal test: build a chain of layers via Category composition
(`>>>`), then walk it.  If composition works, this works.  Two encodings,
same story.

```haskell
-- $setup
-- >>> import Circuit.Hyper (Hyper, lift, observe)
-- >>> import Circuit (Trace (..), run)
-- >>> import Control.Category ((>>>))
-- >>> import qualified Circuit.Trace as T
```

---

## Hyper — final encoding

`lift` embeds a plain function; `observe` severs feedback and runs.

```haskell
streamChain :: [a] -> Hyper () [a]
streamChain = foldr (\x acc -> acc >>> lift (x:)) (lift (const []))

runChain :: [a] -> [a]
runChain xs = observe (streamChain xs) ()
```

```haskell
-- >>> runChain [1,2,3]
-- [1,2,3]
```

Each `lift (x:)` prepends an element.  `>>>` threads the feedback channel
through the layers.  `observe` severs feedback with a constant continuation
and walks the chain — `x : (y : (z : []))`.

(Pre-0.2 this helper was named `runLift`.  That name suggested Free's
`Lift` constructor.  The operation is `observe` after a chain of
`lift`s — `runChain` matches the modern vocabulary: `lift` / `observe`,
not `Lift` / `Compose`.)

---

## Trace — initial encoding (Arr / Knot / run)

Same fold, different surface.  Sequential composition is still `>>>`;
base arrows are `Arr`; the fold is `run`.

```haskell
streamChainT :: [a] -> Trace (,) (->) () [a]
streamChainT = foldr (\x acc -> acc >>> T.Arr (x:)) (T.Arr (const []))

runChainT :: [a] -> [a]
runChainT xs = run (streamChainT xs) ()
```

```haskell
-- >>> runChainT [1,2,3]
-- [1,2,3]
```

| encoding | embed | compose | eliminate |
|----------|-------|---------|-----------|
| Hyper | `lift` | `>>>` | `observe` |
| Trace | `Arr` | `>>>` | `run` |

No `Compose` constructor, no `Lift` on `Trace` — normal form is
`Arr` / `Knot` only.  Here the body never needs `Knot`; pure sequential
pipeline stays a chain of `Arr`s fused by the `Category` instance.

Qualify `T.Arr` in `cabal repl` (interpreted mode also loads
`Circuit.Mon`, which exports its own `Arr`).
