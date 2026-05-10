# coroutine-hyper ⟜ coroutines, Trace encodings, and the loopToHyper bridge

Three questions explored here:
1. Can a coroutine be encoded directly as a Hyper?
2. Can each `Trace` tensor (Either, These) be expressed as a single Hyper?
3. What is the loopToHyper bridge between Circuit and Hyper?

This card needs `these`. Start with:

```
cabal repl -b these
```

Paste blocks in order.

---

## 1. Coro → Channel

A state-machine coroutine encoded as a `Channel` — the same type from
`Circuit.Channel`, defined here inline. The coroutine's state `s` lives
in the closure chain of `go`.

```haskell
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Circuit.Hyper (Hyper(..), invoke, run)
import Data.These (These(..))
import Prelude hiding (id, (.))

-- | A state-machine coroutine.
data Coro s i o = Coro
  { coStep  :: s -> i -> (o, s)
  , coState :: s
  }

-- | Channel = the paper's type: (o → r) ↬ (i → r)
type Channel r i o = Hyper (o -> r) (i -> r)

-- | Encode a Coro as a Channel. State s is captured in the 'go' closure chain.
coroToChannel :: Coro s i o -> (s -> r) -> Channel r i o
coroToChannel (Coro step s0) done = go s0
  where
    go s = Hyper $ \out i ->
      let (o, s') = step s i
      in invoke out (go s') o
```

The problem: `Channel` is opaque. You can't tell whether it produced
`Nothing` (stop) without invoking it. The Producer/Consumer protocol in
`Circuit.Channel` solves this — the Consumer decides when to stop. See
`examples/channel-basics.md`.

---

## 2. Trace tensors as single Hypers

Each `Trace` instance encodes a different iteration discipline.
Instead of using `Trace` directly, we can encode each tensor as
a self-contained `Hyper` that carries its own feedback state.

### Either — iterate until Right

```haskell
-- | Encode Trace (->) Either as a single Hyper.
--   Left = continue, Right = stop.
loopEither :: (Either a b -> Either a c) -> Hyper (Either a b -> c) (Either a b -> c)
loopEither f = h
  where
    h = Hyper $ \k s ->
      case f s of
        Right c -> c
        Left a  -> invoke k h (Left a)

runEither :: (Either a b -> Either a c) -> b -> c
runEither f b = run (loopEither f) (Right b)
```

### These — iterate with optional simultaneous output

`These a c` means "continue AND produce output." Hyper discards the
output on `These` (consumed by composition). The continuation carries
only `This a`.

```haskell
loopThese :: (These a b -> These a c) -> Hyper (These a b -> c) (These a b -> c)
loopThese f = h
  where
    h = Hyper $ \k s ->
      case f s of
        That c    -> c
        This a    -> invoke k h (This a)
        These a _ -> invoke k h (This a)

runThese :: (These a b -> These a c) -> b -> c
runThese f b = run (loopThese f) (That b)
```

### Count to 3 — both tensors

```haskell
testEither :: Int -> Int
testEither = runEither f
  where
    f (Right n) | n < 3    = Left (n + 1)
                | otherwise = Right n
    f (Left n)  | n < 3    = Left (n + 1)
                | otherwise = Right n

testThese :: Int -> Int
testThese = runThese f
  where
    f (That n)    | n < 3    = This (n + 1)
                  | otherwise = That n
    f (This n)    | n < 3    = This (n + 1)
                  | otherwise = That n
    f (These n _) | n < 3    = This (n + 1)
                  | otherwise = That n

-- >>> testEither 0
-- 3
-- >>> testEither 5
-- 5
-- >>> testThese 0
-- 3
-- >>> testThese 5
-- 5
```

---

## 3. The KnotToHyper bridge

A typeclass that dispatches `Knot` bodies directly to `Hyper`,
preserving loop structure (unlike `toHyper` which flattens).

```haskell
{-# LANGUAGE TypeFamilies #-}
import Circuit.Hyper (Hyper(..), invoke, run)

class KnotToHyper t where
  type KnotState t a b :: *
  loopToHyperK :: ((t a b) -> (t a c)) -> Hyper (KnotState t a b -> c) (KnotState t a b -> c)
  runKnot :: ((t a b) -> (t a c)) -> b -> c

instance KnotToHyper Either where
  type KnotState Either a b = Either a b
  loopToHyperK = loopEither
  runKnot = runEither

instance KnotToHyper These where
  type KnotState These a b = These a b
  loopToHyperK = loopThese
  runKnot = runThese
```

The `(,)` tensor is different — it ties a lazy knot via `run` on a
self-referential Hyper. The data itself carries the knot, not the
iteration. See below.

---

## 4. Fibonacci via lazy knot

The `(,)` trace ties a lazy knot: `let (a, c) = f (a, b) in c`.
In Hyper, `run` does the same: `run h = invoke h (Hyper run)`.

```haskell
-- | Fibonacci via Hyper run. The self-reference in 'fibs' IS the lazy knot.
fibs :: [Int]
fibs = run h
  where
    h :: Hyper [Int] [Int]
    h = Hyper $ \_ ->
      let xs = 0 : 1 : zipWith (+) xs (tail xs)
      in xs

-- >>> take 10 fibs
-- [0,1,1,2,3,5,8,13,21,34]
```

---

## 5. Delimited continuations (prose only)

The original file sketched heap-allocated coroutines using `prompt` /
`control0` from `GHC.Exts`. These are internal to `Circuit.Traced` and
not exported. The pattern from the paper (Kidney & Wu §5.2):

- `prompt` sets a boundary for continuation capture
- `yield` calls `control0` to capture the continuation up to the prompt
- The continuation is stored in an `IORef`
- `send` reads the stored continuation and applies it to the input

This is how `Trace (Kleisli IO) Either` works internally. The
user-facing API is `trace` / `↪`. See `other/06-rwr.md` for the
Reflection Without Remorse encoding and `other/04-hyper.md` for the
final encoding story.

---

## reference

- `Circuit.Hyper` — the module
- `Circuit.Traced` — Trace class, delimited continuations (internal)
- `examples/channel-basics.md` — Producer/Consumer/Channel idioms
- `examples/stable-marriage.md` — concurrent coroutine pattern
- Kidney & Wu, POPL 2026 — §2.4, §5.1, §5.2, §5.3
