---
name: queue-state
description: Pure list-backed queue state and state-threading lifters
tags: ['queue', 'pure', 'state']
---

# queue state

Pure @[a]@ buffer interpretations of the 'Queue' strategies.  Useful for
state-threading 'Trace' diagrams where the buffer is carried on the tensor.

```haskell
endsPure :: Queue a -> (a -> [a] -> ([a], Bool), [a] -> ([a], Maybe a))
```

---

## implementation

```haskell
import Circuit.Queue (Queue (..))

endsPure :: Queue a -> (a -> [a] -> ([a], Bool), [a] -> ([a], Maybe a))
endsPure = \case
  Unbounded ->
    ( \x buf -> (buf ++ [x], True),
      \case [] -> ([], Nothing); x : xs -> (xs, Just x)
    )
  Bounded n ->
    ( \x buf -> if length buf < n then (buf ++ [x], True) else (buf, False),
      \case [] -> ([], Nothing); x : xs -> (xs, Just x)
    )
  Single ->
    ( \x buf -> case buf of [] -> ([x], True); _ -> (buf, False),
      \case [] -> ([], Nothing); x : _ -> ([], Just x)
    )
  SwapQ ->
    ( \x _ -> ([x], True),
      \case [] -> ([], Nothing); x : _ -> ([], Just x)
    )
  Latest d ->
    ( \x _ -> ([x], True),
      \buf -> (buf, Just (case buf of x : _ -> x; [] -> d))
    )
  Newest n ->
    ( \x buf ->
        let buf' = buf ++ [x]
         in if length buf' <= n then (buf', True) else (drop 1 buf', True),
      \case [] -> ([], Nothing); x : xs -> (xs, Just x)
    )

push :: (s -> a -> (s, Bool)) -> Trace t (->) (s, a) (s, Bool)
push f = Arr (uncurry f)

pop :: (s -> (s, Maybe a)) -> Trace t (->) (s, ()) (s, Maybe a)
pop f = Arr (\(s, ()) -> f s)

drain :: (s -> (s, [a])) -> Trace t (->) (s, ()) (s, [a])
drain f = Arr (\(s, ()) -> f s)

snapshot :: (s -> (s, [a])) -> Trace t (->) (s, ()) (s, [a])
snapshot f = Arr (\(s, ()) -> f s)
```

---

## bool / maybe signalling

In Trace the channel doors are total; partiality is recovered by carrying
'Bool'/'Maybe' as payload values, and treating close/stop as a separate
lifecycle.

```haskell
let (w, r) = endsPure (Single :: Queue Int)
run (push (flip w) :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([], 1)
-- ([1],True)
run (push (flip w) :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([1], 2)
-- ([1],False)
run (pop r :: Trace (,) (->) ([Int], ()) ([Int], Maybe Int)) ([1], ())
-- ([],Just 1)
run (pop r :: Trace (,) (->) ([Int], ()) ([Int], Maybe Int)) ([], ())
-- ([],Nothing)
```

---

## wither

Pre/post composition on payload legs. Companion-side wither filters the
harvested list; conjoint-side wither is the dual 'lmap'/'first' construction.

```haskell
let (w, r) = endsPure (Unbounded :: Queue Int)
run (drain (\buf -> ([], buf)) >>> rmap (\(s, xs) -> (s, filter even xs))
       :: Trace (,) (->) ([Int], ()) ([Int], [Int])) ([1,2,3], ())
-- ([],[2])
```
