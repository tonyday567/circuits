# PureQueue.Ends — simpler queue ends with `[a]` state (R&D)

```haskell
-- | Pure, visible-state queue ends.  State is [a] for all strategies.
--
-- This is a pure, non-existential analogue of Circuit.IO.Queue.queueEnds
-- that returns write/read functions operating on an explicit [a] buffer.
--
-- The caller threads the buffer through 'Compose' when lifted into circuits.
module PureQueue.Ends where

-- | Queue strategy.
data Queue a
  = Unbounded
  | Bounded Int
  | Single
  | Latest a
  | Newest Int
  | New
  deriving (Show, Eq)

-- | Create pure write/read ends for a queue strategy.
--
-- write :: a -> [a] -> ([a], Bool)    -- push value, Bool = accepted
-- read  :: [a] -> ([a], Maybe a)       -- pop value, Nothing = empty
queueEnds :: Queue a -> (a -> [a] -> ([a], Bool), [a] -> ([a], Maybe a))
queueEnds = \case
  Unbounded ->
    ( \x buf -> (buf ++ [x], True)
    , \case
        []   -> ([], Nothing)
        x:xs -> (xs, Just x)
    )
  Bounded n ->
    ( \x buf ->
        if length buf < n
        then (buf ++ [x], True)
        else (buf, False)
    , \case
        []   -> ([], Nothing)
        x:xs -> (xs, Just x)
    )
  Single ->
    ( \x _ -> ([x], True)
    , \case
        []   -> ([], Nothing)
        x:_  -> ([], Just x)
    )
  Latest d ->
    ( \x _ -> ([x], True)
    , \buf -> (buf, Just (if null buf then d else head buf))
    )
  Newest n ->
    ( \x buf ->
        let buf' = buf ++ [x]
        in if length buf' <= n
           then (buf', True)
           else (drop 1 buf', True)
    , \case
        []   -> ([], Nothing)
        x:xs -> (xs, Just x)
    )
  New ->
    ( \x _ -> ([x], True)
    , \case
        []   -> ([], Nothing)
        x:_  -> ([], Just x)
    )
```
