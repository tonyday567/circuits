# PureQueue.Test — pipeline test (R&D)

```haskell
-- | Pure queueEnds pipeline test — mirror of the STM makeQueue test.
--
-- Two Unbounded queues (A and B), combined state threaded through.
-- Pipeline: produce 7 → pushA → popA → pushB → popB → 7.
module PureQueue.Test where

import Circuit
import Control.Category ((>>>))
import PureQueue.Ends

-- Two queues share combined state: (bufA, bufB)
type Q2 = ([Int], [Int])

pipeline :: Circuit (->) (,) (Q2, ()) (Q2, Int)
pipeline = source >>> pushA >>> popA >>> pushB >>> popB
  where
    (writeA, readA) = queueEnds Unbounded
    (writeB, readB) = queueEnds Unbounded

    source = Lift $ \(qs, ()) -> (qs, 7)

    pushA = Lift $ \((bufA, bufB), x) ->
      let (bufA', _) = writeA x bufA in ((bufA', bufB), ())
    popA  = Lift $ \((bufA, bufB), ()) ->
      let (bufA', Just x) = readA bufA in ((bufA', bufB), x)
    pushB = Lift $ \((bufA, bufB), x) ->
      let (bufB', _) = writeB x bufB in ((bufA, bufB'), ())
    popB  = Lift $ \((bufA, bufB), ()) ->
      let (bufB', Just x) = readB bufB in ((bufA, bufB'), x)

-- | Run with empty buffers.
test :: (Q2, Int)
test = reify pipeline (([], []), ())
```
