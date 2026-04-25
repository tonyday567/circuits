# circuits

[![Hackage](https://img.shields.io/hackage/v/circuits.svg)](https://hackage.haskell.org/package/circuits)
[![build](https://github.com/tonyday567/circuits/actions/workflows/haskell-ci.yml/badge.svg)](https://github.com/tonyday567/circuits/actions/workflows/haskell-ci.yml)

A free traced category.

# Usage

```haskell
import Circuit

-- | Tie the knot: convert a feedback function to a forward function.
--
-- >>> unsecond (\(c, a) -> (a + 10, c + a)) 5
-- 20
unsecond :: ((c, a) -> (c, b)) -> (a -> b)
unsecond f a = b where (c, b) = f (c, a)

-- | A biased accumulator using knot-tying.
--
-- >>> biasedAcc 5
-- 20
biasedAcc :: Int -> Int
biasedAcc = unsecond $ \(c, a) -> (a + 10, c + a)
```

For theory, design narrative, and complete axiom development, see `other/narrative-arc.md`.
