# two-loops ⟜ separate Circuits, fused, and the composition trap

Same task three ways: qList (walk a list) + takeE (take N elements).
First as two separate `Knot`s, then fused into one, then the
composition attempt that fails — because `toHyper` flattens the loops.

Paste each block into `cabal repl`.

## setup

```haskell
{-# LANGUAGE LambdaCase #-}
import Circuit.Circuit (Circuit(..), toHyper, reify)
import Circuit.Hyper (lower)
import Control.Category ((.))
import Prelude hiding ((.), id)
```

## separate Knots

Each Knot is its own feedback loop. The Either tensor: `Left` = continue,
`Right` = stop.

```haskell
qList :: [Int] -> Circuit (->) Either () (Maybe Int)
qList xs = Knot $ \case
  Right () -> case xs of
    []      -> Right Nothing
    (x:xs') -> Left (xs', Just x)
  Left (xs', _) -> case xs' of
    []      -> Right Nothing
    (y:ys)  -> Left (ys, Just y)

takeE :: Int -> Circuit (->) Either (Maybe Int) (Maybe Int)
takeE n = Knot $ \case
  Right mx -> if n <= 0 then Right Nothing else Left (n, mx)
  Left (k, _) -> if k <= 0 then Right Nothing else Left (k-1, Nothing)

-- >>> reify (qList [1,2,3]) ()
-- Right (Just 1)
-- >>> reify (takeE 2) (Just 5)
-- Right (Just 5)
```

## fused — both loops in one Knot

State is `([Int], Int, [Int])` — remaining list, remaining count,
accumulated output.

```haskell
fused :: Int -> [Int] -> Circuit (->) Either () (Maybe [Int])
fused n xs = Knot $ \case
  Right ()           -> collect xs n []
  Left (xs', k, acc) -> collect xs' k acc
  where
    collect [] _ acc     = Right (Just (reverse acc))
    collect _  0  acc    = Right (Just (reverse acc))
    collect (x:xs') k acc = Left (xs', k-1, x:acc)

-- >>> reify (fused 2 [1,2,3,4,5]) ()
-- Right (Just [1,2])
-- >>> reify (fused 5 [1,2,3]) ()
-- Right (Just [1,2,3])
```

## the composition trap

You might try composing the two Circuits with `toHyper`:

```haskell
-- | This DOES NOT WORK. toHyper flattens Knots, so the Either types
--   from qList (Circuit (->) Either) don't align with the (,) composition
--   in Hyper's Category instance.
--
--   Error: Couldn't match type 'Either' with '(,)'
--
-- bad = toHyper (takeE 2) . toHyper (qList [1,2,3])
```

`toHyper` calls `trace` internally, which resolves the Either loop
into a plain function. The resulting `Hyper` uses `(,)` for
composition, so you can't chain two Either-traced Hypers with `(.)`.

What works instead:
- Fuse the loops into one Knot (above)
- Use `toHyperE` (structure-preserving) for Either-aware composition
- Use Producer/Consumer/Channel for composable streaming (see
  `examples/channel-basics.md`)

## reference

- `Circuit.Circuit` — toHyper vs toHyperE (SKILL.md gotchas)
- `examples/hyper-stream.md` — same task via Hyper directly
- `examples/channel-basics.md` — composable streaming with Channel
