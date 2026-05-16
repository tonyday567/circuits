# hyper-loop ⟜ stepwise iteration in Hyper

A loop where each `invoke` is one step. The state lives in closures,
not in a mutable cell. Good for understanding how Hyper's self-reference
(`run`) differs from step-by-step driving.

Paste each block into `cabal repl` in order.

## stepKnot — one step per invoke

```haskell
{-# LANGUAGE LambdaCase #-}
import Circuit.Hyper (Hyper(..), invoke, run)

-- | Each invoke is one iteration. f decides Left (continue) or Right (stop).
stepKnot :: (Either a b -> Either a c) -> a -> Hyper b c
stepKnot f a = Hyper $ \k ->
  let b = invoke k (stepKnot f a)
  in case f (Right b) of
       Right c -> c
       Left a' -> invoke (stepKnot f a') k
```

## countdown — emit decrementing count, stop at 0

```haskell
countdown :: Int -> Hyper () (Maybe Int)
countdown n = stepKnot body n
  where
    body (Right ()) = if n <= 0 then Right Nothing else Left (n-1)
    body (Left k)   = if k <= 0 then Right (Just k) else Left (k-1)

-- | Drive the loop by invoking with a no-op consumer.
drive :: Hyper (Maybe Int) () -> Maybe Int
drive h = invoke h (Hyper $ \_ -> ())

-- >>> drive (countdown 3)
-- Just 3
-- >>> drive (countdown 0)
-- Nothing
```

## compare: run ties the knot once, stepKnot unwinds manually

`run` closes the self-referential loop in one shot. `stepKnot` lets you
step through. Same structure, different driving discipline.

```haskell
-- >>> run (countdown 3)
-- Just 3
```

## reference

- `Circuit.Hyper` — the module
- `other/03-hyper-buries-the-knot.md` — final encoding, Kan characterization
- `examples/while.md` — while loop: Hyper vs Circuit comparison
