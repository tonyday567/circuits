``` haskell
-- | Convenient wrapper for simple IO feedback loops.
--
--   @loopIO step@ creates a Circuit that runs @step@ for each iteration,
--   treating both entry and loop states uniformly.
loopIO :: (a -> IO (Either a b)) -> Circuit (Kleisli IO) Either a b
loopIO step = Loop (Kleisli \case
  Right x -> step x
  Left  x -> step x)
```
