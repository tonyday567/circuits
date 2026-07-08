# hyper-chain ⟜ Category composition on Hyper

The universal test: build a chain of `lift` layers via `(.)`, then walk
it with `observe`.  If Category composition works, this works.

```haskell
-- $setup
-- >>> import Circuit.Hyper
-- >>> import Control.Category
-- >>> import Prelude hiding (id, (.))
```

```haskell
streamChain :: [a] -> Hyper () [a]
streamChain = foldr (\x acc -> lift (x:) . acc) (lift (const []))

runLift :: [a] -> [a]
runLift xs = observe (streamChain xs) ()
```

```haskell
-- >>> runLift [1,2,3]
-- [1,2,3]
```

Each `lift (x:)` prepends an element.  `(.)` threads the feedback channel
through the layers.  `observe` severs feedback with a constant continuation
and walks the chain — `x : (y : (z : []))`.
