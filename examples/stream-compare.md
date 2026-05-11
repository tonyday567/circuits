# stream-compare ⟜ streaming patterns across Hyper and Circuit

How to stream through a list one element at a time. Four approaches
compared, with the working code and why each works or doesn't.

We need: take `[a]`, produce each element individually, stop at end.
This is the basic building block for circuits-io resources.

---

## 1. Hyper prod/cons chain ⟜ full stream, pure, works

The invoke mechanism walks the chain layer by layer. Each `prod` is
one element; `doneP` is the terminator. The consumer accumulates.

```haskell
import Circuit.Channel
import Circuit.Circuit
import Circuit.Hyper
import Control.Category
import Prelude hiding (id, (.))

type Producer o a = Hyper (o -> a) a
type Consumer i a = Hyper a (i -> a)

prod :: o -> Producer o a -> Producer o a
prod o p = Hyper $ \q -> invoke q p o

cons :: (i -> a -> a) -> Consumer i a -> Consumer i a
cons f p = Hyper $ \q i -> f i (invoke q p)

doneP :: a -> Producer o a
doneP  a = Hyper $ \_ -> a
doneC  a = Hyper $ \_ _ -> a

withQ :: Producer o a -> Consumer o a -> a
withQ p c = invoke p c

emitChain :: [a] -> Producer (Maybe a) [a]
emitChain = foldr (\x p -> prod (Just x) p) (prod Nothing (doneP []))

accumChain :: Consumer (Maybe a) [a]
accumChain = h where h = cons (\mx acc -> case mx of Nothing -> acc; Just x -> x:acc) h

runProd :: [a] -> [a]
runProd xs = withQ (emitChain xs) accumChain

-- >>> runProd [1,2,3]
-- [1,2,3]
```

**Why it works:** Each `prod` constructs `Hyper $ \q -> invoke q p o`.
When invoked, the continuation `q` (the Consumer) receives the inner
producer `p` and the element `o`. The Consumer's `cons` layer receives
the element and invokes the next layer. The chain walks itself.

---

## 2. IORef + recursion ⟜ full stream, IO, works

External state via IORef; explicit recursion for the loop.

```haskell
import Data.IORef

runIORef :: Show a => [a] -> IO ()
runIORef xs = do
  ref <- newIORef xs
  let loop = do
        mx <- readIORef ref >>= \m -> case m of
          []    -> pure Nothing
          (x:r) -> writeIORef ref r >> pure (Just x)
        case mx of Nothing -> pure (); Just x -> putStrLn (show x) >> loop
  loop

-- >>> runIORef [10,20,30]
-- 10
-- 20
-- 30
```

**Why it works:** The IORef holds position between calls. The recursion
is the loop. The loop is outside Hyper — it's raw IO. This is the
fallback pattern for any resource that needs external state.

---

## 3. Circuit tensor — one element per reify

Both `(,)` (lazy knot) and `Either` (iteration) give ONE element per
`reify`/`reifyE` call. The tensor encodes the loop body, but `trace`
terminates with the first result. Subsequent elements require another
call with a new input.

```haskell
data Circuit t a b where
  Lift    :: (a -> b) -> Circuit t a b
  Compose :: Circuit t b c -> Circuit t a b -> Circuit t a c
  Knot    :: (t a b -> t a c) -> Circuit t b c

reifyE :: Circuit Either a b -> (a -> b)
reifyE (Lift f) = f
reifyE (Compose f g) = reifyE f . reifyE g
reifyE (Knot k) = traceEither k

traceEither :: (Either a b -> Either a c) -> (b -> c)
traceEither f b = go (Right b) where go x = case f x of Right c -> c; Left a -> go (Left a)

emitEach :: Circuit Either [a] (Maybe a)
emitEach = Knot $ \case
  Right []     -> Right Nothing
  Right (x:xs) -> Left (x:xs)
  Left (x:xs)  -> Right (Just x)

-- >>> reifyE emitEach ([1,2,3] :: [Int])
-- Just 1
-- >>> reifyE emitEach ([2,3] :: [Int])
-- Just 2
```

**Why only one element:** The Either trace iterates THROUGH the Left
branch until it finds a Right. Once it finds Right, it returns.
It doesn't produce multiple Rights — it produces ONE.

The `(,)` trace creates a lazy knot. For finite lists the knot
diverges (circular self-reference). For infinite lazy streams
(fibonacci) it works because the knot is coinductive.

---

## 4. Circuit Compose chain — function composition

A `foldr`-built chain via `Compose`:

```haskell
emitChainC :: [a] -> Circuit Either () (Maybe a)
emitChainC []     = Lift $ const Nothing
emitChainC (x:xs) = Compose (Lift $ const (Just x)) (emitChainC xs)

-- >>> reifyE (emitChainC [1,2,3]) ()
-- Just 1
```

Only the outermost `Lift` fires. `reifyE` composes the functions:
`(\() -> Just 1) . (\() -> Just 2) . (\() -> Nothing) = \() -> Just 1`.

Circuit `Compose` is just `(.)`. Unlike Hyper's `invoke`, it doesn't
thread a continuation — it returns a composed function. There's no
chain-walking mechanism.

---

## Conclusion: invoke is the difference

| Pattern | Streams? | Pure? | Mechanism |
|---------|----------|-------|-----------|
| Hyper prod-chain | Yes | Yes | `invoke` threads continuations |
| IORef + recursion | Yes | No | External state, explicit loop |
| Circuit tensor | One element | Yes | Trace terminates at first `Right` |
| Circuit Compose | First only | Yes | Function composition, no threading |

For circuits-io: the prod-chain via Hyper's `invoke` is the right model.
Each resource operation (open, read, write, close) becomes a layer in
the chain. The chain IS the program — build once, run via `withQ`.

The Circuit tensors and Compose are useful for bracketed resource
lifecycles (acquire/use/release) and lazy coinductive streams,
but not for per-element iteration through a finite resource.
