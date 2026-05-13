# stream-compare ⟜ streaming patterns across Hyper and Circuit

How to stream through a list one element at a time. Four approaches
compared, with the working code and why each works or doesn't.

We need: take `[a]`, produce each element individually, stop at end.
This is the basic building block for circuits-io resources.

---

## 1. Hyper lift chain ⟜ full stream, pure, works

Category composition on Hyper threads values through layers. Each
element is a `lift`, composed with `(.)`. The chain builds once;
`lower` walks it.

```haskell
import Circuit.Hyper
import Control.Category
import Prelude hiding (id, (.))

-- Build the chain via foldr: each element wraps the accumulator
streamChain :: [a] -> Hyper () [a]
streamChain = foldr (\x acc -> lift (x:) . acc) (lift (const []))

runLift :: [a] -> [a]
runLift xs = lower (streamChain xs) ()

-- >>> runLift [1,2,3]
-- [1,2,3]
```

**Why it works:** `lift (x:) :: Hyper [a] [a]` prepends `x` to a list.
Composing `lift (x:) . lift (y:) . lift (const [])` builds a single
Hyper that, when lowered, walks each layer — `x : (y : (z : []))`.
No dual pairs, no invoke threading. Just `(.)` and `lower`.

**prod/cons lineage.** This lift-based approach decomposes the
Kidney & Wu `prod`/`cons` primitives from `Circuit.Channel`:

```
prod x p  =  Hyper $ \c -> (c ⇸ p) x     -- K&W producer prepend
         ≅  lift (x:) . p                 -- same effect, via Category

emit   a  =  Hyper $ \_ -> a             -- Emit: atomic producer (Hyper () a)
forget    =  Hyper $ \_ -> ()            -- Commit: atomic consumer (Hyper a ())
```

`prod` and `cons` are the named primitives of `Circuit.Channel`.
They're the K&W canon. The decomposition into `Emit`/`Commit` +
`Category` is a refinement, not a deletion — the module keeps its
identity while the Category instances carry the structural weight.
See `examples/channel-refactor.md` for the full derivation.

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

Circuit `Compose` is just `(.)`. Unlike Hyper's Category composition, it doesn't
thread a continuation — it returns a composed function. There's no
chain-walking mechanism.

---

## Conclusion: Hyper walks, Circuit collapses

| Pattern | Streams? | Pure? | Mechanism |
|---------|----------|-------|-----------|
| Hyper lift chain | Yes | Yes | Category `(.)` + `lower` |
| IORef + recursion | Yes | No | External state, explicit loop |
| Circuit tensor | One element | Yes | Trace terminates at first `Right` |
| Circuit Compose | First only | Yes | Function composition, no threading |

For circuits-io: the lift chain via Hyper Category is the right model.
Each resource operation (open, read, write, close) becomes a layer in
the chain. The chain IS the program — build once, run via `lower`.

The prod/cons primitives in `Circuit.Channel` are the K&W canon that
decompose into `Emit`/`Commit` + Category (see `channel-refactor.md`).
The lift chain uses the Category instances directly; prod/cons supply
the named API when dual-pair construction is clearer.

The Circuit tensors and Compose are useful for bracketed resource
lifecycles (acquire/use/release) and lazy coinductive streams,
but not for per-element iteration through a finite resource.
