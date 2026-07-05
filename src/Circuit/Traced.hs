{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
#ifdef __GLASGOW_HASKELL__
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
#endif

-- | Close and open feedback loops in a monoidal category.
--
-- A 'Traced' instance for a tensor @t@ specifies how to thread a value
-- through a feedback channel:
--
--   * 'trace' closes the channel — eliminates the tensor and produces
--     a plain morphism. This is where the loop semantics live.
--
--   * 'untrace' opens the channel — lifts a plain morphism into the
--     tensor, leaving the feedback value untouched.
--
-- The trace laws (trace monoidal category axioms):
--
-- 1. __Naturality (tightening)__. Morphisms that don't touch the trace
--    wire pass through freely.
--
--      @trace (untrace f . g . untrace h) = f . trace g . h@
--
-- 2. __Dinaturality (sliding)__. A morphism on the trace wire can slide
--    from one side of the trace to the other.
--
--      @trace (g . untrace f) = trace (untrace f . g)@
--
-- 3. __Vanishing__.
--
--      * Unit: @trace (untrace f) = f@
--      * Tensor: @trace (trace g) = trace (assoc . g . assoc')@
--
-- 4. __Yanking__. Tracing a swap is identity.
--
--      @trace swap = id@
--
-- And for 'trace' and 'untrace' specifically: @'trace' . 'untrace' = 'id'@.
-- 'untrace' is a section of 'trace'; round-tripping through
-- @'untrace' . 'trace'@ only recovers morphisms that were already of the
-- form @'untrace' f@.
--
-- Two tensor semantics are provided, corresponding to the standard
-- trace monoidal structures:
--
-- [@(,)@] A single lazy recursive binding.  @trace f b@ produces
-- @let (a, c) = f (a, b) in c@ — the feedback value @a@ and the
-- output @c@ are co-defined.  This is cyclic sharing, not iteration:
-- the body executes once with a self-referential channel.
-- Only works in a lazy setting — the feedback value is a self-referential
-- thunk.  In a strict language this binding is circular and divergent.
--
-- [@Either@] A while-loop.  @Left a@ feeds back into another iteration;
-- @Right c@ terminates.  The loop runs until a 'Right' is produced.
--
-- For effectful arrows, both tensors lift to 'Kleisli' @m@:
--
--   * @'MonadFix' m => 'Traced' ('Kleisli' m) (,)@ ties the lazy knot
--     via 'mfix'.
--
--   * @'Monad' m => 'Traced' ('Kleisli' m) 'Either'@ iterates via
--     plain recursion.  For 'IO' specifically, an overlapping instance
--     uses GHC's delimited-continuation primops ('prompt#', 'control0#')
--     for constant stack space.
--
-- /References:/
--
--   * Hasegawa (1997) — cartesian (cyclic-sharing) vs computational
--     (iterative) traces.  The @(,)@/@Either@ distinction.
--
--   * Kidney & Wu (2026) — hyperfunctions, producer-consumer pattern.
--
--   * Joyal, Street & Verity (1996) — trace monoidal categories.
#ifdef __GLASGOW_HASKELL__
module Circuit.Traced
  ( Traced (..),
    cellIO,
  )
where
#else
module Circuit.Traced
  ( Traced (..),
  )
where
#endif

#ifdef __GLASGOW_HASKELL__
import Control.Arrow (Kleisli (..))
import Control.Monad.Fix (MonadFix, mfix)
import Data.IORef
import GHC.Exts (PromptTag#, control0#, newPromptTag#, prompt#)
import GHC.IO (IO (..))
#endif

-- $setup
-- >>> import Control.Arrow (Kleisli (..), second)
-- >>> import Control.Category ((>>>))
-- >>> import Data.Either (fromRight)
-- >>> import Circuit.Traced

-- | A trace over a morphism @arr@ and tensor @t@.
--
-- @trace@ closes the feedback loop, eliminating the tensor channel.
-- @untrace@ opens the loop, lifting a plain morphism into the tensor.
class Traced arr t where
  trace :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)

-- * Cartesian tensor — lazy knot

-- | The cartesian trace ties a lazy knot: the feedback value @a@ and
-- output @c@ are produced simultaneously in a single recursive binding.
--
-- Only works in a lazy setting — the feedback value is a self-referential
-- thunk.  In a strict language this binding is circular and divergent.
-- Haskell's lazy evaluation makes cyclic sharing possible without an
-- explicit fixpoint operator.
--
-- >>> :{
-- let powers (ns, ()) =
--       (1 : map (*2) ns, take 5 ns)
-- :}
--
-- >>> trace powers () :: [Integer]
-- [1,2,4,8,16]
--
-- >>> trace (\(acc, x) -> (acc, x + 1)) 5
-- 6
--
-- Vanishing (a): tracing over the unit does nothing.
--
-- Note: using @()@ as the channel type hits a GHC black-hole detection
-- because @()@ has only one constructor. We test with 'Int' as the
-- channel instead — the channel value is unconstrained, so the trace
-- degenerates to plain function application.
--
-- >>> let f (x, a) = (x, a + 1)
-- >>> trace f 5
-- 6
--
-- prop> \n -> trace ((\(x, a) -> (x, a + n)) :: ((Int, Int) -> (Int, Int))) (0 :: Int) == (n :: Int)
--
-- Yanking: tracing a swap is the identity.
--
-- >>> let swap (x, y) = (y, x)
-- >>> trace swap 42
-- 42
--
-- prop> \x -> trace ((\(a, b) -> (b, a)) :: ((Int, Int) -> (Int, Int))) (x :: Int) == x
--
-- Tightening: payload morphisms pass freely through the trace.
--
-- >>> let f (x, a) = (x, a)
-- >>> trace (second (+1) . f . second (*2)) 5
-- 11
--
-- prop> \x -> trace (second ((+1) :: Int -> Int) . (id :: ((Int, Int) -> (Int, Int))) . second ((*2) :: Int -> Int)) (x :: Int) == x * 2 + 1
--
-- Sliding: a morphism on the channel slides from one side to the other.
--
-- >>> let swap (x, y) = (y, x)
-- >>> trace (second (+1) . swap) 5
-- 6
--
-- >>> trace (swap . second (+1)) 5
-- 6
--
-- prop> \x -> trace (second ((+1) :: Int -> Int) . ((\(a, b) -> (b, a)) :: ((Int, Int) -> (Int, Int)))) (x :: Int) == trace (((\(a, b) -> (b, a)) :: ((Int, Int) -> (Int, Int))) . second ((+1) :: Int -> Int)) x
--
-- Strength: an independent payload wire is invisible to the trace.
--
-- >>> let f (x, c) = (x, c + 1)
-- >>> let g (x, (a, c)) = (x', (a * 2, d)) where (x', d) = f (x, c)
-- >>> trace g (3, 5)
-- (6,6)
--
-- prop> \a c -> trace ((\(x, (p, q)) -> (x, (p + a, q + 1))) :: ((Int, (Int, Int)) -> (Int, (Int, Int)))) (0 :: Int, c :: Int) == (a :: Int, c + 1)
instance Traced (->) (,) where
  trace f b = let (a, c) = f (a, b) in c
  untrace = fmap

-- * Either tensor — iteration

-- | The Either trace iterates: 'Left' feeds back (continue), 'Right'
-- terminates (exit). A compact, under-appreciated pattern for loops in Haskell.
--
-- >>> :{
-- let fac (n, acc) | n <= 1    = Right acc
--                  | otherwise = Left (n - 1, n * acc)
-- :}
--
-- >>> trace (either fac fac) (5, 1 :: Int)
-- 120
--
-- >>> :{
-- let countdown = \case
--       Left n | n > 0 -> Left (n - 1)
--              | otherwise -> Right n
--       Right n | n > 0 -> Left (n - 1)
--               | otherwise -> Right n
-- :}
--
-- >>> trace countdown (3 :: Int)
-- 0
--
-- Vanishing (a): tracing over the unit does nothing.
--
-- >>> let f = Right . (+1) . fromRight undefined
-- >>> trace f 5
-- 6
--
-- prop> \n -> trace ((Right . (+ n) . fromRight (undefined :: Int)) :: (Either () Int -> Either () Int)) (0 :: Int) == (n :: Int)
--
-- Yanking: tracing a swap is the identity.
--
-- >>> :{
-- let swapEither (Left x)  = Right x
--     swapEither (Right x) = Left x
-- :}
--
-- >>> trace swapEither 42
-- 42
--
-- prop> \x -> trace ((\e -> case e of Left a -> Right a; Right a -> Left a) :: (Either Int Int -> Either Int Int)) (x :: Int) == x
--
-- Tightening: payload morphisms pass freely through the trace.
--
-- >>> let f = fmap ((+1) :: Int -> Int) . fmap ((*2) :: Int -> Int)
-- >>> trace (f :: Either () Int -> Either () Int) 5
-- 11
--
-- prop> \x -> trace (fmap ((+1) :: Int -> Int) . fmap ((*2) :: Int -> Int) :: Either () Int -> Either () Int) (x :: Int) == x * 2 + 1
instance Traced (->) Either where
  trace f b = go (Right b)
    where
      go x = case f x of
        Right c -> c
        Left a -> go (Left a)
  untrace = fmap

#ifdef __GLASGOW_HASKELL__

-- * Kleisli m (,) — lazy knot via MonadFix

-- | Traced for 'Kleisli' @m@ with the cartesian tensor, requiring @'MonadFix' m@.
--
-- The lazy knot is tied via 'mfix'. The feedback channel is lazy in the
-- recursive binding — the body must not force the feedback value before
-- producing it, or 'mfix' will diverge (just as the pure @(,)@ trace
-- black-holes on strict fields).
--
-- >>> :{
-- let fibs = Kleisli $ \(fibs, ()) ->
--       pure (0 : 1 : zipWith (+) fibs (drop 1 fibs), take 3 fibs)
-- :}
--
-- >>> runKleisli (trace fibs) ()
-- [0,1,1]
instance MonadFix m => Traced (Kleisli m) (,) where
  trace (Kleisli f) =
    Kleisli
      ( \b -> do
          (_, c) <- mfix $ \ ~(s, _) -> f (s, b)
          pure c
      )

  untrace (Kleisli f) =
    Kleisli
      ( \(a, b) -> do
          c <- f b
          pure (a, c)
      )

-- * Kleisli m Either — iteration for any Monad

-- | Traced for 'Kleisli' @m@ with the 'Either' tensor, for any @'Monad' m@.
--
-- Iterates by feeding 'Left' back into the step function until a 'Right'
-- is produced. Uses plain recursion — builds stack proportional to
-- iteration count.
--
-- >>> :{
-- let countTo target = Kleisli $ \case
--       Left n | n < target -> pure (Left (n + 1))
--              | otherwise  -> pure (Right n)
--       Right ()            -> pure (Left 0)
-- :}
--
-- >>> runKleisli (trace (countTo (3 :: Int))) ()
-- 3
--
-- This instance is @OVERLAPPABLE@: the IO-specific instance below takes
-- priority for 'IO', providing constant-stack iteration via delimited
-- continuations.
instance {-# OVERLAPPABLE #-} Monad m => Traced (Kleisli m) Either where
  trace (Kleisli f) =
    Kleisli $ \b -> go (Right b)
      where
        go x = f x >>= \case
          Right c -> pure c
          Left a -> go (Left a)

  untrace (Kleisli f) =
    Kleisli $ \case
      Left a -> pure (Left a)
      Right b -> Right <$> f b

-- * Kleisli IO Either — delimited continuations (constant stack)

-- | GHC delimited-continuation primops.
data PromptTag a = PromptTag (PromptTag# a)

-- | Create a new prompt tag for delimited continuations.
newPromptTag :: IO (PromptTag a)
newPromptTag =
  IO
    ( \s ->
        case newPromptTag# s of
          (# s', t #) -> (# s', PromptTag t #)
    )

-- | Run an IO computation under a prompt boundary.
prompt :: PromptTag a -> IO a -> IO a
prompt (PromptTag t) (IO m) = IO (prompt# t m)

-- | Captures the continuation up to the nearest prompt with the matching tag.
control0 :: forall a b. PromptTag a -> ((IO b -> IO a) -> IO a) -> IO b
control0 (PromptTag t) f = IO (control0# t arg)
  where
    arg f# s = case f (\(IO x) -> IO (f# x)) of IO m -> m s

-- | Traced for 'Kleisli' 'IO' with 'Either' tensor.
--
-- Each iteration re-establishes the prompt boundary. When @control0@
-- fires on @Left a@, it captures the continuation, wraps it around
-- the next loop step, and jumps back to the prompt — constant stack.
--
-- >>> :{
-- let exit42 = Kleisli $ \case
--       Right () -> pure (Right (42 :: Int))
-- :}
--
-- >>> runKleisli (trace exit42) ()
-- 42
instance {-# OVERLAPPING #-} Traced (Kleisli IO) Either where
  trace (Kleisli body) =
    Kleisli
      ( \initial -> do
          tag <- newPromptTag
          let go x =
                prompt tag $
                  body x
                    >>= ( \case
                            Right c -> pure c
                            Left a -> control0 tag (\k -> k (go (Left a)))
                        )
          go (Right initial)
      )

  untrace (Kleisli f) =
    Kleisli
      ( \case
          Left a -> pure (Left a)
          Right b -> Right <$> f b
      )

-- * Stateful stages via IORef

-- | Create a stateful 'Kleisli' 'IO' arrow backed by 'IORef'.
--
-- Allocates a mutable reference once, then each invocation reads the
-- current state, applies the transfer function, writes the new state
-- back, and returns the output. The 'IORef' is hidden inside the
-- arrow — callers see a pure @Kleisli IO a b@.
--
-- This breaks the circular dependency that 'MonadFix' requires for
-- the 'Traced' @(,)@ instance: the feedback value is stored in the
-- mutable cell rather than being self-referential. Strict accumulators
-- (counters, frequency tables, running sums) work without diverging.
#ifdef __GLASGOW_HASKELL__
cellIO
  :: s
  -- ^ initial state
  -> (s -> a -> IO (s, b))
  -- ^ transfer: current state and input yield next state and output
  -> IO (Kleisli IO a b)
cellIO s0 step = do
  ref <- newIORef s0
  pure $
    Kleisli $ \a -> do
      s <- readIORef ref
      (s', b) <- step s a
      writeIORef ref s'
      pure b
#endif

#endif
