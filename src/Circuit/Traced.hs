{-# LANGUAGE CPP #-}
#ifdef __GLASGOW_HASKELL__
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
#endif

-- | The trace: feedback in a monoidal category.
--
-- 'Trace' generalises the ability to close a feedback loop. For each
-- tensor @t@, a 'Trace' instance specifies what \"feedback\" means:
--
--   * @(,)@ — lazy knot: output and feedback are produced simultaneously.
--     @trace f b = let (a, c) = f (a, b) in c@.
--
--   * @Either@ — iteration: @Left a@ feeds back (continue), @Right c@
--     terminates (exit). The loop runs until a 'Right' is produced.
--
-- Together these instances supply the 'Trace' constraints that
-- 'Circuit.Circuit''s @lower@ function dispatches on when it encounters
-- a 'Knot', making 'Circuit' the free traced monoidal category over any
-- base arrow with a tensor.
--
-- * Delimited continuations
--
-- The @Trace (Kleisli IO) Either@ instance uses GHC's delimited
-- continuation primops (@prompt#@ / @control0#@) to run IO loops in
-- constant stack space. Each iteration re-enters at the prompt boundary
-- rather than building up a call stack.
--
-- Correspondence with delimited continuation operators:
--
-- @
--   Trace (Kleisli IO) Either   ≅   delimited continuations
--   trace / reset               ≅   prompt
--   feedback Left               ≅   shift / control0
--   exit Right                  ≅   return from reset
-- @
--
-- These instances require GHC; they are omitted on other compilers.
module Circuit.Traced
  ( Trace (..),
  )
where

#ifdef __GLASGOW_HASKELL__
import Control.Arrow (Kleisli (..))
import Data.IORef (newIORef, readIORef, writeIORef)
import GHC.Exts (PromptTag#, control0#, newPromptTag#, prompt#)
import GHC.IO (IO (..))
import System.IO.Unsafe (unsafeInterleaveIO)
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
class Trace arr t where
  trace :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)

-- * Cartesian tensor — lazy knot

-- | The cartesian trace ties a lazy knot: the feedback value @a@ and
-- output @c@ are produced simultaneously in a single recursive binding.
--
-- >>> take 5 (trace (\(fibs, ()) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs)) () :: [Integer])
-- [0,1,1,2,3]
--
-- Vanishing (a): tracing over the unit does nothing.
--
-- Note: using @()@ as the channel type hits a GHC black-hole detection
-- because @()@ has only one constructor. We test with 'Int' as the
-- channel instead — the channel value is unconstrained, so the trace
-- degenerates to plain function application.
--
-- >>> let f (x, a) = (x, a + 1) in trace f 5
-- 6
--
-- prop> \n -> trace ((\(x, a) -> (x, a + n)) :: ((Int, Int) -> (Int, Int))) (0 :: Int) == (n :: Int)
--
-- Yanking: tracing a swap is the identity.
--
-- >>> let swap (x, y) = (y, x) in trace swap 42
-- 42
--
-- prop> \x -> trace ((\(a, b) -> (b, a)) :: ((Int, Int) -> (Int, Int))) (x :: Int) == x
--
-- Tightening: payload morphisms pass freely through the trace.
--
-- >>> let f (x, a) = (x, a) in trace (second (+1) . f . second (*2)) 5
-- 11
--
-- prop> \x -> trace (second ((+1) :: Int -> Int) . (id :: ((Int, Int) -> (Int, Int))) . second ((*2) :: Int -> Int)) (x :: Int) == x * 2 + 1
--
-- Sliding: a morphism on the channel slides from one side to the other.
--
-- >>> let swap (x, y) = (y, x) in trace (second (+1) . swap) 5
-- 6
--
-- >>> let swap (x, y) = (y, x) in trace (swap . second (+1)) 5
-- 6
--
-- prop> \x -> trace (second ((+1) :: Int -> Int) . ((\(a, b) -> (b, a)) :: ((Int, Int) -> (Int, Int)))) (x :: Int) == trace (((\(a, b) -> (b, a)) :: ((Int, Int) -> (Int, Int))) . second ((+1) :: Int -> Int)) x
--
-- Strength: an independent payload wire is invisible to the trace.
--
-- >>> let f (x, c) = (x, c + 1) in trace (\(x, (a, c)) -> let (x', d) = f (x, c) in (x', (a * 2, d))) (3, 5)
-- (6,6)
--
-- prop> \a c -> trace ((\(x, (p, q)) -> (x, (p + a, q + 1))) :: ((Int, (Int, Int)) -> (Int, (Int, Int)))) (0 :: Int, c :: Int) == (a :: Int, c + 1)
instance Trace (->) (,) where
  trace f b = let (a, c) = f (a, b) in c
  untrace = fmap

-- * Either tensor — iteration

-- | The Either trace iterates: 'Left' feeds back (continue), 'Right'
-- terminates (exit). A compact, under-appreciated pattern for loops in Haskell.
--
-- >>> trace (\x -> case x of Right n | n < 3 -> Left (n + 1); _ -> Right ()) (0 :: Int)
-- ()
--
-- >>> let step n = if n < 3 then Left (n + 1) else Right n in trace (either step step) (0 :: Int)
-- 3
--
-- Vanishing (a): tracing over the unit does nothing.
--
-- >>> let f = Right . (+1) . fromRight undefined in trace f 5
-- 6
--
-- prop> \n -> trace ((Right . (+ n) . fromRight (undefined :: Int)) :: (Either () Int -> Either () Int)) (0 :: Int) == (n :: Int)
--
-- Yanking: tracing a swap is the identity.
--
-- >>> let swapEither (Left x) = Right x; swapEither (Right x) = Left x in trace swapEither 42
-- 42
--
-- prop> \x -> trace ((\e -> case e of Left a -> Right a; Right a -> Left a) :: (Either Int Int -> Either Int Int)) (x :: Int) == x
--
-- Tightening: payload morphisms pass freely through the trace.
--
-- >>> trace (fmap ((+1) :: Int -> Int) . fmap ((*2) :: Int -> Int) :: Either () Int -> Either () Int) 5
-- 11
--
-- prop> \x -> trace (fmap ((+1) :: Int -> Int) . fmap ((*2) :: Int -> Int) :: Either () Int -> Either () Int) (x :: Int) == x * 2 + 1
instance Trace (->) Either where
  trace f b = go (Right b)
    where
      go x = case f x of
        Right c -> c
        Left a -> go (Left a)
  untrace = fmap

#ifdef __GLASGOW_HASKELL__

-- * Kleisli IO (,) — lazy knot via IORef

-- | ⚠️ UNSAFE: Lazy knot tying for @Kleisli IO@ with the cartesian tensor.
--
-- The feedback value is tied via an 'IORef' and 'unsafeInterleaveIO'.
-- This defies IO's ordering guarantees — the knot crashes at runtime if
-- the body forces the feedback channel before the 'writeIORef' completes.
--
-- Safe only when the body is lazy in the feedback channel (the first
-- component of the pair), which holds for circuits built from 'ambient',
-- 'preC', 'postC', and plain 'Kleisli' arrows. Composition with effects
-- that sequence strictly may break the knot silently.
--
-- >>> runKleisli (trace (Kleisli $ \(fibs, ()) -> pure (0 : 1 : zipWith (+) fibs (drop 1 fibs), take 3 fibs))) ()
-- [0,1,1]
instance Trace (Kleisli IO) (,) where
  trace (Kleisli f) =
    Kleisli
      ( \b -> do
          ref <- newIORef (error "Trace (Kleisli IO) (,): knot not tied")
          a <- unsafeInterleaveIO (readIORef ref)
          (a', c) <- f (a, b)
          writeIORef ref a'
          pure c
      )

  untrace (Kleisli f) =
    Kleisli
      ( \(a, b) -> do
          c <- f b
          pure (a, c)
      )

-- * Kleisli IO Either — delimited continuations

-- | GHC delimited-continuation primops.
data PromptTag a = PromptTag (PromptTag# a)

newPromptTag :: IO (PromptTag a)
newPromptTag =
  IO
    ( \s ->
        case newPromptTag# s of
          (# s', t #) -> (# s', PromptTag t #)
    )

prompt :: PromptTag a -> IO a -> IO a
prompt (PromptTag t) (IO m) = IO (prompt# t m)

-- | Captures the continuation up to the nearest prompt with the matching tag.
control0 :: forall a b. PromptTag a -> ((IO b -> IO a) -> IO a) -> IO b
control0 (PromptTag t) f = IO (control0# t arg)
  where
    arg f# s = case f (\(IO x) -> IO (f# x)) of IO m -> m s

-- | Trace for 'Kleisli' 'IO' with 'Either' tensor.
--
-- Each iteration re-establishes the prompt boundary. When 'control0'
-- fires on @Left a@, it captures the continuation, wraps it around
-- the next loop step, and jumps back to the prompt — constant stack.
--
-- >>> runKleisli (trace (Kleisli $ \case Right () -> pure (Right (42 :: Int)))) ()
-- 42
instance Trace (Kleisli IO) Either where
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

#endif
