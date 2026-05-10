{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

-- | Coroutines as Hyper, Trace→Hyper, and delimited-continuation coroutines.
--
-- Three questions:
--   1. Can we encode a coroutine (Coro s i o) directly as a Hyper?
--   2. Can we use delimited continuations (prompt/control0) for heap coroutines?
--   3. Can Trace instances be expressed as Hyper combinators?

import Circuit.Hyper
  ( Hyper (..),
    run,
    base,
    lift,
    lower,
    invoke,
    ana,
    valueFix,
    (⇸),
    (⊲),
    (↓),
    (⥁),
  )
import Circuit.Traced
  ( Trace (..),
    PromptTag,
    newPromptTag,
    prompt,
    control0,
  )
import Prelude hiding (id, (.))
import Control.Category ((.), id)

import Data.IORef
import Data.These (These (..))

-- ==========================================================================
-- 1. Coro → Channel (Hyper encoding)
-- ==========================================================================

-- | The state-machine coroutine from stable-marriage.hs.
data Coro s i o = Coro
  { coStep  :: s -> i -> (o, s)
  , coState :: s
  }

sendCoro :: Coro s i o -> i -> (o, Coro s i o)
sendCoro co i = let (o, s') = coStep co (coState co) i
                in (o, co { coState = s' })

-- | Channel r i o = (o → r) ↬ (i → r)
--   A coroutine that consumes i, produces o, with result extraction r.
type Channel r i o = Hyper (o -> r) (i -> r)

-- | Encode a Coro as a Channel.
--   Given a way to extract the result from the final state (done :: s -> r),
--   build a Channel that at each step: receives i, applies the step function,
--   produces o via the dual channel, and recurses with the new state.
--
--   This is the fundamental encoding: the coroutine's state s is captured
--   in the closure chain of 'go'.
coroToChannel :: Coro s i o -> (s -> r) -> Channel r i o
coroToChannel (Coro step s0) done = go s0
  where
    go s = Hyper $ \out i ->
      let (o, s') = step s i
      in invoke out (go s') o

-- | Run a Channel to completion, extracting the result.
--   Provide an initial input to kick it off, and a result extractor.
runChannel :: Channel r i o -> i -> (s -> r) -> r
runChannel ch i done = undefined -- needs the state s, which is hidden

-- Actually, the state s is internal to the Channel. To extract r, we
-- need to run the Channel until it signals "done." But how does it
-- signal done? Through the protocol.
--
-- Variant: use Maybe o as output — Nothing signals done.

-- | A Channel that can signal completion via Maybe output.
--   When the coroutine is done, it returns Nothing instead of producing.
type TermChannel r i o = Channel r i (Maybe o)

-- | Encode a finite Coro (with termination) as a TermChannel.
--   step returns Maybe output — Nothing means done.
data CoroTerm s i o = CoroTerm
  { ctStep  :: s -> i -> (Maybe o, s)
  , ctState :: s
  }

coroTermToChannel :: forall s i o r. CoroTerm s i o -> (s -> r) -> TermChannel r i o
coroTermToChannel (CoroTerm step s0) done = go s0
  where
    go :: s -> TermChannel r i o
    go s = Hyper $ \out i ->
      case step s i of
        (Nothing, _) -> done s
        (Just o, s') -> invoke out (go s') (Just o)

-- | Drive a TermChannel with inputs. When the channel produces Nothing,
--   the result r is returned.
driveChannel :: TermChannel r i o -> [i] -> r
driveChannel ch = go ch
  where
    go _ [] = error "Channel underflow"
    go ch (i:is) = undefined  -- can't pattern-match on Channel to see if it produced

-- The issue: Channel is opaque. We can't tell whether it produced
-- Nothing or Just without invoking it. We need a different interface.
-- The Producer/Consumer pattern solves this: the Consumer consumes
-- the Producer's output and decides when to stop.

-- ==========================================================================
-- 2. Trace instances as Hyper combinators
-- ==========================================================================

-- | Each Trace instance gives a different iteration protocol.
--   These can be expressed as Hyper patterns.

-- ---------------------------------------------------------------------------
-- 2a. Trace (->) Either ≈ Producer/Consumer with Maybe
-- ---------------------------------------------------------------------------

-- Trace (->) Either: Left = feedback (continue), Right = output (stop).
-- This is: iterate a function f :: Either a b -> Either a c until Right.
--
-- Hyper equivalent: Producer sends Just for each Left step, Nothing for Right.
-- Consumer processes each Just and accumulates.
--
-- The coinductive Consumer 'h = cons step h' IS the trace loop.

-- traceToHyper, traceEitherAsHyper, traceProducer, traceConsumer:
-- (Exploratory sketches — see channel.md for the working Producer/Consumer
-- encoding of Either-trace as Producer of 'a' values driven by a Consumer.)

-- ==========================================================================
-- 2b. Trace (->) (,) — lazy knot as Hyper run
-- ==========================================================================

-- Trace (->) (,): f (a, b) = (a, c) — a is simultaneously produced and consumed.
-- The lazy knot ties a to itself: let (a, c) = f (a, b) in c.
--
-- Hyper equivalent: 'run' ties the same knot at the type level.
--   run :: Hyper a a -> a
--   run h = invoke h (Hyper run)
--
-- For productive knots (e.g., Fibonacci), 'run' on a self-referential Hyper
-- gives the lazy knot semantics directly:

-- | Fibonacci via Hyper run. The self-reference in 'fibs' IS the lazy knot.
--   run ties the recursive knot: run h = invoke h (Hyper run).
tracePairFib :: [Int]
tracePairFib = run h
  where
    h :: Hyper [Int] [Int]
    h = Hyper $ \_ ->    -- ignore continuation — knot is in the data
      let fibs = 0 : 1 : zipWith (+) fibs (tail fibs)
      in fibs

-- ==========================================================================
-- 2c. Trace (->) These — dual-channel iteration
-- ==========================================================================

-- Trace (->) These: This a = feedback silently, That c = stop with output,
--   These a c = feedback AND output simultaneously.
--
-- Hyper equivalent: a Producer that sometimes emits output while continuing.
--   The These tensor allows "emit AND continue" vs Either's "emit OR continue."
--
-- This maps to a Producer where the message type includes both output and
-- a signal to continue: Producer (Maybe (a, c)) r — where Just (a, c) means
-- "here's output c, and here's the next feedback a."

-- ==========================================================================
-- 3. Delimited continuations for heap-allocated coroutines
-- ==========================================================================

-- | A coroutine is a computation that can yield values and be resumed.
--   With delimited continuations (prompt/control0), we can capture the
--   "rest of the computation" and store it on the heap.
--
--   The pattern:
--     1. prompt sets a boundary for continuation capture
--     2. yield calls control0 to capture the continuation up to prompt
--     3. The continuation is stored (IORef)
--     4. When resumed, the continuation is invoked with the input

-- | The "heap-allocated coroutine" pattern: a coroutine stored in an IORef.
--   When resumed with input i, produces output o and a new CoIO (the continuation).
newtype CoIO i o = CoIO (IORef (i -> IO (o, CoIO i o)))

-- (coroutine creation with delimited continuations: sketched.
--  The paper uses callCC; with prompt/control0 the pattern is:
--    prompt tag (coroutineBody)
--  where coroutineBody uses yieldIO to suspend. See paper §5.2.)

-- | yield captures the continuation and stores it for later resume.
--   The prompt tag type must match the yield type — the prompt's result IS
--   the yielded value. When the coroutine yields o, control0 captures the
--   continuation k :: IO i -> IO o (resume with input i, eventually yield o).
--   The continuation is stored in the IORef. The yielded o is returned
--   through the prompt.
yieldIO :: PromptTag o -> o -> IORef (i -> IO o) -> IO i
yieldIO tag o ref = control0 tag $ \k -> do
  writeIORef ref (\i -> k (pure i))  -- store continuation for later resume
  pure o                              -- return yielded value through prompt

-- Let me look at the paper's pattern more carefully.
-- The paper uses callCC (undelimited). With delimited continuations,
-- the pattern is cleaner because prompt bounds the capture.
--
-- The key pattern (from paper §5.2):
--   yield o = Co (\k -> Hyp (\h i -> invoke h (k i) o))
--   send c v = callCC (\k -> ... invoke (route c ...) ...)
--
-- With prompt/control0, 'yield' becomes:
--   1. control0 captures the continuation up to prompt
--   2. Store it in an IORef
--   3. Return the yielded value through the prompt
-- 'send' becomes:
--   1. Read the stored continuation from IORef
--   2. Apply it to the input value
--   3. The coroutine runs until next yield

-- ==========================================================================
-- 4. loopToHyper: each Trace tensor as a single Hyper
-- ==========================================================================

-- | The function-space trick: absorb the feedback type into the Hyper's
--   domain by using @Hyper (s -> r) (s -> r)@ where @s@ carries both
--   feedback and input. 'run' ties the recursive knot.
--
--   Unlike 'toHyper (Knot f) = lift (trace f)', which flattens the loop,
--   these encodings preserve the loop structure inside the Hyper.

-- ---------------------------------------------------------------------------
-- 4a. Either tensor — iterate until Right
-- ---------------------------------------------------------------------------

-- | Encode @Trace (->) Either@ as a single Hyper.
--   State @s = Either a b@ carries both feedback @a@ and input @b@.
--
--   >>> run (loopEither f) (Right (5 :: Int))
--   (same as trace f 5)
loopEither :: (Either a b -> Either a c) -> Hyper (Either a b -> c) (Either a b -> c)
loopEither f = h
  where
    h = Hyper $ \k s ->
      case f s of
        Right c -> c
        Left a  -> invoke k h (Left a)

-- | Run the Either-loop from an initial input.
runEither :: (Either a b -> Either a c) -> b -> c
runEither f b = run (loopEither f) (Right b)

-- ---------------------------------------------------------------------------
-- 4b. (,) tensor — lazy knot
-- ---------------------------------------------------------------------------

-- | Encode @Trace (->) (,)@ as a single Hyper.
--   The lazy knot @let (a, c) = f (a, b) in c@ is tied by 'run'.
--   No function-space trick needed — the Hyper is simply 'Hyper c c'.
--
--   >>> run (loopPair f) 5
--   (same as trace f 5)
-- (loopPair and loopPairCorrect: incomplete sketches. The (,) trace
--  ties 'a' to itself via a lazy knot. 'run' alone isn't enough —
--  valueFix or explicit self-reference in the data is needed.
--  See loopPairFib for a concrete example, and loopPairFull for
--  the valueFix approach.)

-- | For productive knots, the Hyper ignores its continuation
--   and the lazy knot is in the data (as in tracePairFib above).
loopPairFib :: Hyper [Int] [Int]
loopPairFib = lift $ \_ ->
  let fibs = 0 : 1 : zipWith (+) fibs (tail fibs)
  in fibs

-- ---------------------------------------------------------------------------
-- 4c. These tensor — iterate with optional output
-- ---------------------------------------------------------------------------

-- | Encode @Trace (->) These@ as a single Hyper.
--   State @s = These a b@. @That c@ terminates with output.
--   @This a@ continues silently. @These a c@ continues AND produces output.
--   (Output on @These@ is consumed by the caller via composition.)
loopThese :: (These a b -> These a c) -> Hyper (These a b -> c) (These a b -> c)
loopThese f = h
  where
    h = Hyper $ \k s ->
      case f s of
        That c    -> c
        This a    -> invoke k h (This a)
        These a _ -> invoke k h (This a)  -- output consumed, continue

runThese :: (These a b -> These a c) -> b -> c
runThese f b = run (loopThese f) (That b)

-- ==========================================================================
-- 5. loopToHyper: dispatch on tensor
-- ==========================================================================

-- | Convert a Knot body directly to a Hyper, preserving the loop structure.
--   Dispatches on the tensor type.
class KnotToHyper t where
  type KnotState t a b :: *
  loopToHyper :: ((t a b) -> (t a c)) -> Hyper (LoopState t a b -> c) (LoopState t a b -> c)
  runKnot :: ((t a b) -> (t a c)) -> b -> c

instance KnotToHyper Either where
  type KnotState Either a b = Either a b
  loopToHyper = loopEither
  runKnot = runEither

instance KnotToHyper These where
  type KnotState These a b = These a b
  loopToHyper = loopThese
  runKnot = runThese

-- For (,) the encoding is different — 'valueFix' not 'run'.
-- Included for completeness but the pattern differs from Either/These.

-- ==========================================================================
-- Tests
-- ==========================================================================

-- Test Either-loop: counting loop from Traced.hs
testEitherCount :: Int -> Int
testEitherCount = runEither f
  where
    f (Right n) | n < 3    = Left (n + 1)
                | otherwise = Right n
    f (Left n)  | n < 3    = Left (n + 1)
                | otherwise = Right n

-- Test These-loop
testTheseCount :: Int -> Int
testTheseCount = runThese f
  where
    f (That n)    | n < 3    = This (n + 1)
                  | otherwise = That n
    f (This n)    | n < 3    = This (n + 1)
                  | otherwise = That n
    f (These n _) | n < 3    = This (n + 1)
                  | otherwise = That n

-- ==========================================================================
-- Main: demonstrate the encodings
-- ==========================================================================

main :: IO ()
main = do
  putStrLn "=== Trace (->) (,) as Hyper run (Fibonacci) ==="
  print (take 10 tracePairFib)
  putStrLn "Expected: [0,1,1,2,3,5,8,13,21,34]"
  putStrLn ""
  putStrLn "=== loopEither (counting to 3) ==="
  print (testEitherCount 0)
  print (testEitherCount 2)
  print (testEitherCount 5)
  putStrLn "Expected: 3, 3, 5"
  putStrLn ""
  putStrLn "=== loopThese (counting to 3) ==="
  print (testTheseCount 0)
  print (testTheseCount 2)
  print (testTheseCount 5)
  putStrLn "Expected: 3, 3, 5"
