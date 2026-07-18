-- | Queue strategies and ends for circuits — pure and STM.
--
-- The 'Queue' type describes buffering semantics (Unbounded, Bounded,
-- Single, Latest, Newest).  Two families of ends:
--
-- * 'endsSTM' — STM mutables, blocking reads.
-- * 'endsPure' — pure @[a]@ state, 'Bool'/'Maybe' for partiality.
--
-- 'endsQueue' creates a dual pair of circuit ends sharing an STM channel.
-- 'push' and 'pop' lift pure ends into 'Circuit's with state threaded
-- through the tensor.  All four are polymorphic in the tensor @t@.
module Circuit.Queue
  ( -- * Queue strategies
    Queue (..),

    -- * Queue ends
    endsSTM,
    endsPure,

    -- * Circuit ends (STM)
    endsQueue,
    closeQueue,

    -- * Ends product
    Ends (..),
    openSTM,

    -- * Type aliases
    WireK,
    Emit,
    Commit,

    -- * State-threading lifters
    push,
    pop,
    drain,
    snapshot,

    -- * Box view
    boxOf,
  )
where

import Circuit.Classes ((>>>))
import Circuit.Ends (openK)
import Circuit.Layer (run)
import Circuit.Monoidal (Tensor (..))
import Circuit.Trace (In (..), Out (..), Trace (..), Traced, runIn, runOut)
import Control.Applicative
import Control.Arrow (Kleisli (..))
import Control.Concurrent.STM
import Control.Monad (void)
import Control.Monad.Fix (MonadFix)
import Prelude

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XNondecreasingIndentation
-- >>> import Circuit (Trace(..), run, par)
-- >>> import Circuit.Classes ((>>>))
-- >>> import Circuit.Ends (open, openK)
-- >>> import Circuit.Queue
-- >>> import Circuit.Trace (In(..), Out(..), runIn, runOut, close)
-- >>> import Control.Arrow (Kleisli(..), runKleisli)
-- >>> import Control.Concurrent.STM (STM, TQueue, atomically, newTQueueIO, readTQueue, writeTQueue)
-- >>> import Data.Profunctor (lmap, rmap)

-- ---------------------------------------------------------------------------
-- Type aliases
-- ---------------------------------------------------------------------------

-- | A wire over 'Kleisli' @m@ with the @(,)@ tensor, by convention.
-- 'endsQueue' and 'closeQueue' are polymorphic in the tensor; this alias
-- pins it for readability.
type WireK m = Trace (,) (Kleisli m)

-- | Unit-grounded harvest port (@() → a@).
--
-- Same shape as plugging free 'Out' against unit 'In':
-- @'runIn' outA inU :: Trace t arr () a@.
-- Free ends remain 'In'/'Out'; this alias is only the port shape over
-- 'Kleisli' @m@ (historical name — prefer speaking in In/Out).
--
-- >>> import Circuit (run)
-- >>> import Circuit.Ends (open)
-- >>> import Circuit.Trace (runIn)
-- >>> let (outA, _inA) = open ("emit me" :: String)
-- >>> let (_outU, inU) = open ()
-- >>> run (runIn outA inU) ()
-- "emit me"
type Emit m a = WireK m () a

-- | Unit-grounded feed port (@a → ()@).
--
-- Same shape as plugging free 'In' against unit 'Out':
-- @'runOut' inA outU :: Trace t arr a ()@.
--
-- >>> import Circuit (run)
-- >>> import Circuit.Ends (open)
-- >>> import Circuit.Trace (runOut)
-- >>> let (_outA, inA) = open ("consume me" :: String)
-- >>> let (outU, _inU) = open ()
-- >>> run (runOut inA outU) "payload"
-- ()
type Commit m a = WireK m a ()

-- ---------------------------------------------------------------------------
-- Queue strategies
-- ---------------------------------------------------------------------------

-- | How messages are queued between producer and consumer.
data Queue a
  = -- | Unbounded FIFO queue.
    Unbounded
  | -- | Bounded FIFO with backpressure (write blocks when full).
    Bounded Int
  | -- | Single-slot buffer (write rejects when full — MVar-style A).
    -- Overwrite-on-full (B) is 'SwapQ'.
    Single
  | -- | Single-slot buffer, overwrite-on-full (B semantics — swapTMVar).
    -- Write always succeeds; read empties.
    SwapQ
  | -- | Always holds the latest value (overwrites, never blocks).
    Latest a
  | -- | Like 'Bounded' but drops oldest when full.
    Newest Int
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- STM ends
-- ---------------------------------------------------------------------------

-- | Create STM write/read ends for a queue strategy.
--
-- @
-- endsSTM :: Queue a -> STM (a -> STM (), STM a)
-- @
--
-- The read end blocks until a value is available.  Write behaviour
-- varies by strategy:
--
-- [/Unbounded/] Never blocks on write.
-- [/Bounded n/] Blocks on write when @n@ items are queued.
-- [/Single/] MVar-style: blocks on write when full (A semantics).
-- [/Latest a/] Never blocks; always holds a value (seed @a@ initially).
-- [/Newest n/] Never blocks on write (drops oldest); blocks on empty read.
--
-- === Unbounded
--
-- >>> (w, r) <- atomically (endsSTM Unbounded :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 1 >> w 2
-- >>> atomically r
-- 1
-- >>> atomically r
-- 2
--
-- Multi-op compose in one transaction:
--
-- >>> (w, r) <- atomically (endsSTM Unbounded :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 1 >> w 2 >> r
-- 1
--
-- === Bounded
--
-- >>> (w, r) <- atomically (endsSTM (Bounded 2) :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 1 >> w 2
-- >>> atomically r
-- 1
-- >>> atomically r
-- 2
-- >>> atomically (w 3)  -- succeeds: reads drained the queue
-- >>> atomically r
-- 3
--
-- === Single (A: MVar-style — write blocks when full)
--
-- >>> (w, r) <- atomically (endsSTM (Single :: Queue Int) :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 42
-- >>> atomically r
-- 42
-- >>> atomically $ w 99 >> r  -- compose: write then read in one transaction
-- 99
--
-- === SwapQ (B: swapTMVar-style — write always succeeds, overwriting)
--
-- >>> (w, r) <- atomically (endsSTM (SwapQ :: Queue Int) :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 1 >> w 2  -- second write overwrites the first
-- >>> atomically r
-- 2
-- >>> (w2, r2) <- atomically (endsSTM (SwapQ :: Queue Int) :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w2 5 >> r2  -- compose: write then read in one transaction
-- 5
--
-- === Latest (always holds a value, never blocks)
--
-- >>> (w, r) <- atomically (endsSTM (Latest 0) :: STM (Int -> STM (), STM Int))
-- >>> atomically r
-- 0
-- >>> atomically $ w 5
-- >>> atomically r
-- 5
-- >>> atomically $ w 7 >> r  -- compose: overwrite then read
-- 7
--
-- === Newest (bounded; drops oldest when full)
--
-- >>> (w, r) <- atomically (endsSTM (Newest 2) :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 1 >> w 2 >> w 3  -- 3rd write drops oldest (1)
-- >>> atomically r
-- 2
-- >>> atomically r
-- 3
endsSTM :: Queue a -> STM (a -> STM (), STM a)
endsSTM = \case
  Bounded n -> do
    q <- newTBQueue (fromIntegral n)
    pure (writeTBQueue q, readTBQueue q)
  Unbounded -> do
    q <- newTQueue
    pure (writeTQueue q, readTQueue q)
  Single -> do
    m <- newEmptyTMVar
    pure (putTMVar m, takeTMVar m)
  SwapQ -> do
    v <- newEmptyTMVar
    let write x = tryPutTMVar v x >>= \case True -> pure (); False -> void (swapTMVar v x)
    pure (write, takeTMVar v)
  Latest a -> do
    t <- newTVar a
    pure (writeTVar t, readTVar t)
  Newest n -> do
    q <- newTBQueue (fromIntegral n)
    let write x = writeTBQueue q x <|> (tryReadTBQueue q *> write x)
    pure (write, readTBQueue q)

-- ---------------------------------------------------------------------------
-- Pure ends
-- ---------------------------------------------------------------------------

-- | Create pure write/read ends for a queue strategy.
--
-- All strategies operate on a @[a]@ buffer.  'Bool' signals write
-- acceptance; 'Maybe' signals value availability.
--
-- === Unbounded
--
-- >>> let (w_ub, r_ub) = endsPure (Unbounded :: Queue Int)
-- >>> let (ub1, ow1) = w_ub 1 []
-- >>> ow1
-- True
-- >>> let (ub2, ow2) = w_ub 2 ub1
-- >>> ow2
-- True
-- >>> r_ub ub2
-- ([2],Just 1)
-- >>> r_ub []
-- ([],Nothing)
--
-- === Bounded
--
-- >>> let (w_b, r_b) = endsPure (Bounded 2 :: Queue Int)
-- >>> let (bb1, bw1) = w_b 1 []
-- >>> bw1
-- True
-- >>> let (bb2, bw2) = w_b 2 bb1
-- >>> bw2
-- True
-- >>> let (bb3, bw3) = w_b 3 bb2
-- >>> bw3
-- False
-- >>> r_b bb2
-- ([2],Just 1)
-- >>> r_b []
-- ([],Nothing)
--
-- === Single (A: MVar-style — write rejects when full)
--
-- >>> let (w_s, r_s) = endsPure (Single :: Queue Int)
-- >>> let (sb1, sw1) = w_s 1 []
-- >>> sw1
-- True
-- >>> let (sb2, sw2) = w_s 2 sb1
-- >>> sw2
-- False
-- >>> sb2
-- [1]
-- >>> r_s sb1
-- ([],Just 1)
-- >>> r_s []
-- ([],Nothing)
--
-- === SwapQ (B: swapTMVar-style — write always succeeds, overwriting)
--
-- >>> let (w_sw, r_sw) = endsPure (SwapQ :: Queue Int)
-- >>> let (sw1, swok1) = w_sw 1 []
-- >>> swok1
-- True
-- >>> sw1
-- [1]
-- >>> let (sw2, swok2) = w_sw 2 sw1
-- >>> swok2
-- True
-- >>> sw2
-- [2]
-- >>> r_sw sw1
-- ([],Just 1)
-- >>> r_sw []
-- ([],Nothing)
--
-- === Latest (read never empties; returns seed when empty)
--
-- >>> let (w_l, r_l) = endsPure (Latest 0 :: Queue Int)
-- >>> r_l []
-- ([],Just 0)
-- >>> let (lb1, _) = w_l 5 []
-- >>> r_l lb1
-- ([5],Just 5)
-- >>> let (lb2, _) = w_l 7 lb1
-- >>> r_l lb2
-- ([7],Just 7)
--
-- === Newest (bounded; drops oldest when full)
--
-- >>> let (w_n, r_n) = endsPure (Newest 2 :: Queue Int)
-- >>> let (nb1, _) = w_n 1 []
-- >>> let (nb2, _) = w_n 2 nb1
-- >>> nb2
-- [1,2]
-- >>> let (nb3, _) = w_n 3 nb2
-- >>> nb3
-- [2,3]
-- >>> r_n nb3
-- ([3],Just 2)
endsPure :: Queue a -> (a -> [a] -> ([a], Bool), [a] -> ([a], Maybe a))
endsPure = \case
  Unbounded ->
    ( \x buf -> (buf ++ [x], True),
      \case [] -> ([], Nothing); x : xs -> (xs, Just x)
    )
  Bounded n ->
    ( \x buf -> if length buf < n then (buf ++ [x], True) else (buf, False),
      \case [] -> ([], Nothing); x : xs -> (xs, Just x)
    )
  -- Single: MVar-style (A).  Write succeeds only when empty;
  -- overwrite-on-full (B) lives in SwapQ.
  Single ->
    ( \x buf -> case buf of [] -> ([x], True); _ -> (buf, False),
      \case [] -> ([], Nothing); x : _ -> ([], Just x)
    )
  -- SwapQ: B semantics — write always succeeds (overwrites); read empties.
  SwapQ ->
    ( \x _ -> ([x], True),
      \case [] -> ([], Nothing); x : _ -> ([], Just x)
    )
  Latest d ->
    ( \x _ -> ([x], True),
      \buf -> (buf, Just (case buf of x : _ -> x; [] -> d))
    )
  Newest n ->
    ( \x buf ->
        let buf' = buf ++ [x]
         in if length buf' <= n then (buf', True) else (drop 1 buf', True),
      \case [] -> ([], Nothing); x : xs -> (xs, Just x)
    )

-- ---------------------------------------------------------------------------
-- State-threading lifters
-- ---------------------------------------------------------------------------

-- | Push to state, returning 'Bool'.
-- 'False' signals rejection (e.g. bounded queue full).
--
-- Bare FIFO via 'endsPure' (note: 'flip' to match state-first order):
--
-- >>> let qpush = push (flip (fst (endsPure Unbounded)))
-- >>> run (qpush :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([], 1)
-- ([1],True)
push :: (s -> a -> (s, Bool)) -> Trace t (->) (s, a) (s, Bool)
push f = Arr (uncurry f)

-- | Pop from state, returning 'Maybe' a.
-- 'Nothing' signals empty.
--
-- Bare FIFO via 'endsPure':
--
-- >>> let qpop = pop (snd (endsPure Unbounded))
-- >>> run (qpop :: Trace (,) (->) ([Int], ()) ([Int], Maybe Int)) ([1,2,3], ())
-- ([2,3],Just 1)
-- >>> run (qpop :: Trace (,) (->) ([Int], ()) ([Int], Maybe Int)) ([], ())
-- ([],Nothing)
pop :: (s -> (s, Maybe a)) -> Trace t (->) (s, ()) (s, Maybe a)
pop f = Arr (\(s, ()) -> f s)

-- | Drain all available values from the state, returning them in order.
--
-- Unlike 'pop', which removes one value, 'drain' empties the buffer in a
-- single step. Use with the batch reader from 'endsPureBatch' or a custom
-- log cursor.
--
-- >>> let qdrain = drain (\buf -> ([], buf))
-- >>> run (qdrain :: Trace (,) (->) ([Int], ()) ([Int], [Int])) ([1,2,3], ())
-- ([],[1,2,3])
drain :: (s -> (s, [a])) -> Trace t (->) (s, ()) (s, [a])
drain f = Arr (\(s, ()) -> f s)

-- | Read all available values from the state without emptying it.
--
-- >>> let qsnap = snapshot (\buf -> (buf, buf))
-- >>> run (qsnap :: Trace (,) (->) ([Int], ()) ([Int], [Int])) ([1,2,3], ())
-- ([1,2,3],[1,2,3])
snapshot :: (s -> (s, [a])) -> Trace t (->) (s, ()) (s, [a])
snapshot f = Arr (\(s, ()) -> f s)

-- ---------------------------------------------------------------------------
-- Box view — monoidal packaging of a free dual pair
-- ---------------------------------------------------------------------------

-- | Box as a monoidal view of a free dual pair.
--
-- The primary store is the 'Ends' record (the pair of free ends). 'boxOf'
-- packages the unit-plugged halves into one morphism @(a, ()) → ((), b)@
-- for wiring into larger monoidal diagrams. Keep the 'Ends' record if you
-- need independent async access; 'boxOf' is lossy as a view of the pair.
--
-- * Law 2 (splay): from 'boxOf ends' you cannot recover the independent free
--   halves.
-- * Law 3 (bifunctor / dimap): contramap on the commit side is
--   pre-composition with 'first'; postmap on the emit side is
--   post-composition with 'second'.
-- * Law 5 (queue instance): unit-plugged queue wires already have the box
--   shape, so their view is just 'par'.
--
-- >>> import Data.Bifunctor (first, second)
-- >>> ends <- atomically (openSTM Unbounded :: STM (Ends (,) (Kleisli STM) Int Int))
-- >>> let box = boxOf ends
-- >>> :t box
-- box :: Trace (,) (Kleisli STM) (Int, ()) ((), Int)
-- >>> let commit' = In (\o -> lmap (+10) (runOut (commit ends) o))
-- >>> let box' = boxOf (Ends commit' (emit ends))
-- >>> :t box'
-- box' :: Trace (,) (Kleisli STM) (Int, ()) ((), Int)
-- >>> (push, pop) <- atomically (endsQueue Unbounded :: STM (WireK IO Int (), WireK IO () Int))
-- >>> let queueBox = par push pop :: Trace (,) (Kleisli IO) (Int, ()) ((), Int)
-- >>> :t queueBox
-- queueBox :: Trace (,) (Kleisli IO) (Int, ()) ((), Int)
boxOf :: (MonadFix m) => Ends (,) (Kleisli m) a b -> Trace (,) (Kleisli m) (a, ()) ((), b)
boxOf ends = par (runOut (commit ends) outU) (runIn (emit ends) inU)
  where
    (outU, inU) = openK ()

-- ---------------------------------------------------------------------------
-- Box Maybe/Bool signalling translated up into Trace
-- ---------------------------------------------------------------------------

-- | Old @box@ used doors that signalled on every step:
--
-- @
--   emit   :: m (Maybe a)   -- Nothing = closed / empty
--   commit :: a -> m Bool   -- False   = reject / stop
-- @
--
-- In Trace the channel doors are total; the same behaviour is recovered
-- by carrying Bool/Maybe as payload values, and by treating close/stop as
-- a separate lifecycle. A 'Single' queue strategy already gives the right
-- state functions.
--
-- >>> let (w, r) = endsPure (Single :: Queue Int)
-- >>> run (push (flip w) :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([], 1)
-- ([1],True)
-- >>> run (push (flip w) :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([1], 2)
-- ([1],False)
-- >>> run (pop r :: Trace (,) (->) ([Int], ()) ([Int], Maybe Int)) ([1], ())
-- ([],Just 1)
-- >>> run (pop r :: Trace (,) (->) ([Int], ()) ([Int], Maybe Int)) ([], ())
-- ([],Nothing)
--
-- The free ends still have the total box shape @(a, ()) -> ((), b)@;
-- signalling never appears in the channel type:
--
-- >>> let (outA, inA) = open (1 :: Int) :: (Out (->) (,) Int, In (->) (,) Int)
-- >>> let (outU, inU) = open () :: (Out (->) (,) (), In (->) (,) ())
-- >>> let commit = In (\o -> lmap (const ()) (runOut inU o)) :: In (->) (,) Int
-- >>> :t par (runOut commit outU) (runIn outA inU) :: Trace (,) (->) (Int, ()) ((), Int)
-- par (runOut commit outU) (runIn outA inU) :: Trace (,) (->) (Int, ()) ((), Int)
--   :: Trace (,) (->) (Int, ()) ((), Int)
--
-- Closure or stop is 'close', 'replClose', or a runner turn — not a value
-- returned on every emit/commit.

-- ---------------------------------------------------------------------------
-- Type ladder examples (Trace (t a c) (t d b) claims)
-- ---------------------------------------------------------------------------

-- | E1 — Unit specialisation is real. 'boxOf' packages the free pair into
-- the boring box shape @(a, ()) -> ((), b)@; the free pair remains available
-- beside the view.
--
-- >>> ends <- atomically (openSTM Unbounded :: STM (Ends (,) (Kleisli STM) Int Int))
-- >>> :t boxOf ends
-- boxOf ends :: Trace (,) (Kleisli STM) (Int, ()) ((), Int)
-- >>> :t (commit ends, emit ends)
-- (commit ends, emit ends)
--   :: (In (Kleisli STM) (,) Int, Out (Kleisli STM) (,) Int)

-- | E2 — Free 'par' has open @c@ / @d@ legs. It does not force unit.
--
-- >>> let both = par ((+1) :: Int -> Int) ((*2) :: Int -> Int)
-- >>> both (3, 4) :: (Int, Int)
-- (4,8)
--
-- The same combinator specialises to the unit-grounded box shape when the
-- legs are plugged at '()':
--
-- >>> let left = const () :: Int -> ()
-- >>> let right = const (7 :: Int) :: () -> Int
-- >>> let box = Arr (par left right) :: Trace (,) (->) (Int, ()) ((), Int)
-- >>> :t box
-- box :: Trace (,) (->) (Int, ()) ((), Int)

-- | E3 — 'Bool' as commit-ack status payload, not a door type. The channel
-- stays total; rejection is observed as a returned 'Bool'.
--
-- >>> let (w, _r) = endsPure (Single :: Queue Int)
-- >>> run (push (flip w) :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([], 1)
-- ([1],True)
-- >>> run (push (flip w) :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([1], 2)
-- ([1],False)

-- | E4 — 'Maybe' as emit partiality payload, not an 'Emitter' door. Empty is
-- 'Nothing'; a value is 'Just'. (See the Maybe/Bool block above for the full
-- Single-queue narrative.)
--
-- >>> let (_w, r) = endsPure (Single :: Queue Int)
-- >>> run (pop r :: Trace (,) (->) ([Int], ()) ([Int], Maybe Int)) ([7], ())
-- ([],Just 7)
-- >>> run (pop r :: Trace (,) (->) ([Int], ()) ([Int], Maybe Int)) ([], ())
-- ([],Nothing)

-- | E5 — Stop on empty or reject is a runner decision, not a channel door.
-- The runner observes the 'Bool'/'Maybe' payloads and decides whether to
-- continue; the free halves remain total.
--
-- >>> let (w, r) = endsPure (Single :: Queue Int)
-- >>> run (pop r :: Trace (,) (->) ([Int], ()) ([Int], Maybe Int)) ([9], ())
-- ([],Just 9)
-- >>> run (push (flip w) :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([], 9)
-- ([9],True)
-- >>> run (push (flip w) :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([9], 5)
-- ([9],False)

-- | E6 — Withering is pre/post composition on payload legs, not a second
-- theory. Emit-side wither filters the harvested list; commit-side wither
-- is the dual 'lmap'/'first' construction.
--
-- >>> let (w, r) = endsPure (Unbounded :: Queue Int)
-- >>> run (push (flip w) :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([], 1)
-- ([1],True)
-- >>> run (push (flip w) :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([1], 2)
-- ([1,2],True)
-- >>> run (push (flip w) :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([1,2], 3)
-- ([1,2,3],True)
-- >>> run (rmap (\(s, xs) -> (s, filter even xs)) (drain (\buf -> ([], buf))) :: Trace (,) (->) ([Int], ()) ([Int], [Int])) ([1,2,3], ())
-- ([],[2])

-- | E7 — @c@ can carry control without being unit. A demand 'Bool' on the
-- left leg decides whether to emit on the right leg.
--
-- >>> let demandEmit = Arr (\((), demand) -> ((), if demand then Just (1 :: Int) else Nothing))
-- >>> :t demandEmit
-- demandEmit :: Trace t (->) ((), Bool) ((), Maybe Int)
-- >>> run (demandEmit :: Trace (,) (->) ((), Bool) ((), Maybe Int)) ((), True)
-- ((),Just 1)
-- >>> run (demandEmit :: Trace (,) (->) ((), Bool) ((), Maybe Int)) ((), False)
-- ((),Nothing)

-- ---------------------------------------------------------------------------
-- STM queue ends
-- ---------------------------------------------------------------------------

-- | Create a dual pair: push end and pop end sharing a single STM channel.
--
-- Each operation is wrapped in its own 'atomically'.  You cannot batch
-- multiple writes or a write-plus-read into a single STM transaction.
--
-- For atomic composition use 'endsSTM' directly:
--
-- >>> (w, r) <- atomically (endsSTM Unbounded :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 1 >> w 2 >> r  -- both writes + read in ONE transaction
-- 1
--
-- 'endsQueue' bakes 'atomically' into each circuit step.  The same work
-- would require three separate 'atomically' calls — visible to concurrent
-- writers.  When you need multi-op atomicity, reach for 'endsSTM' and wrap
-- in 'atomically' yourself.
--
-- Use 'WireK' to pin the tensor for readability:
--
-- >>> (pushA, popA) <- atomically (endsQueue Unbounded :: STM (WireK IO Int (), WireK IO () Int))
-- >>> (pushB, popB) <- atomically (endsQueue Unbounded :: STM (WireK IO Int (), WireK IO () Int))
-- >>> let pipe = Arr (Kleisli $ \() -> pure (7 :: Int)) >>> pushA >>> popA >>> pushB >>> popB
-- >>> runKleisli (run pipe) ()
-- 7
endsQueue :: Queue a -> STM (Trace t (Kleisli IO) a (), Trace t (Kleisli IO) () a)
endsQueue q = do
  (write, read') <- endsSTM q
  pure (Arr (Kleisli (atomically . write)), Arr (Kleisli (\() -> atomically read')))

-- | Plug a push end and a pop end together into a single circuit.
--
-- This is the extrinsic analogue of 'Circuit.Ends.close': two ends
-- that share an STM channel are composed into @Circuit a a@.
--
-- >>> (pushA, popA) <- atomically (endsQueue Unbounded :: STM (WireK IO Int (), WireK IO () Int))
-- >>> runKleisli (run (closeQueue pushA popA)) 42
-- 42
closeQueue ::
  (Traced t (Kleisli IO)) =>
  Trace t (Kleisli IO) a () ->
  Trace t (Kleisli IO) () a ->
  Trace t (Kleisli IO) a a
closeQueue push' pop' = push' >>> pop'

-- ---------------------------------------------------------------------------
-- Ends product — the dual free ends as a named record
-- ---------------------------------------------------------------------------

-- | The product of free channel ends: 'commit' writes, 'emit' reads.
--
-- Named after the collective noun for the commit / emit pair.
-- The type parameters let @a@ and @b@ differ; for queues they are the same.
data Ends t arr a b = Ends
  { commit :: In arr t a  -- ^ Write end (producer).
  , emit   :: Out arr t b  -- ^ Read end  (consumer).
  }

-- | Open a queue strategy as STM 'Ends'.
--
-- Allocates STM primitives and returns the dual ends sharing the same
-- mutable channel.  Both ends live in 'STM', so you can compose
-- operations across channels in a single 'atomically' block.
--
-- @
-- ends <- atomically (openSTM Unbounded)
-- atomically $ do
--   msg <- runKleisli (run (runIn (emit ends) inU)) ()
--   runKleisli (run (runOut (commit ends) outU)) msg
-- @
--
-- === Unbounded
--
-- >>> import Circuit.Ends (openK)
-- >>> let (outU, inU) = openK ()
-- >>> ends <- atomically (openSTM Unbounded :: STM (Ends (,) (Kleisli STM) Int Int))
-- >>> atomically $ runKleisli (run (runOut (commit ends) outU)) 42
-- >>> atomically $ runKleisli (run (runIn (emit ends) inU)) ()
-- 42
--
-- Multi-op compose in one 'atomically' (both writes + read):
--
-- >>> ends <- atomically (openSTM Unbounded :: STM (Ends (,) (Kleisli STM) Int Int))
-- >>> atomically $ runKleisli (run (runOut (commit ends) outU)) 1 >> runKleisli (run (runOut (commit ends) outU)) 2 >> runKleisli (run (runIn (emit ends) inU)) ()
-- 1
--
-- 'close' recovers the value through the queue:
--
-- >>> ends <- atomically (openSTM Unbounded :: STM (Ends (,) (Kleisli STM) Int Int))
-- >>> atomically $ runKleisli (run (close (commit ends) (emit ends))) 7
-- 7
--
-- === SwapQ (overwrite on write)
--
-- >>> ends <- atomically (openSTM SwapQ :: STM (Ends (,) (Kleisli STM) Int Int))
-- >>> atomically $ runKleisli (run (runOut (commit ends) outU)) 1 >> runKleisli (run (runOut (commit ends) outU)) 2 >> runKleisli (run (runIn (emit ends) inU)) ()
-- 2
openSTM :: Queue a -> STM (Ends (,) (Kleisli STM) a a)
openSTM = \case
  Unbounded -> do
    q <- newTQueue
    let outA = Out $ \_ -> Arr (Kleisli $ \_ -> readTQueue q)
        inA = In $ \o -> Arr (Kleisli $ \a -> writeTQueue q a >> runKleisli (run (runIn o inA)) a)
    pure (Ends inA outA)
  Bounded n -> do
    q <- newTBQueue (fromIntegral n)
    let outA = Out $ \_ -> Arr (Kleisli $ \_ -> readTBQueue q)
        inA = In $ \o -> Arr (Kleisli $ \a -> writeTBQueue q a >> runKleisli (run (runIn o inA)) a)
    pure (Ends inA outA)
  Single -> do
    v <- newEmptyTMVar
    let outA = Out $ \_ -> Arr (Kleisli $ \_ -> takeTMVar v)
        inA = In $ \o -> Arr (Kleisli $ \a -> putTMVar v a >> runKleisli (run (runIn o inA)) a)
    pure (Ends inA outA)
  SwapQ -> do
    v <- newEmptyTMVar
    let write x = tryPutTMVar v x >>= \case True -> pure (); False -> void (swapTMVar v x)
        outA = Out $ \_ -> Arr (Kleisli $ \_ -> takeTMVar v)
        inA = In $ \o -> Arr (Kleisli $ \a -> write a >> runKleisli (run (runIn o inA)) a)
    pure (Ends inA outA)
  Latest a -> do
    t <- newTVar a
    let outA = Out $ \_ -> Arr (Kleisli $ \_ -> readTVar t)
        inA = In $ \o -> Arr (Kleisli $ \x -> writeTVar t x >> runKleisli (run (runIn o inA)) x)
    pure (Ends inA outA)
  Newest n -> do
    q <- newTBQueue (fromIntegral n)
    let write x = writeTBQueue q x <|> (tryReadTBQueue q *> write x)
        outA = Out $ \_ -> Arr (Kleisli $ \_ -> readTBQueue q)
        inA = In $ \o -> Arr (Kleisli $ \a -> write a >> runKleisli (run (runIn o inA)) a)
    pure (Ends inA outA)
