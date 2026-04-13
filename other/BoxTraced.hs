{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module BoxTraced where

import Prelude hiding (id, (.))
import Control.Category (Category (..))
import Control.Concurrent (forkIO)
import Control.Concurrent.MVar
import Control.Concurrent.STM
import Control.Monad (forM_, void)
import Traced (TracedA (..), Trace (..), run)
import Hyp    (Hyp, toHyp, rep, (⊙))

-- ---------------------------------------------------------------------------
-- § 1. Wire and Process
--
-- Wire a = Either a ()
--
-- The key identifications:
--   STM TQueue        = the Knot channel s
--   spawnQueue        = Knot introduction: materialise s in IO
--   glueP             = run: close the Knot, drain the channel
--   composeBox        = intCompose: trace out the shared channel
--   Codensity bracket = prompt boundary: manage channel lifetime
-- ---------------------------------------------------------------------------

type Wire a = Either a ()

-- | Pure process: TracedA morphism between wires.
--   run :: ProcessE a b -> Wire a -> Wire b
type ProcessE a b = TracedA (->) Either (Wire a) (Wire b)
type ProcessP a b = TracedA (->) (,)    (Wire a) (Wire b)

-- Basic processes

liftP :: (a -> b) -> ProcessE a b
liftP f = Lift (either (Left . f) Right)

filterP :: (a -> Bool) -> ProcessE a a
filterP p = Lift $ either (\a -> if p a then Left a else Right ()) Right

-- State via (,) Knot: channel and payload arrive simultaneously.
-- Either Knot separates them across loop steps — can't thread state that way.
-- (,) Knot ties them lazily — state and value are always co-present.
withStateP :: (s -> a -> (s, b)) -> ProcessP (s, a) (s, b)
withStateP f = Knot step
  where
    step (s, Left (_, a)) = let (s', b) = f s a in (s', Left (s', b))
    step (s, Right ())    = (s, Right ())

-- ---------------------------------------------------------------------------
-- § 2. The queue IS the Knot channel
--
-- When we interpret ProcessE in IO, the Knot channel s becomes a TQueue.
-- spawnQueue materialises s. glueIO runs the while-loop.
-- ---------------------------------------------------------------------------

data Ends a = Ends
  { readEnd  :: IO (Wire a)   -- pull: Emitter
  , writeEnd :: a -> IO Bool  -- push: Committer
  , sealEnd  :: IO ()         -- close: terminate
  }

spawnQueue :: IO (Ends a)
spawnQueue = do
  q      <- newTQueueIO
  sealed <- newTVarIO False
  pure $ Ends
    { readEnd  = atomically $
                   (Left <$> readTQueue q)
                   `orElse` (readTVar sealed >>= \b ->
                        if b then pure (Right ()) else retry)
    , writeEnd = \a -> atomically $ do
                   b <- readTVar sealed
                   if b then pure False
                        else writeTQueue q a >> pure True
    , sealEnd  = atomically $ writeTVar sealed True
    }

-- | Run a ProcessE in IO: interpret then loop.
--   This is the original glue, generalised.
glueIO :: ProcessE a b -> IO (Wire a) -> (b -> IO Bool) -> IO ()
glueIO p pull push = loop
  where
    step = run p
    loop = pull >>= \wa -> case step wa of
      Right ()  -> pure ()
      Left b    -> push b >>= \ok -> if ok then loop else pure ()

-- | glue = glueIO on the identity process
glueQ :: IO (Wire a) -> (a -> IO Bool) -> IO ()
glueQ = glueIO (Lift id)

-- ---------------------------------------------------------------------------
-- § 3. Box and composition
--
-- Box a b = live channel: committer end takes a, emitter end gives b.
-- The queue inside IS the Knot. The Box exposes both ends.
-- ---------------------------------------------------------------------------

data Box a b = Box
  { emit   :: IO (Wire b)   -- positive wire out
  , commit :: a -> IO Bool  -- negative wire in
  }

spawnBox :: IO (Box a a, IO ())
spawnBox = do
  ends <- spawnQueue
  pure (Box (readEnd ends) (writeEnd ends), sealEnd ends)

-- | composeBox = intCompose
--   Trace out the shared a-wire between f and g.
--   f's emitter feeds into a queue; g's committer reads from it.
--   Runs the connection concurrently.
--   Returns Box with f's committer and g's emitter.
composeBox :: Box c a -> Box a b -> IO (Box c b)
composeBox f g = do
  ends <- spawnQueue
  done <- newEmptyMVar
  void $ forkIO $ do
    glueQ (emit f) (writeEnd ends)
    sealEnd ends
  void $ forkIO $ do
    glueQ (readEnd ends) (commit g)
    putMVar done ()
  takeMVar done
  pure (Box (emit g) (commit f))

-- ---------------------------------------------------------------------------
-- § 4. toHyp: the final encoding
--
-- Both ProcessE and ProcessP map to Hyp (Wire a) (Wire b).
-- The tensor disappears. Knot dissolves into ι.
--
-- toHyp in Hyp.hs is defined for TracedA (->) (,) — the (,) tensor.
-- For ProcessE (Either tensor) we use run to interpret first, then rep.
-- For ProcessP ((,) tensor) toHyp works directly.
--
-- The deeper point: Hyp is the final object for any traced category.
-- The route through (,) is the canonical one (Hyp.hs uses it directly).
-- The route through Either goes via run :: ProcessE a b -> Wire a -> Wire b,
-- then lifts into Hyp as rep (run p) — the unique observed morphism.
-- ---------------------------------------------------------------------------

-- | ProcessP → Hyp directly (same tensor as Hyp.hs uses)
processPtoHyp :: ProcessP a b -> Hyp (Wire a) (Wire b)
processPtoHyp = toHyp

-- | ProcessE → Hyp via run: interpret the Either trace, then embed.
--   rep (run p) = the constant hyperfunction that always applies run p.
--   This loses the Knot structure (feedback flattened) but gives a valid Hyp.
processEtoHyp :: ProcessE a b -> Hyp (Wire a) (Wire b)
processEtoHyp p = rep (run p)

-- | Compose two ProcessE via Hyp
composeViaHyp :: ProcessE a b -> ProcessE b c -> Hyp (Wire a) (Wire c)
composeViaHyp f g = processEtoHyp g ⊙ processEtoHyp f

-- ---------------------------------------------------------------------------
-- § 5. Smoke tests
-- ---------------------------------------------------------------------------

-- | Push a list into a Box and collect results
test_queue :: IO [Int]
test_queue = do
  (box, seal) <- spawnBox
  result <- newEmptyMVar
  void $ forkIO $ do
    xs <- drain (emit box)
    putMVar result xs
  forM_ [1..5 :: Int] $ \i -> commit box i
  seal
  takeMVar result
  where
    drain pull = go []
      where go acc = pull >>= \case
              Right ()  -> pure (reverse acc)
              Left a    -> go (a : acc)

-- | liftP: map over the wire
test_liftP :: Wire Int
test_liftP = run (liftP (*2)) (Left 21)
-- Expected: Left 42

-- | filterP: terminate on mismatch
test_filterP :: Wire Int
test_filterP = run (filterP even) (Left 3)
-- Expected: Right ()

-- | filterP passes evens
test_filterP2 :: Wire Int
test_filterP2 = run (filterP even) (Left 4)
-- Expected: Left 4

-- | Compose two processes
test_compose :: Wire Int
test_compose = run (liftP (+1) . liftP (*2)) (Left 5)
-- (*2) then (+1): Left 11

-- | The (,) Knot ties state lazily: s = fst (f s a).
-- For strict s (arithmetic) this diverges — s = s+1 has no fixed point.
-- This reveals the operational difference:
--   (,) Knot = productive only when s is not strictly forced
--   Either Knot = strict state via while-loop, no self-reference
-- 
-- A productive (,) Knot example: s is a lazy list (not forced at each step)
test_stateP :: Wire (Int, Int)
test_stateP = run (Knot step) (Left (0, 5))
  where
    -- Channel s :: Int is NOT fed back into the computation of b,
    -- only into the next channel step. The output b = a*2 ignores s.
    -- s = 0 always (not forced in the step output channel slot).
    step :: (Int, Wire (Int, Int)) -> (Int, Wire (Int, Int))
    step (_, Left (s, a)) = (s, Left (s, a * 2))  -- s not modified, no loop
    step (s, Right ())    = (s, Right ())

main :: IO ()
main = do
  putStrLn $ "liftP (*2) (Left 21) = "   ++ show test_liftP
  putStrLn $ "filterP even (Left 3) = "  ++ show test_filterP
  putStrLn $ "filterP even (Left 4) = "  ++ show test_filterP2
  putStrLn $ "compose (Left 5) = "        ++ show test_compose
  putStrLn $ "(,) Knot (Left (0,5)) = "  ++ show test_stateP
  xs <- test_queue
  putStrLn $ "queue [1..5] = "            ++ show xs
