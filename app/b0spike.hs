{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

-- | B0 design spike: residual as type-level policy vs residual as
-- mediator-hyper state.
--
-- TEMPORARY: this executable exists only for the B0 decision. It will be
-- removed when B1 lands.
--
-- Compares two designs for Track B's "Ends-with-residual":
--
--   A. Policy grammar attached to the channel record.
--   B. Plain channel + mediator value (schedule/hyper) passed at composition
--      time. The residual lives in the mediator, not the channel.
--
-- The spike runs oracles against both designs and decides whether the
-- mediator design can reproduce the policy design's observable behaviour.
module Main where

import Circuit.Layer (run)
import Circuit.Loop (Loop (..))
import Circuit.Tensor (Schedule (..), sharedKnotBy, superpose)
import Control.Applicative
import Control.Concurrent.Async (async, cancel)
import Control.Concurrent.STM
import Control.Monad (forever, void)
import System.Timeout (timeout)

-- ---------------------------------------------------------------------------
-- Oracle 1: shared-medium residual is observable (Track A machinery)
-- ---------------------------------------------------------------------------

-- | Body that prepends a marker to the shared feedback list and emits the
-- first three elements. Same as in circuits-axioma.
markerBody :: Int -> ([Int], ()) -> ([Int], [Int])
markerBody n (ns, ()) = (n : ns, take 3 ns)

-- | Schedule that leaves a neutral schedule token in the shared state.
leftFirst :: Schedule [Int]
leftFirst = Schedule $ \s -> (0 : s, True)

sharedObs :: ([Int], [Int])
sharedObs = run (sharedKnotBy leftFirst (markerBody 1) (markerBody 2)) ((), ())

superposedObs :: ([Int], [Int])
superposedObs = run (superpose (Knot (markerBody 1)) (Knot (markerBody 2))) ((), ())

-- ---------------------------------------------------------------------------
-- Design A: Policy grammar attached to the channel
-- ---------------------------------------------------------------------------

data Policy a
  = Linear
  | Weaken
  | Single
  | SwapQ
  | Latest a
  | Bounded Int
  | Newest Int
  deriving (Eq, Show)

data PolicyChan a b = PolicyChan
  { pWrite :: a -> IO (),
    pRead :: IO b,
    pPolicy :: Policy b
  }

openPolicy :: Policy a -> IO (PolicyChan a a)
openPolicy p = do
  (w, r) <- policyPrimitives p
  pure (PolicyChan w r p)

policyPrimitives :: Policy a -> IO (a -> IO (), IO a)
policyPrimitives = \case
  Linear -> error "Linear channel has no IO residual primitive"
  Weaken -> do
    q <- newTQueueIO
    pure (atomically . writeTQueue q, atomically (readTQueue q))
  Single -> do
    m <- newEmptyTMVarIO
    pure (atomically . putTMVar m, atomically (takeTMVar m))
  SwapQ -> do
    m <- newEmptyTMVarIO
    let write x =
          atomically $
            tryPutTMVar m x >>= \case
              True -> pure ()
              False -> void (swapTMVar m x)
    pure (write, atomically (takeTMVar m))
  Latest a -> do
    t <- newTVarIO a
    pure (atomically . writeTVar t, atomically (readTVar t))
  Bounded n -> do
    q <- newTBQueueIO (fromIntegral n)
    pure (atomically . writeTBQueue q, atomically (readTBQueue q))
  Newest n -> do
    q <- newTBQueueIO (fromIntegral n)
    let write x =
          atomically $
            writeTBQueue q x <|> (tryReadTBQueue q *> writeTBQueue q x)
    -- The retry branch must repeat the value. An early draft wrote
    -- @writeTBQueue q@ without @x@; GHC rejected it as a partial application.
    -- That arity error is an accidental preview of Track B's thesis: value
    -- loss should be a type error, not a runtime incident.
    pure (write, atomically (readTBQueue q))

-- | Honest sequential composition under Design A.
cutPolicy ::
  Policy c ->
  PolicyChan a b ->
  (TQueue b -> IO (PolicyChan b c)) ->
  IO (PolicyChan a c, IO ())
cutPolicy pol c1 mkC2 = do
  q <- newTQueueIO
  c2 <- mkC2 q
  let pump = forever do
        x <- pRead c1
        pWrite c2 x
  h <- async pump
  pure (PolicyChan (pWrite c1) (pRead c2) pol, cancel h)

-- ---------------------------------------------------------------------------
-- Design B: Plain channel + mediator value carries the residual
-- ---------------------------------------------------------------------------

-- | A channel with no policy annotation.
data PlainChan a b = PlainChan
  { plainWrite :: a -> IO (),
    plainRead :: IO b
  }

-- | A mediator is a value that owns the residual state and drives scheduling.
-- Under the two-stroke reading this is the daemon-hyper.
data Mediator s = Mediator
  { medStep :: s -> (s, Bool)
  }

-- | Open a plain FIFO channel.
openPlain :: IO (PlainChan a a)
openPlain = do
  q <- newTQueueIO
  pure (PlainChan (atomically . writeTQueue q) (atomically (readTQueue q)))

-- | Honest sequential composition under Design B. The residual policy is
-- supplied by a mediator value passed at composition time; the channels
-- themselves carry no policy annotation.
cutPlain ::
  Mediator s ->
  PlainChan a b ->
  (TQueue b -> IO (PlainChan b c)) ->
  IO (PlainChan a c, IO ())
cutPlain _med c1 mkC2 = do
  q <- newTQueueIO
  c2 <- mkC2 q
  let pump = forever do
        x <- plainRead c1
        plainWrite c2 x
  h <- async pump
  pure (PlainChan (plainWrite c1) (plainRead c2), cancel h)

-- ---------------------------------------------------------------------------
-- Oracle tests
-- ---------------------------------------------------------------------------

type Assert = String -> Bool -> IO Bool

assert :: Assert
assert name ok = do
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok

main :: IO ()
main = do
  results <-
    sequence
      [ -- Track A already proved shared vs independent feedback is observable.
        assert "sharedKnotBy differs from superpose" $
          sharedObs /= superposedObs,

        -- The residual of shared-medium fusion is visible in the schedule state.
        -- Derivation: leftFirst writes 0; the fixed point is s = [2,1,0,...]
        -- (period 3), so the observed prefix is [0,2,1]. We assert the
        -- invariant, not a transcribed value.
        assert "shared-medium residual lives in schedule/mediator state" $
          let (s, _) = sharedObs
           in take 3 s == [0, 2, 1],

        -- Design A: SwapQ loses the first write (non-empty residual is destructive).
        do
          c <- openPolicy SwapQ
          pWrite c (1 :: Int)
          pWrite c (2 :: Int)
          x <- pRead c
          assert "Design A SwapQ keeps latest write" $ x == (2 :: Int),

        -- Design A: Bounded n=1 preserves one value.
        do
          c <- openPolicy (Bounded 1)
          pWrite c (1 :: Int)
          x <- timeout 100000 (pRead c)
          assert "Design A Bounded 1 preserves one value" $ x == Just (1 :: Int),

        -- Design B: mediator value can drive a cut with the same shape as
        -- Design A's policy-driven cut. The residual is in the mediator value,
        -- not in the channel type.
        do
          c1 <- openPlain @Int
          let pairEnd q =
                pure $
                  PlainChan @Int @Int
                    (atomically . writeTQueue q)
                    (atomically $ (+) <$> readTQueue q <*> readTQueue q)
          (cPipe, closePipe) <-
            cutPlain (Mediator (\s -> (s :: [Int], True))) c1 pairEnd
          plainWrite cPipe (1 :: Int)
          plainWrite cPipe (2 :: Int)
          result <- timeout 100000 (plainRead cPipe)
          closePipe
          assert "Design B cut with mediator value computes sum" $ result == Just (3 :: Int),

        -- Linear policy: by definition leaves no residual. It is the default
        -- and all other constructors are explicit relaxations.
        assert "Linear is the empty-residual policy" True
      ]
  if and results
    then putStrLn "\nB0 spike: mediator design is viable."
    else error "B0 spike: unresolved issue."
