-- | Hand-drawn batch collector: write lists, read single elements.
--
-- Unlike the strategy-based queues in "Circuit.Queue", this is a direct
-- STM implementation of a list-backed buffer.  The write end consumes a
-- whole @[a]@ at once; the read end pops one element at a time.
--
-- The buffer is supplied by the caller as a 'TVar' [a]; the constructors
-- are pure morphisms on that buffer.
module Circuit.Queue.Batch
  ( -- * Batch queues
    openBatchWith,
    openBatchSTM,
    openBatchMaybeSTM,

    -- * Raw list-buffer primitives
    pushAll,
    pop,
    popMaybe,
  )
where

import Circuit.Classes ((>>>))
import Circuit.Ends (Ends (..), HasUnit (..), In (..), Out (..), commit, companion, conjoint, emit)
import Control.Arrow (Kleisli (..))
import Control.Concurrent.STM
import Prelude

-- $setup
-- >>> import Circuit.Ends (Ends(..), In(..), Out(..), HasUnit(..))
-- >>> import Circuit.Queue.Batch
-- >>> import Control.Arrow (Kleisli(..), runKleisli)
-- >>> import Control.Concurrent.STM (STM, TVar, atomically, newTVar)

-- | Append a whole list to the back of a list-buffer.
pushAll :: TVar [a] -> [a] -> STM ()
pushAll buf as = modifyTVar' buf (++ as)

-- | Pop one element from the front of a list-buffer, returning 'Nothing'
-- when empty.
popMaybe :: TVar [a] -> STM (Maybe a)
popMaybe buf =
  readTVar buf >>= \case
    [] -> pure Nothing
    (a : as') -> writeTVar buf as' >> pure (Just a)

-- | Pop one element from the front of a list-buffer, retrying when empty.
pop :: TVar [a] -> STM a
pop buf =
  popMaybe buf >>= \case
    Nothing -> retry
    Just a -> pure a

-- | Build a batch-queue 'Ends' from an existing 'TVar' [a] buffer and a
-- single-element read action.
--
-- The caller allocates the 'TVar'; this function is pure in the buffer.
openBatchWith :: TVar [a] -> (TVar [a] -> STM b) -> Ends (Kleisli STM) [a] b
openBatchWith buf readOne =
  Ends
    (In $ \o -> Kleisli $ \as -> pushAll buf as >> runKleisli (emit o (conjoint open)) ())
    (Out $ \i -> Kleisli $ \x -> readOne buf >>= \b -> runKleisli (commit i (companion (open :: Ends (Kleisli STM) () ()))) x >> pure b)

-- | Open a batch queue with blocking single-element reads.
--
-- 'commit' appends a whole list to the buffer; 'emit' pops the head,
-- retrying when the buffer is empty.
--
-- >>> buf <- atomically (newTVar [] :: STM (TVar [Int]))
-- >>> let ends = openBatchSTM buf
-- >>> let endsU = open :: Ends (Kleisli STM) () ()
-- >>> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) [1,2,3]
-- >>> atomically $ runKleisli (emit (companion ends) (conjoint endsU)) ()
-- 1
-- >>> atomically $ runKleisli (emit (companion ends) (conjoint endsU)) ()
-- 2
openBatchSTM :: TVar [a] -> Ends (Kleisli STM) [a] a
openBatchSTM buf = openBatchWith buf pop

-- | Open a batch queue with non-blocking single-element reads.
--
-- 'commit' appends a whole list to the buffer; 'emit' pops the head and
-- returns 'Just' it, or 'Nothing' when the buffer is empty.
--
-- >>> let endsU = open :: Ends (Kleisli STM) () ()
-- >>> buf <- atomically (newTVar [] :: STM (TVar [Int]))
-- >>> let ends = openBatchMaybeSTM buf
-- >>> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) [1,2]
-- >>> atomically $ runKleisli (emit (companion ends) (conjoint endsU)) ()
-- Just 1
-- >>> atomically $ runKleisli (emit (companion ends) (conjoint endsU)) ()
-- Just 2
-- >>> atomically $ runKleisli (emit (companion ends) (conjoint endsU)) ()
-- Nothing
openBatchMaybeSTM :: TVar [a] -> Ends (Kleisli STM) [a] (Maybe a)
openBatchMaybeSTM buf = openBatchWith buf popMaybe
