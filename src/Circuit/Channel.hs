{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

-- | Channel: bidirectional coroutines via hyperfunctions.
--
-- From Kidney & Wu, \"Hyperfunctions: Communicating Continuations\" (POPL 2026).
--
--   Producer o a = (o → a) ↬ a     — produces messages of type o, result a
--   Consumer i a = a ↬ (i → a)     — consumes messages of type i, result a
--   Channel r i o = (o → r) ↬ (i → r) — bidirectional pipe
--
-- Compact closed structure:
--   unit   :: a → (Producer m a, Consumer m a)
--   counit :: Consumer m a → Producer m a → a
--
-- Message-level adjunction:
--   prod :: o → Producer o a → Producer o a
--   cons :: (i → a → a) → Consumer i a → Consumer i a
--
-- Pure lockstep interpreter:
--   withQ :: Producer m a → Consumer m a → a

module Circuit.Channel
  ( -- * Types
    Producer,
    Consumer,
    Channel,

    -- * Compact closed
    unit,
    counit,
    withQ,

    -- * Constructors
    prod,
    cons,

    -- * Base cases
    doneP,
    doneC,
  )
where

import Circuit.Hyper (Hyper (..), invoke)

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | A Producer sends messages of type @o@, yielding a result @a@.
--   The continuation @o → a@ maps what the consumer sends back to the result.
type Producer o a = Hyper (o -> a) a

-- | A Consumer receives messages of type @i@, yielding a result @a@.
--   The continuation @i → a@ is provided by the producer.
type Consumer i a = Hyper a (i -> a)

-- | A Channel consumes @i@ and produces @o@, with result @r@.
--   Bidirectional: can both send (via @o → r@) and receive (via @i → r@).
type Channel r i o = Hyper (o -> r) (i -> r)

-- ---------------------------------------------------------------------------
-- Compact closed structure
-- ---------------------------------------------------------------------------

-- | Create a matched producer/consumer pair from a value.
--   The producer emits the value; the consumer accepts it.
unit :: a -> (Producer o a, Consumer i a)
unit a = (Hyper (\_ -> a), Hyper (\_ _ -> a))

-- | Annihilate a consumer and producer — run them together.
--   The counit of the compact closed structure.
counit :: Consumer m a -> Producer m a -> a
counit c p = invoke p c

-- | Run a producer and consumer in lockstep (turn-based, pure).
withQ :: Producer m a -> Consumer m a -> a
withQ = invoke

-- ---------------------------------------------------------------------------
-- Constructors
-- ---------------------------------------------------------------------------

-- | Send a message of type @o@ and continue with the rest of the producer.
--   𝜄 (prod o p) q = 𝜄 q p o
prod :: o -> Producer o a -> Producer o a
prod o p = Hyper $ \q -> invoke q p o

-- | Receive a message of type @i@, process it with @f@, and continue.
--   𝜄 (cons f p) q i = f i (𝜄 q p)
cons :: (i -> a -> a) -> Consumer i a -> Consumer i a
cons f p = Hyper $ \q i -> f i (invoke q p)

-- ---------------------------------------------------------------------------
-- Base cases
-- ---------------------------------------------------------------------------

-- | A producer that immediately returns the accumulator.
doneP :: a -> Producer o a
doneP a = Hyper $ \_ -> a

-- | A consumer that ignores all messages and returns the accumulator.
doneC :: a -> Consumer i a
doneC a = Hyper $ \_ _ -> a
