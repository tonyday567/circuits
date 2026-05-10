{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PostfixOperators #-}

-- | Compact closed structure on 'Hyper'.
--
-- 'Hyper' is a profunctor: @Hyper a b@ is contravariant in @a@,
-- covariant in @b@. Profunctors form a compact closed category —
-- every object has a dual. This module names the dual pairs and
-- provides the unit/counit morphisms.
--
-- @
--   Producer m a = (m → a) ↬ a     — dual of Consumer
--   Consumer m a = a ↬ (m → a)     — dual of Producer
--   Channel r i o = (o → r) ↬ (i → r) — bidirectional pipe
-- @
--
-- = Unit and counit
--
-- @
--   unit :: a → (Producer m a, Consumer m a)
--   glue :: Consumer m a → Producer m a → a
-- @
--
-- 'unit' creates a matched producer/consumer pair from a value.
-- The value @a@ is the shared accumulator — both sides carry it
-- and return it when the connection closes.
--
-- 'glue' annihilates the pair: connect them and run in lockstep
-- until both terminate. The result is the accumulator @a@.
--
-- = Message-level adjunction
--
-- @
--   prod :: o → Producer o a → Producer o a
--   cons :: (i → a → a) → Consumer i a → Consumer i a
-- @
--
-- 'prod' sends a message; 'cons' receives and processes one.
-- These build the linked chain of Hypers that communicate stepwise.
--
-- The concrete encoding follows Kidney & Wu,
-- \"Hyperfunctions: Communicating Continuations\" (POPL 2026).
-- See @examples/channel.md@ and @examples/spec-hyper.hs@ for
-- pipeline construction and the coinductive Consumer pattern.
module Circuit.Channel
  ( -- * Types
    Producer,
    Consumer,
    Channel,

    -- * Construction
    prod,
    cons,
    yield,
    accept,

    -- * Compact closed
    unit,
    glue,
  )
where

import Circuit.Hyper (Hyper (..), invoke)

-- $setup
-- >>> import Circuit.Hyper (run)

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | A Producer sends messages of type @m@, yielding a result @a@.
--   The continuation @m → a@ maps what the consumer sends back to the result.
type Producer m a = Hyper (m -> a) a

-- | A Consumer receives messages of type @m@, yielding a result @a@.
--   The continuation @m → a@ is provided by the producer.
type Consumer m a = Hyper a (m -> a)

-- | A Channel consumes @i@ and produces @o@, with result @r@.
--   Bidirectional: can both send (via @o → r@) and receive (via @i → r@).
type Channel r i o = Hyper (o -> r) (i -> r)

-- ---------------------------------------------------------------------------
-- Construction
-- ---------------------------------------------------------------------------

-- | Send a message of type @o@ and continue with the rest of the producer.
--
-- >>> glue (cons (\x _ -> x) (accept 0)) (prod 42 (yield 0))
-- 42
prod :: o -> Producer o a -> Producer o a
prod o p = Hyper $ \q -> invoke q p o

-- | Receive a message of type @i@, process it with @f@, and continue.
--
-- The step function @f :: i -> a -> a@ receives the message and the
-- accumulator, returning the new accumulator.
--
-- >>> glue (cons (\x acc -> x + acc) (accept 0)) (yield 0)
-- 0
cons :: (i -> a -> a) -> Consumer i a -> Consumer i a
cons f p = Hyper $ \q i -> f i (invoke q p)

-- | A producer that emits a single value (the accumulator) and stops.
--
-- >>> glue (accept 42) (yield 42)
-- 42
yield :: a -> Producer o a
yield a = Hyper $ const a

-- | A consumer that ignores all messages and returns the accumulator.
--
-- >>> glue (accept 42) (yield 42)
-- 42
accept :: a -> Consumer i a
accept a = Hyper $ \_ _ -> a

-- ---------------------------------------------------------------------------
-- Compact closed
-- ---------------------------------------------------------------------------

-- | Create a matched producer/consumer pair from a value.
--   Both carry the same accumulator @a@. The producer emits it;
--   the consumer accepts it.
--
-- >>> let (p, c) = unit 42 :: (Producer Int Int, Consumer Int Int)
-- >>> glue c p
-- 42
unit :: a -> (Producer m a, Consumer m a)
unit a = (Hyper (const a), Hyper (\_ _ -> a))

-- | Connect a consumer and producer — run them in lockstep until
--   both terminate. The dual pair annihilates, leaving the accumulator.
--
--   The counit of the compact closed structure on 'Hyper'.
--
-- >>> glue (accept "done") (yield "done")
-- "done"
glue :: Consumer m a -> Producer m a -> a
glue c p = invoke p c
