{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Compact closed structure on 'Hyper'.
--
-- 'Hyper' is a profunctor: @Hyper a b@ is contravariant in @a@,
-- covariant in @b@. Profunctors form a compact closed category --
-- every object has a dual. This module names the dual pairs and
-- provides the unit/counit morphisms.
--
-- @
--   Producer m r a = (a → m r) ↬ (m r)   — dual of Consumer
--   Consumer m r a = (m r) ↬ (a → m r)   — dual of Producer
--   Channel m r i o = (o → m r) ↬ (i → m r) — bidirectional pipe
-- @
--
-- = Naming convention
--
-- @m@ — ambient monad (Identity for pure, IO for effects)
-- @r@ — carrier / result type
-- @a@ — element being communicated
-- @i@ — input element (Channel)
-- @o@ — output element (Channel)
--
-- = Unit and counit
--
-- @
--   unit :: Applicative m => r → (Producer m r a, Consumer m r a)
--   glue :: Producer m r a → Consumer m r a → m r
-- @
--
-- 'unit' creates a matched producer/consumer pair from a value.
-- 'glue' annihilates the pair: connect them and run in lockstep
-- until both terminate.
--
-- = Message-level adjunction
--
-- @
--   prod :: a → Producer m r a → Producer m r a
--   cons :: (a → m r → m r) → Consumer m r a → Consumer m r a
-- @
--
-- 'prod' sends a message; 'cons' receives and processes one.
-- These build the linked chain of Hypers that communicate stepwise.
--
-- The concrete encoding follows Kidney & Wu,
-- \"Hyperfunctions: Communicating Continuations\" (POPL 2026).
-- See @examples/channel-basics.md@ for pipeline construction
-- and the coinductive Consumer pattern.
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

import Circuit.Hyper

-- $setup
-- >>> :set -XBlockArguments
-- >>> import Circuit.Hyper (run)
-- >>> import Data.Functor.Identity (Identity(..), runIdentity)

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | A Producer sends elements of type @a@, embedded in monad @m@,
--   yielding a result carrier @r@ (also in @m@).
--
--   @Producer m r a = (a → m r) ↬ (m r)@
type Producer m r a = Hyper (a -> m r) (m r)

-- | A Consumer receives elements of type @a@, in monad @m@,
--   yielding a result carrier @r@.
--
--   @Consumer m r a = (m r) ↬ (a → m r)@
type Consumer m r a = Hyper (m r) (a -> m r)

-- | A Channel consumes @i@ and produces @o@, with monad @m@ and
--   result carrier @r@. Bidirectional: can both send (via @o → m r@)
--   and receive (via @i → m r@).
--
--   @Channel m r i o = (o → m r) ↬ (i → m r)@
type Channel m r i o = Hyper (o -> m r) (i -> m r)

-- ---------------------------------------------------------------------------
-- Construction
-- ---------------------------------------------------------------------------

-- | Send an element @a@ and continue with the rest of the producer.
--
-- >>> import Data.Functor.Identity (Identity(..), runIdentity)
-- >>> runIdentity $ glue (cons (\x _ -> pure x) (accept (0 :: Int))) (prod 42 (yield 0 :: Producer Identity Int Int))
-- 42
prod :: a -> Producer m r a -> Producer m r a
prod x p = Hyper $ \q -> (q ⇸ p) x

-- | Receive an element, process it with step function @f@, continue.
--
-- The step @f :: a → m r → m r@ receives the element and the result
-- of the rest of the chain, returning the new result.
--
-- >>> runIdentity $ glue (cons (\x acc -> fmap (+ x) acc) (accept (0 :: Int))) (yield 0 :: Producer Identity Int Int)
-- 0
cons :: (a -> m r -> m r) -> Consumer m r a -> Consumer m r a
cons f c = Hyper $ \p x -> f x (p ⇸ c)

-- | A producer that emits nothing — just returns the carrier @r@
--   in the ambient monad.
--
-- >>> runIdentity $ glue (accept 42) (yield 42)
-- 42
yield :: Applicative m => r -> Producer m r a
yield r = Hyper $ \_ -> pure r

-- | A consumer that ignores all elements and returns the carrier @r@.
--
-- >>> runIdentity $ glue (accept 42) (yield 42)
-- 42
accept :: Applicative m => r -> Consumer m r a
accept r = Hyper $ \_ _ -> pure r

-- ---------------------------------------------------------------------------
-- Compact closed
-- ---------------------------------------------------------------------------

-- | Create a matched producer/consumer pair from a value.
--
-- >>> let (p, c) = unit 42 :: (Producer Identity Int a, Consumer Identity Int a)
-- >>> runIdentity $ glue c p
-- 42
unit :: Applicative m => r -> (Producer m r a, Consumer m r a)
unit r = (Hyper $ \_ -> pure r, Hyper $ \_ _ -> pure r)

-- | Connect a consumer and producer — run them in lockstep until
--   both terminate. The dual pair annihilates, leaving the carrier
--   @r@ in the ambient monad @m@.
--
--   The counit of the compact closed structure on 'Hyper'.
--
-- >>> runIdentity $ glue (accept "done") (yield "done")
-- "done"
glue :: Consumer m r a -> Producer m r a -> m r
glue c p = p ⇸ c
