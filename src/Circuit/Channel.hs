{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PostfixOperators #-}

-- | Atomic communication primitives on 'Hyper'.
--
-- Kidney & Wu (POPL 2026) start with two atomic types:
--
-- @
--   Emit   a = () ↬ a   — produce a value
--   Commit a = a ↬ ()   — consume a value
-- @
--
-- These carry no internal state — they're pure value sources and sinks.
-- State is threaded externally via composition. 'lift' bridges to effects:
--
-- @
--   lift putStrLn        :: Hyper String (IO ())  — IO sink
--   lift (const readLn)  :: Hyper () (IO String)  — IO source
-- @
--
-- = Channel
--
-- 'Channel r i o' is the bidirectional pipe — consumes @i@,
-- produces @o@, with result @r@.
module Circuit.Channel
  ( -- * Atomic types
    Emit,
    Commit,

    -- * Channel
    Channel,

    -- * Construction
    emit,
    commit,
  )
where

import Circuit.Hyper

-- $setup
-- >>> :set -XBlockArguments

-- ---------------------------------------------------------------------------
-- Atomic types
-- ---------------------------------------------------------------------------

-- | An atomic value producer. @() ↬ a@ — produces @a@ when invoked.
--
-- >>> emit 42 ⇸ commit
-- 42
type Emit a = Hyper () a

-- | An atomic value consumer. @a ↬ ()@ — accepts @a@, returns ().
--
-- >>> emit 42 ⇸ commit
-- 42
type Commit a = Hyper a ()

-- ---------------------------------------------------------------------------
-- Channel
-- ---------------------------------------------------------------------------

-- | A bidirectional pipe: consumes @i@, produces @o@, result carrier @r@.
--
--   @Channel r i o = (o → r) ↬ (i → r)@
type Channel r i o = Hyper (o -> r) (i -> r)

-- ---------------------------------------------------------------------------
-- Construction
-- ---------------------------------------------------------------------------

-- | Wrap a value into an 'Emit'.
--
-- >>> emit 42 ⇸ commit
-- 42
emit :: a -> Emit a
emit a = Hyper $ \_ -> a

-- | A 'Commit' that ignores its input.
--
-- >>> emit 42 ⇸ commit
-- 42
commit :: Commit a
commit = Hyper $ \_ -> ()
