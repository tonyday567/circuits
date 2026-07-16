{-# LANGUAGE RankNTypes #-}

-- | 'Circuit.Ends' re-exports 'Out' and 'In' from 'Circuit.Trace'
-- and provides the units 'open' (pure) and 'openSTM' (runtime 'TVar'),
-- plus pure unit-grounding views used as proof spikes for
-- 'Circuit.Queue.Commit' / 'Circuit.Queue.Emit'.
--
-- = Background
--
-- In a proarrow equipment (Bartosz Milewski, 2026), every vertical arrow
-- @f@ has a /companion/ @B(f,1)@ and a /conjoint/ @B(1,f)@, which are
-- horizontal arrows (profunctors) going in opposite directions.  For the
-- identity functor @id@, these specialise to:
--
-- @
--   Companion(id)(x, a) = p(x, a)      -- 'Out'
--   Conjoint(id)(a, x)  = p(a, x)      -- 'In'
-- @
--
-- where @p@ is the hom-profunctor ('Circuit' @arr@ @t@).
--
-- The companion and conjoint form an adjunction @In ⊣ Out@.
-- The unit @η@ is 'open'; the counit @ε@ is 'close'.  The yanking identity
-- @close i o = runOut i o@ is the defining characteristic.
--
-- = Intrinsic vs extrinsic
--
-- When the channel is structural (pure 'Circuit's with 'Knot' feedback),
-- 'Out' and 'In' are genuinely different roles — the 'forall x'
-- forces mutual recursion.  This is the /intrinsic/ case.
--
-- When the channel is a runtime object (an 'IORef', 'TChan', socket), both
-- ends collapse to the same handle on the mutable cell.  That is the
-- /extrinsic/ case, served by 'Circuit.Queue.makeQueue'.
--
-- = close ≅ trace
--
-- Slogan: @close@ is the dual-end analogue of 'trace'. 'Knot' introduces
-- feedback and 'trace' resolves it; 'open' introduces a matched pair of
-- channel ends and 'close' resolves them. The matched pair lives on one
-- facet: both 'Out' and 'In' refer to the same hidden channel.
--
-- By the spider lemma of proarrow equipment, any 'Knot' factors as:
--
-- @
--   Knot body = open >>> body' >>> close
-- @
--
-- and conversely. 'Out'/'In' is not a replacement for 'Knot' —
-- it is a refinement that lets the two channel ends travel independently
-- before being plugged together with 'close'.
--
-- = Proof spikes (pure mocks)
--
-- Design gate: unit-ground 'Commit'/'Emit' /before/ treating them as free ends.
--
-- * Mock 0 — yank: @'close' i o@ recovers the seed of @'open'@ (below).
-- * Mock 1–2 — unit-ground: @'asCommit'@ / @'asEmit'@ are @'In'@/@'Out'@
--   plugged at the monoidal unit @()@. Same shapes as 'Circuit.Queue.Commit'
--   / 'Circuit.Queue.Emit' (@a → ()@ / @() → a@).
-- * Mock 3 — polarity: harness write = @'asCommit'@, harness read = @'asEmit'@;
--   re-seat who is \"the process\" and the app names flip — types do not.
module Circuit.Ends
  ( -- * Channel ends (re-exported from 'Circuit')
    Out (..),
    In (..),
    close,

    -- * Unit
    open,

    -- * Unit-grounded views (Commit / Emit shapes)
    asCommit,
    asEmit,

    -- * Runtime unit
    openSTM,
  )
where

import Circuit.Layer (run)
import Circuit.Trace (Out (..), In (..), Trace (..), close)
import Control.Arrow (Kleisli (..))
import Control.Concurrent.STM
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit (run)
-- >>> import Circuit.Ends

-- | @η@ — the unit of the companion/conjoint adjunction (pure case).
--
-- Create two channel ends from a seed value.  The seed becomes the
-- channel's initial state.  The companion always returns the seed;
-- the conjoint calls the companion back, which returns the seed —
-- the mutual recursion bottoms out because the companion returns first.
--
-- Mock 0 (yank): close recovers the seed, independent of the payload.
--
-- >>> let (outA, inA) = open (42 :: Int)
-- >>> run (close inA outA) 99
-- 42
open :: a -> (Out (->) (,) a, In (->) (,) a)
open seed = (outA, inA)
  where
    outA = Out $ \_ -> Arr (const seed)
    inA = In $ \o -> runIn o inA

-- | Unit-grounded /commit/ shape: @'In' a@ plugged against @'Out' ()@.
--
-- @
--   asCommit :: In arr t a -> Out arr t () -> Trace t arr a ()
-- @
--
-- Same port shape as 'Circuit.Queue.Commit' (@a → ()@): feed @a@, discard
-- into the monoidal unit.  Free ends stay @'In'@/@'Out'@; this is a
-- /view/, not a second primitive.
--
-- Mock 2 (unit-ground commit): pure constant channel discards the payload.
--
-- >>> let (outA, inA) = open (7 :: Int)
-- >>> let (outU, _inU) = open ()
-- >>> run (asCommit inA outU) 99
-- ()
asCommit :: In arr t a -> Out arr t () -> Trace t arr a ()
asCommit i o = runOut i o

-- | Unit-grounded /emit/ shape: @'Out' a@ plugged against @'In' ()@.
--
-- @
--   asEmit :: Out arr t a -> In arr t () -> Trace t arr () a
-- @
--
-- Same port shape as 'Circuit.Queue.Emit' (@() → a@): harvest @a@ from
-- the unit.  Dual of 'asCommit'.
--
-- Mock 2 (unit-ground emit): pure constant channel yields the seed.
--
-- >>> let (outA, _inA) = open (7 :: Int)
-- >>> let (_outU, inU) = open ()
-- >>> run (asEmit outA inU) ()
-- 7
--
-- Mock 3 (polarity / process choice): harness /write/ is 'asCommit',
-- harness /read/ is 'asEmit'.  Face-to-face composition on one cell is
-- the same pair of ends; re-seat who is \"the process\" and Write/Read
-- names flip — @'In'@/@'Out'@ do not.
--
-- >>> let (outP, inP) = open ("payload" :: String)
-- >>> let (outU, inU) = open ()
-- >>> let write = asCommit inP outU   -- feed process
-- >>> let read  = asEmit  outP inU    -- harvest process
-- >>> run write "ignored"
-- ()
-- >>> run read ()
-- "payload"
asEmit :: Out arr t a -> In arr t () -> Trace t arr () a
asEmit o i = runIn o i

-- | Runtime unit for an STM 'TVar' cell.
--
-- The companion reads the cell; the conjoint writes its input and then reads
-- the cell back through the companion.  This gives 'close' a duplex
-- (write-then-read) meaning over a shared mutable cell.
--
-- >>> import Control.Arrow (Kleisli (..), runKleisli)
-- >>> import Control.Concurrent.STM
-- >>> t <- newTVarIO "before"
-- >>> (outA, inA) <- openSTM t
-- >>> runKleisli (run (close inA outA)) "after"
-- "after"
openSTM :: TVar a -> IO (Out (Kleisli IO) (,) a, In (Kleisli IO) (,) a)
openSTM tvar = pure (outA, inA)
  where
    outA = Out $ \_ -> Arr (Kleisli $ \_ -> readTVarIO tvar)
    inA = In $ \o ->
      Arr
        ( Kleisli $ \a -> do
            atomically (writeTVar tvar a)
            runKleisli (run (runIn o inA)) a
        )
