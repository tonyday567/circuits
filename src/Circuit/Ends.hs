{-# LANGUAGE RankNTypes #-}

-- | 'Circuit.Ends' re-exports 'Out' and 'In' from 'Circuit.Trace'
-- and provides the units 'open' (pure) and 'openSTM' (runtime 'TVar').
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
-- = Free ends only (no cargo wrappers)
--
-- The API is 'In', 'Out', 'open', 'close', and the field runners
-- 'runIn' / 'runOut'.  Unit-grounding is not a second primitive — plug
-- the other end at @()@ with 'runOut' / 'runIn' directly:
--
-- @
--   runOut inA outU  :: Trace t arr a ()   -- In  at unit  (a → ())
--   runIn  outA inU  :: Trace t arr () a   -- Out at unit  (() → a)
-- @
--
-- Doctests below gate that story (yank + unit plug + polarity).
module Circuit.Ends
  ( -- * Free channel ends
    Out (..),
    In (..),
    close,

    -- * Unit (matched pair)
    open,

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
-- >>> import Circuit.Trace (Out (..), In (..), runIn, runOut)

-- | @η@ — the unit of the companion/conjoint adjunction (pure case).
--
-- Create two channel ends from a seed value.  The seed becomes the
-- channel's initial state.  The companion always returns the seed;
-- the conjoint calls the companion back, which returns the seed —
-- the mutual recursion bottoms out because the companion returns first.
--
-- Yank: 'close' recovers the seed, independent of the payload.
--
-- >>> let (outA, inA) = open (42 :: Int)
-- >>> run (close inA outA) 99
-- 42
--
-- Unit plug (no wrapper): 'runOut' / 'runIn' at @()@ are the grounded ports.
--
-- >>> let (outA, inA) = open (7 :: Int)
-- >>> let (outU, inU) = open ()
-- >>> run (runOut inA outU) 99
-- ()
-- >>> run (runIn outA inU) ()
-- 7
--
-- Polarity: feed = 'runOut' (In against unit Out); harvest = 'runIn'
-- (Out against unit In).  Re-seat who is \"the process\" — verbs flip;
-- 'In'/'Out' do not.
--
-- >>> let (outP, inP) = open ("payload" :: String)
-- >>> let (outU, inU) = open ()
-- >>> run (runOut inP outU) "ignored"
-- ()
-- >>> run (runIn outP inU) ()
-- "payload"
open :: a -> (Out (->) (,) a, In (->) (,) a)
open seed = (outA, inA)
  where
    outA = Out $ \_ -> Arr (const seed)
    inA = In $ \o -> runIn o inA

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
