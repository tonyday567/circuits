{-# LANGUAGE RankNTypes #-}

-- | Net channel ends — the second horizontal instantiation of Out/In.
--
-- The proof spikes in 'Circuit.Ends' show that free ends ('Out'/'In')
-- work over 'Circuit.Trace.Trace'.  This module shows the same pattern
-- works over 'Circuit.Net.Net' — the free traced PROP with bimonoid
-- structure.
--
-- = Why Net matters
--
-- 'Trace' is in normal form (at most one 'Knot' over a base arrow).
-- 'Net' keeps wiring inspectable: 'Copy', 'Plus', 'Par', and 'Knot'
-- are all visible constructors.  This means a Net-based channel can
-- be fanned out to multiple readers (via 'Copy') or merged from
-- multiple writers (via 'Plus').  Trace channels cannot express this
-- because the wiring is collapsed into a single 'Knot'.
--
-- = Spike contents
--
-- * Mock 0 — yanking over Net: 'netOpen' / 'netClose' recovers the seed.
-- * Mock 1 — composition with Net structure: ends compose with 'Par',
--   'Compose', and bimonoid constructors.
-- * Mock 2 — enrich\/melt bridge: a Trace Out\/In pair lifts to Net,
--   composes with Net structure, and melts back to Trace.
--
-- This is a pure spike — no IO, no processes.  The same free-ends
-- design works over both horizontal categories.
module Circuit.Ends.Net
  ( -- * Net channel ends
    NetOut (..),
    NetIn (..),
    netClose,

    -- * Unit
    netOpen,
  )
where

import Circuit.Net (Net (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Circuit.Dagger (Bimonoid, Dagger (..), copy, discard, plus, zero)
-- >>> import Circuit.Ends (Out (..), In (..), close)
-- >>> import Circuit.Ends.Net
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Net (Net (..), enrich, melt)
-- >>> import Circuit.Trace (Trace (..))
-- >>> import Prelude hiding (id, (.))

-- | 'NetOut' is the Net analog of 'Circuit.Ends.Out'.
--
-- Companion of identity in the proarrow equipment over 'Net'.
-- Covariant in @a@ (sits in the output position).
newtype NetOut t arr a = NetOut
  { emitNet :: forall x. NetIn t arr x -> Net t arr x a
  }

-- | 'NetIn' is the Net analog of 'Circuit.Ends.In'.
--
-- Conjoint of identity.  Contravariant in @a@ (sits in the input position).
newtype NetIn t arr a = NetIn
  { commitNet :: forall x. NetOut t arr x -> Net t arr a x
  }

-- | Plug two Net channel ends together.
--
-- @
-- netClose i o = commitNet i o
-- @
--
-- Same shape as 'Circuit.Ends.close' but produces an inspectable 'Net'
-- instead of a 'Trace' in normal form.
netClose :: NetIn t arr a -> NetOut t arr a -> Net t arr a a
netClose i = commitNet i

-- | @η@ — the unit of the Net companion/conjoint adjunction.
--
-- Create two Net channel ends from a seed.  The companion always
-- returns the seed; the conjoint calls the companion back — mutual
-- recursion bottoms out because the companion returns first.
--
-- Mock 0 (yank over Net): 'netClose' recovers the seed, same yanking
-- pattern as 'Circuit.Ends.Unit.open' over 'Trace'.
--
-- >>> let (co, contra) = netOpen (42 :: Int)
-- >>> run (netClose contra co) 99
-- 42
--
-- The seed is recovered independent of the payload — yanking holds.
netOpen :: a -> (NetOut (,) (->) a, NetIn (,) (->) a)
netOpen seed = (co, contra)
  where
    co = NetOut $ \_ -> Lift (const seed)
    contra = NetIn $ \o -> emitNet o contra

-- $mock1
-- Mock 1 — composition with Net structure
--
-- NetOut/NetIn compose with Net's structural constructors.
-- Closing an open pair gives a 'Net a a' that can be composed
-- (via 'Compose') with other Net circuits.
--
-- >>> let (co, contra) = netOpen (7 :: Int)
-- >>> let doubler = Lift (*2) :: Net (,) (->) Int Int
-- >>> let circuit = doubler `Compose` netClose contra co `Compose` Lift (+1)
-- >>> run circuit 10
-- 14
--
-- Pipeline: (+1) then close(const 7) then (*2).  10→11→7→14.

-- $mock2
-- Mock 2 — enrich\/melt bridge
--
-- A Trace Out/In pair lifts to Net via 'enrich', composes with
-- Net structure, and melts back to Trace.  Round-trip preserves
-- observable behaviour.
--
-- >>> let traceCircuit = Arr (const 5) :: Trace (,) (->) Int Int
-- >>> -- Lift to Net
-- >>> let netCircuit = enrich traceCircuit :: Net (,) (->) Int Int
-- >>> -- Compose with Net structure (using Compose, not .)
-- >>> let netPiped = Lift (+3) `Compose` netCircuit :: Net (,) (->) Int Int
-- >>> -- Melt back to Trace
-- >>> run (melt netPiped :: Trace (,) (->) Int Int) 100
-- 8
--
-- The trace circuit (constant 5) composed with (+3):  100→5→8.
-- Melting a Net that was enriched from Trace preserves the result.
