{-# LANGUAGE RankNTypes #-}

-- | Free channel ends over a base arrow.
--
-- A channel has exactly two ends:
--
--   * 'Out' — the companion (read / emit end), covariant in the payload.
--   * 'In'  — the conjoint (write / commit end), contravariant in the payload.
--
-- 'Ends' is the record that pairs one 'In' with one 'Out'.  The ends are
-- defined purely in terms of the base arrow @arr@; wiring into a traced
-- monoidal category is performed by separate machinery (e.g. "Circuit.Trace").
--
-- The companion and conjoint form an adjunction @In ⊣ Out@.
-- The unit @η@ is 'Circuit.Ends.Unit.open', producing a matched pair;
-- the counit @ε@ is 'close', plugging the pair back together.  The
-- yanking identity @close i o = commit i o@ is the defining characteristic.
module Circuit.Ends
  ( -- * Channel ends (bi-polar contract)
    Out (..),
    In (..),

    -- * Matched pair
    Ends (..),

    -- * Counit
    close,
  )
where

-- $setup
-- >>> import Circuit.Classes ((>>>))
-- >>> import Circuit.Ends
-- >>> import Circuit.Ends.Unit (open)

-- ---------------------------------------------------------------------------
-- Channel ends — the companion and conjoint of the identity functor.
-- ---------------------------------------------------------------------------

-- | 'Out' is the companion of the identity functor.  Covariant in @a@
-- (sits in the output position).
newtype Out arr a = Out
  { -- | Emit through the companion, supplying the other end.
    emit :: forall x. In arr x -> arr x a
  }

-- | 'In' is the conjoint of the identity functor.  Contravariant in
-- @a@ (sits in the input position).
newtype In arr a = In
  { -- | Commit through the conjoint, supplying the other end.
    commit :: forall x. Out arr x -> arr a x
  }

-- | A matched pair of channel ends: one 'In' and one 'Out'.
--
-- This is the bi-polar communication contract.  The conjoint ('In')
-- consumes payloads of type @a@; the companion ('Out') produces payloads
-- of type @b@.  For symmetric channels such as queues @a = b@.
data Ends arr a b = Ends
  { conjoint  :: In arr a   -- ^ Write end (producer), the conjoint.
  , companion :: Out arr b  -- ^ Read end  (consumer), the companion.
  }

-- | Counit of the companion / conjoint adjunction.
--
-- Plug an 'In' and an 'Out' of the same payload type together to produce
-- a morphism of @arr@ from @a@ to @a@.
--
-- 'close' is literally 'commit': the 'In' end already carries the
-- morphism that consumes the payload and produces the result, so
-- plugging just means applying that morphism to the supplied 'Out'.
--
-- Yanking: for the unit ends from "Circuit.Ends.Unit",
-- @close (conjoint ends) (companion ends) = id@.
close :: In arr a -> Out arr a -> arr a a
close contra = commit contra
