{-# LANGUAGE RankNTypes #-}

-- | String-diagram boxes from channel ends.
--
-- A matched pair of free ends ('Circuit.Ends.Ends') is a box with one
-- input wire and one output wire.  This module embeds that box into a
-- traced monoidal category by unit-plugging the remaining two slots.
module Circuit.Box
  ( box,
  )
where

import Circuit.Classes (Category (..))
import Circuit.Ends (Ends (..), commit, conjoint, companion, emit)
import Circuit.Ends.Unit (HasUnit (..))
import Circuit.Monoidal (Tensor (..))
import Circuit.Trace (Trace (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Ends (Ends(..), In(..), Out(..), commit, conjoint, companion, emit)
-- >>> import Circuit.Box (box)
-- >>> import Circuit.Ends.Unit (HasUnit(..))
-- >>> import Circuit.Trace (Trace(..))

-- | Embed an 'Ends' into a 'Trace' morphism with unit wires.
--
-- Uses 'par' at the base arrow level and lifts the result with 'Arr'.
--
-- >>> let ends = open
-- >>> :t box ends
-- box ends
--   :: (HasUnit arr, Circuit.Monoidal.Tensor (,) arr) =>
--      Trace (,) arr ((), ()) ((), ())
box :: (HasUnit arr, Tensor (,) arr) => Ends arr a b -> Trace (,) arr (a, ()) ((), b)
box ends =
  Arr $
    par
      (commit (conjoint ends) (companion open))
      (emit (companion ends) (conjoint open))
