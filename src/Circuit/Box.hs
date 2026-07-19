{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

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
import Circuit.Ends (Ends (..), HasUnit (..), commit, conjoint, companion, emit)
import Circuit.Tensor (Tensor (..), Unit)
import Circuit.Trace (Trace (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Circuit.Ends (Ends(..), HasUnit(..), In(..), Out(..), commit, conjoint, companion, emit)
-- >>> import Circuit.Box (box)
-- >>> import Circuit.Trace (Trace(..))

-- | Embed an 'Ends' into a 'Trace' morphism with unit wires.
--
-- Uses 'par' at the base arrow level and lifts the result with 'Arr'.
--
-- >>> let ends = open :: Ends (->) () ()
-- >>> :t box @(,) ends
-- box @(,) ends :: Trace (,) (->) ((), ()) ((), ())
box ::
  forall t arr a b.
  (HasUnit (Unit t) arr, Tensor t arr) =>
  Ends arr a b ->
  Trace t arr (t a (Unit t)) (t (Unit t) b)
box ends =
  Arr $
    par
      (commit (conjoint ends) (companion open))
      (emit (companion ends) (conjoint open))
