{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

-- | String-diagram boxes from channel ends.
--
-- A matched pair of free ends ('Circuit.Ends.Ends') is a box with one
-- input wire and one output wire.  This module embeds that box into a
-- traced monoidal category by unit-plugging the remaining two slots.
module Circuit.Box
  ( box,
    boxAsymmetric,
  )
where

import Circuit.Category (Category (..), (>>>))
import Circuit.Ends (Ends (..), HasUnit (..), commit, conjoint, companion, emit)
import Circuit.Tensor (Tensor (..), Unit)
import Circuit.Loop (Loop (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Circuit.Ends (Ends, ends)
-- >>> import Circuit.Box (box)
-- >>> import Circuit.Layer (run)

-- | Embed an 'Ends' into a plain @Loop t arr a b@.
--
-- Connects the two channel ends through the unit object, giving a plain
-- @Loop t arr a b@. This is the version most users expect: input on the
-- left, output on the right, with the unit plumbing hidden.
--
-- >>> let e = ends (const ()) (const 42) :: Ends (->) () Int
-- >>> run (box @(,) e) ()
-- 42
box ::
  forall t arr a b.
  (HasUnit (Unit t) arr, Ob arr a, Ob arr b, Ob arr (Unit t)) =>
  Ends arr a b ->
  Loop t arr a b
box ends =
  Lift $
    commit (conjoint ends) (companion (open :: Ends arr (Unit t) (Unit t)))
      >>> emit (companion ends) (conjoint (open :: Ends arr (Unit t) (Unit t)))

-- | Asymmetric box with units exposed on opposite sides.
--
-- Uses 'par' at the base arrow level and lifts the result with 'Lift'.
-- The input carries the unit on the right and the output carries the unit
-- on the left; most users will prefer the unit-normalised 'box'.
--
-- >>> let e = ends (const ()) (const 42) :: Ends (->) () Int
-- >>> run (boxAsymmetric @(,) e) ((), ())
-- ((),42)
boxAsymmetric ::
  forall t arr a b.
  (HasUnit (Unit t) arr, Tensor t arr) =>
  Ends arr a b ->
  Loop t arr (t a (Unit t)) (t (Unit t) b)
boxAsymmetric ends =
  Lift $
    par
      (commit (conjoint ends) (companion open))
      (emit (companion ends) (conjoint open))
