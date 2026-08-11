-- | Mediator-as-shared-state for the ⅋ connective.
--
-- A 'Circuit.Mediate.Mediator' is a state machine with residual state @s@.
-- In the ⅋ picture the residual is not a field on the channel; it is the
-- shared feedback wire that the participants touch in series.  This module
-- expresses a mediator as a 'Circuit.Tensor.sharedBy' body with an explicit
-- seed.
--
-- The decomposition follows the corrected algebra:
--
-- @
-- sharedBy sched f g  =  stepS sched  ⨟ₛ  ambient_c f  ⨟ₛ  ambient_b g
-- @
--
-- The two bodies are the two factors on the medium axis.  For a mediator
-- whose step is @s -> a -> (s, Maybe b)@, the left body stores one input
-- into the residual and the right body consumes a second input together
-- with the stored residual to produce an output.
--
-- Note on seeding.  The 'mediateSharedBody' form takes an explicit seed
-- @s0@ and runs one step; this is the direct analogue of 'register' and
-- 'idChannel'.  Wrapping the body in a @(,)@ 'Circuit.Loop.Knot' would make
-- the seed the fixed point of the body rather than an explicit argument.
-- For finite-state mediators like @pairSum@ the body is strict in the
-- feedback state, so the fixed point is not productive; the explicit-seed
-- form is the one that behaves.
module Circuit.Tensor.Mediate
  ( mediateSharedBody,
    mediateStoreBody,
    mediateEmitBody,
  )
where

import Circuit.Mediate (Mediator (..))
import Circuit.Tensor (Schedule (..), sharedBy)
import Prelude

-- | Store an input into the mediator's residual, discarding any emitted
-- output.  This is the left factor on the shared medium.
mediateStoreBody :: Mediator s a b -> (s, a) -> (s, ())
mediateStoreBody med (s, x) =
  let (s', _) = medStep med s x
   in (s', ())

-- | Consume an input together with the current residual, returning whatever
-- the mediator emits.  This is the right factor on the shared medium.
mediateEmitBody :: Mediator s a b -> (s, a) -> (s, Maybe b)
mediateEmitBody med (s, x) = medStep med s x

-- | One step of the mediated composition, with an explicit seed.
--
-- The input pair is @(storedInput, triggerInput)@.  The left factor stores
-- @storedInput@ into the residual; the right factor feeds @triggerInput@
-- together with the updated residual to the mediator step.  The schedule
-- chooses the order of the two factors, which is observable when the
-- mediator needs the stored value before it can emit.
mediateSharedBody ::
  Mediator s a b ->
  Schedule s ->
  (s, (a, a)) ->
  (s, ((), Maybe b))
mediateSharedBody med sched =
  sharedBy sched (mediateStoreBody med) (mediateEmitBody med)
