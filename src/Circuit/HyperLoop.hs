{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Bridges between the syntactic circuit types ('Loop', 'Free') and the
-- final semantic encoding ('Circuit.Hyper.HyperF').
--
-- 'Loop' is the free/initial traced monoidal category and 'HyperF' is the
-- final/coinductive one.  The two functors here are the canonical
-- change-of-representation maps:
--
-- * 'encode' / 'encodeFree' interpret syntax into semantics.  A 'Knot'
--   becomes a 'trace'; a 'Lift' becomes a lifted base arrow.
-- * 'flatten' forgets the feedback structure and recovers the underlying
--   observable arrow as a 'Loop'.
--
-- Keeping these bridges in their own module means 'Circuit.Hyper' can stay
-- a pure semantic object: it knows nothing about 'Loop' or 'Free'.
--
-- === doctests
--
-- >>> import Circuit.Hyper (observe)
-- >>> import Circuit.HyperLoop (encode)
-- >>> import Circuit.Loop (Loop (..))
--
-- >>> observe (encode (Lift (+1) :: Loop (,) (->) Int Int)) 5
-- 6
module Circuit.HyperLoop
  ( encode,
    encodeFree,
    flatten,

    -- * Shared-medium composition via base change
    stateKleisli,
    runSharedHyperH,
    sharedHyperBy,
  )
where

import Circuit.Category (Category (..), Ob)
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Free qualified as F
import Circuit.Hyper
  ( HyperBase (..),
    HyperF,
    liftH,
    observeH,
  )
import Circuit.Loop (Loop (..))
import Circuit.Tensor (Schedule (..), Shared (..), sharedBy)
import Control.Arrow (Kleisli (..))
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans.State.Lazy (StateT (..), runStateT)
import Data.Functor.Identity (Identity (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Loop (Loop (..))
-- >>> import Circuit.Free qualified as F
-- >>> import Circuit.Hyper (observe)

-- | Encode a 'Free' category into a 'HyperF'.
--
-- The lift of the canonical fold 'run' into the final encoding.
--
-- Law: @'observe' . 'encodeFree' = 'run'@ — the two interpreters
-- from Free agree.
--
-- >>> observe (encodeFree (F.Lift (+1))) 5
-- 6
encodeFree ::
  (HyperBase arr, Ob arr a, Ob arr b) =>
  F.Free arr a b ->
  HyperF arr a b
encodeFree (F.Lift f) = liftH f
encodeFree (F.Compose f g) = encodeFree f . encodeFree g

-- | Encode a 'Loop' into a 'HyperF'.
--
-- This is the unique traced functor from the initial object ('Loop')
-- to the final object ('HyperF'), satisfying the commuting triangle
-- @'observe' . 'encode' = 'run'@.
--
-- 'Lift' constructors embed directly via 'liftH'; 'Knot' constructors
-- become 'trace' over a hyperfunction.
--
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Loop (Loop (..))
-- >>> observe (encode (Lift (+1) :: Loop (,) (->) Int Int)) 5
-- 6
encode ::
  ( HyperBase arr,
    Strength (,) arr,
    Ob arr a,
    Ob arr b
  ) =>
  Loop (,) arr a b ->
  HyperF arr a b
encode (Lift f) = liftH f
encode (Knot f) = trace (liftH f)

-- | Flatten a 'HyperF' to a 'Loop' by observing it.
--
-- This is the forgetful map from the final encoding to the initial encoding.
-- All feedback structure is lost; only the observable behaviour remains.
--
-- >>> let h = Circuit.Hyper.lift (+ 1)
-- >>> run (flatten h) 5
-- 6
--
-- Flatten then encode is not identity — the feedback structure is gone:
--
-- >>> let h = Circuit.Hyper.lift (+ 1)
-- >>> Circuit.Hyper.observe (encode (flatten h)) 5
-- 6
flatten ::
  (HyperBase arr) =>
  HyperF arr a b ->
  Loop (,) arr a b
flatten h = Lift (mkArr (observeH h))

-- ---------------------------------------------------------------------------
-- Shared-medium composition (the bridge square)
-- ---------------------------------------------------------------------------

-- | Lift a stateful function into the state-enriched Kleisli base.
--
-- This is the base change that makes the medium explicit: a body
-- @arr (s, a) (s, b)@ becomes a Kleisli arrow @a -> StateT s m b@.
stateKleisli ::
  (Monad m) =>
  ((s, a) -> (s, b)) ->
  Kleisli (StateT s m) a b
stateKleisli f = Kleisli $ \a -> StateT $ \s -> let (s', b) = f (s, a) in pure (b, s')

-- | Run a shared-state hyperfunction from an initial medium state.
runSharedHyperH ::
  (MonadFix m) =>
  s ->
  HyperF (Kleisli (StateT s m)) a b ->
  a ->
  m (b, s)
runSharedHyperH s0 h a = runStateT (observeH h a) s0

-- | Shared-medium fusion in the final encoding.
--
-- Two hyperfunctions whose inputs/outputs carry the medium state are fused
-- along that medium using the schedule.  This is the right-hand side of the
-- bridge square:
--
-- @
--   encode (sharedKnotBy sched k1 k2)  ≅  sharedHyperBy sched (encode (Lift k1)) (encode (Lift k2))
-- @
--
-- The implementation extracts the underlying arrows via 'observeH'/'mkArr',
-- composes them with the schedule-driven 'sharedBy', and re-encodes via
-- 'trace'/'liftH'.  The state-enriched base (@Kleisli (StateT s m)@) provides
-- the conceptual home for the medium; this combinator is its value-level
-- presentation.
sharedHyperBy ::
  forall arr s a b c d.
  ( HyperBase arr,
    Strength (,) arr,
    Shared (,) arr,
    Ob arr s,
    Ob arr (a, c),
    Ob arr (b, d),
    Ob arr (s, (a, c)),
    Ob arr (s, (b, d))
  ) =>
  Schedule s ->
  HyperF arr (s, a) (s, b) ->
  HyperF arr (s, c) (s, d) ->
  HyperF arr (a, c) (b, d)
sharedHyperBy sched f g = trace (liftH (sharedBy sched f' g'))
  where
    f' = mkArr (observeH f)
    g' = mkArr (observeH g)
