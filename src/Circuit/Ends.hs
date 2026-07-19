{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Free channel ends over a base arrow.
--
-- A channel has exactly two ends:
--
--   * 'Out' — the companion (read / emit end), covariant in the payload.
--   * 'In'  — the conjoint (write / commit end), contravariant in the payload.
--
-- 'Ends' is the record that pairs one 'In' with one 'Out'.  The ends are
-- defined purely in terms of the base arrow @arr@.
--
-- The companion and conjoint form an adjunction @In ⊣ Out@.
-- The unit @η@ is 'open', producing a matched pair; the counit @ε@ is
-- 'close', plugging the pair back together.  The yanking identity
-- @close i o = commit i o@ is the defining characteristic.
module Circuit.Ends
  ( -- * Channel ends (bi-polar contract)
    Out (..),
    In (..),

    -- * Matched pair
    Ends (..),

    -- * Counit
    close,

    -- * Prefixing an action to an 'In'
    prefixIn,

    -- * Suffixing an action to an 'Out'
    suffixOut,

    -- * Build an 'Ends' from primitive actions
    ends,
    endsK,

    -- * Unit ends (requires constant morphisms)
    HasUnit (..),

  )
where

import Circuit.Classes (Category (..), Discrete (..), (>>>))
import Control.Arrow (Kleisli (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Classes ((>>>))
-- >>> import Circuit.Ends

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
--
-- Together with 'prefixIn' and 'suffixOut', 'Ends' carries an /enriched/
-- profunctor structure over the base category @arr@: 'prefixIn' is the
-- left (contravariant) action by an @arr@-morphism, and 'suffixOut' is
-- the right (covariant) action.  The usual 'Data.Profunctor.dimap' uses
-- functions @(->)@; here the action is by morphisms of @arr@ itself.
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
-- Yanking: for the unit ends from 'open',
-- @close (conjoint ends) (companion ends) = id@.
close :: In arr a -> Out arr a -> arr a a
close contra = commit contra

-- | Precompose an action with a unit 'In' end.
--
-- Given @prefix :: arr a ()@ and the conjoint of the unit ends
-- @'open' :: Ends arr () ()@, produce an 'In' end at type @a@.  Running
-- the resulting end first executes @prefix@ and then delegates to the
-- unit behaviour (which emits through the supplied companion).
--
-- This is the canonical way to build effectful write ends: the unit
-- carries the recursive "continue" part, and @prefix@ is the side effect
-- performed before continuing.
--
-- >>> let endsU = open :: Ends (->) () ()
-- >>> let inA = prefixIn (const ()) (conjoint endsU) :: In (->) Int
-- >>> commit inA (companion endsU) 42
-- ()
prefixIn :: forall arr a. (Discrete arr) => arr a () -> In arr () -> In arr a
prefixIn prefix i = In $ \(o :: Out arr x) -> withOb @arr @a $ withOb @arr @() $ withOb @arr @x $ prefix >>> commit i o

-- | Postcompose an action with a unit 'Out' end.
--
-- Given @suffix :: arr () b@ and the companion of the unit ends
-- @'open' :: Ends arr () ()@, produce an 'Out' end at type @b@.  Running
-- the resulting end first emits through the unit behaviour (which ignores
-- the supplied conjoint) and then executes @suffix@ on the emitted value.
--
-- This is the canonical way to build effectful read ends: the unit
-- carries the recursive "ignore input" part, and @suffix@ is the side
-- effect performed after reading.
--
-- >>> let endsU = open :: Ends (->) () ()
-- >>> let outA = suffixOut (companion endsU) (const 42) :: Out (->) Int
-- >>> emit outA (conjoint endsU) ()
-- 42
suffixOut :: forall arr b. (Discrete arr) => Out arr () -> arr () b -> Out arr b
suffixOut o suffix = Out $ \(i :: In arr x) -> withOb @arr @x $ withOb @arr @() $ withOb @arr @b $ emit o i >>> suffix

-- ---------------------------------------------------------------------------
-- Unit ends
-- ---------------------------------------------------------------------------

-- | Arrows that have unit channel ends for a given unit object @u@.
--
-- The unit ends are the identity-on-@u@ morphism split into its two
-- polar halves.  The companion is constant; the conjoint delegates to
-- the opposing companion.
--
-- These ends require the base arrow to support constant morphisms, so
-- they are captured by this class rather than being definable for all
-- arrows.
class (Category arr) => HasUnit u arr where
  -- | The monoidal unit as channel ends.
  --
  -- === Yank
  --
  -- >>> let ends = open :: Ends (->) () ()
  -- >>> close (conjoint ends) (companion ends) ()
  -- ()
  --
  -- === Unit plug
  --
  -- >>> let endsA = open :: Ends (->) () ()
  -- >>> let endsU = open :: Ends (->) () ()
  -- >>> commit (conjoint endsA) (companion endsU) ()
  -- ()
  -- >>> emit (companion endsA) (conjoint endsU) ()
  -- ()
  open :: Ends arr u u

-- | Build an 'Ends' from a write morphism and a read morphism.
--
-- @write :: arr a ()@ consumes the input payload and produces the unit;
-- @read :: arr () b@ consumes the unit and produces the output payload.
-- The unit ends wire the two halves together.
--
-- This is the canonical way to turn a pair of primitive channel actions
-- into a matched pair of 'In' and 'Out' ends.
ends ::
  forall arr a b.
  (Discrete arr, HasUnit () arr) =>
  arr a () ->
  arr () b ->
  Ends arr a b
ends write receive =
  Ends
    (In $ \(o :: Out arr x) -> withOb @arr @a $ withOb @arr @() $ withOb @arr @x $ write >>> emit o (conjoint open))
    (Out $ \(i :: In arr x) -> withOb @arr @x $ withOb @arr @() $ withOb @arr @b $ commit i (companion open) >>> receive)

-- | Specialization of 'ends' for 'Kleisli' actions.
--
-- @write :: a -> m ()@ consumes the input payload; @receive :: m b@
-- produces the output payload. The unit handling is hidden inside the
-- 'Kleisli' wrappers.
endsK ::
  forall m a b.
  (Monad m) =>
  (a -> m ()) ->
  m b ->
  Ends (Kleisli m) a b
endsK write receive = ends (Kleisli write) (Kleisli $ const receive)

-- | Unit ends for @(->)@ with unit @()@.
--
-- The companion is the constant function returning @()@; the conjoint
-- recursively emits through the supplied companion.
instance HasUnit () (->) where
  open = Ends inU outU
    where
      outU = Out $ \_ -> const ()
      inU = In $ \o -> emit o inU

-- | Unit ends for 'Kleisli' @m@ with unit @()@.
--
-- Same shape as the @(->)@ instance, but the constant companion returns
-- @()@ in the monad.
instance (Monad m) => HasUnit () (Kleisli m) where
  open = Ends inU outU
    where
      outU = Out $ \_ -> Kleisli $ \_ -> pure ()
      inU = In $ \o -> emit o inU
