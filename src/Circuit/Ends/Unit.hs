{-# LANGUAGE RankNTypes #-}

-- | Unit channel ends.
--
-- The monoidal unit as a matched pair of free channel ends.  Both ends
-- carry the unit object @u@ of the ambient tensor; the companion always
-- emits @u@ and the conjoint commits the payload and asks the companion
-- what to return.
--
-- These ends require the base arrow to support constant morphisms, so
-- they are captured by the 'HasUnit' class rather than living in the
-- core "Circuit.Ends" abstraction.
module Circuit.Ends.Unit
  ( HasUnit (..),
  )
where

import Circuit.Classes (Category (..))
import Circuit.Ends (Ends (..), In (..), Out (..), emit)
import Control.Arrow (Kleisli (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Classes ((>>>))
-- >>> import Circuit.Ends (Ends(..), In(..), Out(..), close, commit, conjoint, companion, emit)
-- >>> import Circuit.Ends.Unit (HasUnit(..))

-- | Arrows that have unit channel ends for a given unit object @u@.
--
-- The unit ends are the identity-on-@u@ morphism split into its two
-- polar halves.  The companion is constant; the conjoint delegates to
-- the opposing companion.
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
