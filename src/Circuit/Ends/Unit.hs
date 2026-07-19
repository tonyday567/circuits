{-# LANGUAGE RankNTypes #-}

-- | Unit channel ends.
--
-- The monoidal unit as a matched pair of free channel ends.  Both ends
-- carry @()@; the companion always emits @()@ and the conjoint commits
-- the payload and asks the companion what to return.
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
-- >>> import Circuit.Ends (Ends(..), In(..), Out(..), close, commit, conjoint, companion, emit)
-- >>> import Circuit.Ends.Unit (HasUnit(..))

-- | Arrows that have unit channel ends.
--
-- The unit ends are the identity-on-@()@ morphism split into its two
-- polar halves.  The companion is constant; the conjoint delegates to
-- the opposing companion.
class (Category arr) => HasUnit arr where
  -- | The monoidal unit as channel ends.
  --
  -- === Yank
  --
  -- >>> let ends = open
  -- >>> close (conjoint ends) (companion ends) ()
  -- ()
  --
  -- === Unit plug
  --
  -- >>> let endsA = open
  -- >>> let endsU = open
  -- >>> commit (conjoint endsA) (companion endsU) ()
  -- ()
  -- >>> emit (companion endsA) (conjoint endsU) ()
  -- ()
  open :: Ends arr () ()

instance HasUnit (->) where
  open = Ends inU outU
    where
      outU = Out $ \_ -> const ()
      inU = In $ \o -> emit o inU

-- | Unit ends for 'Kleisli' @m@.
--
-- Same shape as the @(->)@ instance, but the constant companion returns
-- @()@ in the monad.
instance (Monad m) => HasUnit (Kleisli m) where
  open = Ends inU outU
    where
      outU = Out $ \_ -> Kleisli $ \_ -> pure ()
      inU = In $ \o -> emit o inU
