{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Adjunctions organising the library.
--
-- The tower of free/forgetful functors:
--
-- @
-- Net t  ⊣  Circuit t  ⊣  Free  ⊣  Id
-- @
--
-- Each left adjoint adds structure; each right adjoint forgets it:
--
-- * 'Id'       — base arrow (no structure)
-- * 'Free'     — adds sequential composition
-- * 'Circuit t'— adds feedback loops over tensor @t@
-- * 'Net t'    — adds monoidal and bimonoid wiring
--
-- The units are the canonical inclusions ("lift . lift" patterns are
-- exactly the inclusion into a composite free construction).  The
-- counits are the canonical folds; nested counits collapse the
-- corresponding nested free layers.
--
-- Iconic equations:
--
-- * 'loom'  = 'reify' . 'melt'      = 'runFree' . 'freeze' . 'melt'
-- * 'reify' = 'runFree' . 'freeze'
module Circuit.Adjunction where

import Circuit.Trace qualified as T
import Circuit.Free qualified as F
import Circuit.Net (Net (..), melt)
import Circuit.Monoidal (MonoidalP (..))
import Circuit.Traced qualified as Tr
import Control.Category (Category, id, (.))
import Data.Kind (Constraint, Type)
import Prelude hiding (id, (.))

-- | Identity profunctor — wraps the base arrow as a profunctor endofunctor.
newtype Id arr a b = Id {unId :: arr a b}

instance Category arr => Category (Id arr) where
  id = Id id
  Id f . Id g = Id (f . g)

-- | Adjunction class for profunctor endofunctors.
-- @f arr@ is a category over base @arr@; unit/counit are natural transformations.
class Adjunction (f :: (k -> k -> Type) -> k -> k -> Type)
                 (u :: (k -> k -> Type) -> k -> k -> Type)
                 | f -> u where
  type AdjC f u (arr :: k -> k -> Type) :: Constraint
  type AdjC f u arr = ()
  unit   :: AdjC f u arr => arr a b -> u (f arr) a b
  counit :: AdjC f u arr => f (u arr) a b -> arr a b

-- | Free ⊣ Id — free category, forgetful to base arrow.
--
-- Unit: embed a base arrow as a single 'Lift'.
-- Counit: flatten @Free (Id arr)@ by unwrapping 'Id' and folding 'Free'.
instance Adjunction F.Free Id where
  type AdjC F.Free Id arr = Category arr
  unit x = Id (F.Lift x)
  counit c = F.runFree (F.hoistFree unId c)

-- | Circuit t ⊣ Free.
--
-- Unit: double lift — base arrow -> 'Circuit' -> 'Free (Circuit t arr)'.
-- Counit: collapse @Circuit t (Free arr)@ by freezing to @Free (Free arr)@,
-- then joining the nested 'Free' layers with 'runFree'.
instance Adjunction (T.Circuit t) F.Free where
  type AdjC (T.Circuit t) F.Free arr = (Category arr, Tr.Trace arr t)
  unit x = F.Lift (T.Lift x)
  counit = F.runFree . F.runFree . T.freeze

-- | Net t ⊣ Circuit t.
--
-- Unit: double lift — base arrow -> 'Net' -> 'Circuit (Net t arr)'.
-- Counit: collapse @Net t (Circuit t arr)@ by melting to
-- @Circuit t (Circuit t arr)@, then joining the nested 'Circuit' layers
-- with 'reify'.
instance Adjunction (Net t) (T.Circuit t) where
  type AdjC (Net t) (T.Circuit t) arr = (Tr.Trace arr t, MonoidalP arr)
  unit x = T.Lift (Lift x)
  counit = T.reify . T.reify . melt
