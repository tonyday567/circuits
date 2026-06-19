{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}

-- | The free category over a base arrow — just 'Lift' and 'Compose'.
--
-- 'Free' is 'Trace' without the knot constructor.  Where 'Trace' is the free /traced/
-- category, 'Free' is the free category.  The 'freeze' interpreter in
-- "Circuit.Trace" dissolves 'Trace' into a 'Lift' by calling 'trace'
-- on the base arrow, making the decomposition 'realise' = 'runFree' . 'freeze'.
module Circuit.Free
  ( Free (..),
    runFree,
    hoistFree,
  )
where

import Circuit.Traced
import Prelude hiding (id, (.))

#ifdef __GLASGOW_HASKELL__
import Control.Category
#else
import Circuit.Classes
#endif

-- $setup
-- >>> import Circuit.Free
-- >>> import Prelude hiding (id, (.))

-- | The free category over a base arrow @arr@.
--
-- Two constructors:
--
--   * 'Lift' — embed a base arrow.
--   * 'Compose' — sequential composition.
--
-- >>> runFree (Lift (+1) :: Free (->) Int Int) 5
-- 6
data Free arr a b where
  -- | Embed a base arrow.
  Lift :: arr a b -> Free arr a b
  -- | Sequential composition.
  Compose :: Free arr b c -> Free arr a b -> Free arr a c

instance (Category arr) => Category (Free arr) where
  id = Lift id
  (.) = Compose

-- | Interpret a 'Free' to a plain arrow.
--
-- This is the canonical fold — no 'Trace' needed, just 'Category'.
--
-- >>> runFree (Lift (+1) `Compose` Lift (*2) :: Free (->) Int Int) 5
-- 11
runFree :: (Category arr) => Free arr a b -> arr a b
runFree (Lift f) = f
runFree (Compose f g) = runFree f . runFree g

-- | Functor map for 'Free' over the base arrow.
--
-- Lifts a natural transformation on base arrows to a map between
-- free categories.  This is the functorial action used by the
-- counit of the 'Free' ⊣ 'Id' adjunction.
hoistFree :: (Category arr, Category arr') => (forall x y. arr x y -> arr' x y) -> Free arr a b -> Free arr' a b
hoistFree h (Lift f) = Lift (h f)
hoistFree h (Compose f g) = Compose (hoistFree h f) (hoistFree h g)

-- | Lift the 'Traced' class through 'Free'.
--
-- A loop body in @Free arr@ is folded before calling the base 'trace'.
instance (Category arr, Traced arr t) => Traced (Free arr) t where
  trace body = Lift (trace (runFree body))
  untrace f = Lift (untrace (runFree f))
