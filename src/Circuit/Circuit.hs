{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The Circuit GADT: free traced monoidal category.
--
-- `Circuit arr t a b` is the initial encoding of a traced monoidal category
-- over base arrow `arr` with tensor `t`. The three constructors encode:
--
--   - `Lift`: embedding of a base arrow (strict monoidal functor)
--   - `Compose`: sequential composition (category structure)
--   - `Loop`: feedback channel (trace structure)
--
-- The `lower` function interprets any `Circuit` to a plain function via
-- the `Trace` instance on `t`.

module Circuit.Circuit
  ( -- * Circuit GADT
    Circuit (..),

    -- * Interpretation
    reify,
    lower,

    -- * Utilities
    toHyper,
    hyperfy,
    flatten,
  )
where

import Control.Category (Category (..), id, (.))
import Circuit.Traced
import Circuit.Hyper (Hyper (..))
import qualified Circuit.Hyper as Hyper
import Prelude hiding (id, (.))

-- | Circuit arr t a b is the free traced monoidal category.
data Circuit arr t a b where
  -- | Lift embeds a base arrow (strict monoidal functor).
  Lift :: arr a b -> Circuit arr t a b

  -- | Compose performs sequential composition (category structure).
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c

  -- | Loop opens a feedback channel. The tensor t carries the channel type.
  Loop :: arr (t a b) (t a c) -> Circuit arr t b c

instance (Category arr) => Category (Circuit arr t) where
  id = Lift id
  (.) = Compose

instance Functor (Circuit (->) t a) where
  fmap f = Compose (Lift f)

instance (Trace (->) t) => Applicative (Circuit (->) t x) where
  pure a = Lift (const a)
  f <*> v = Lift $ \x -> reify f x (reify v x)

instance (Trace (->) t) => Monad (Circuit (->) t x) where
  m >>= k = Lift $ \x -> reify (k (reify m x)) x

-- | Interpret a Circuit to a plain function via the Trace instance.
--
-- This is the unique traced functor from the initial object (Circuit)
-- to the target category. The Mendler case (when a Loop appears on the
-- left of Compose) enforces the sliding axiom of traced monoidal categories.
lower :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
lower (Lift f) = f
lower (Compose (Loop f) g) = trace (f . untrace (lower g))
lower (Compose f g) = lower f . lower g
lower (Loop k) = trace k

-- | Alias for 'lower': interpret a Circuit as a plain function.
-- Used as the primary name for Circuit elimination to avoid conflict
-- with Hyper's elimination function.
reify :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
reify = lower

-- | Flatten a Hyper to a Circuit by observing it.
--
-- This is the forgetful map from the final encoding to the initial encoding.
-- All feedback structure is lost; only the observable behaviour remains.
flatten :: Hyper a b -> Circuit (->) (,) a b
flatten h = Lift (Hyper.lower h)

-- | Convert a Circuit to a Hyper (unfolding).
--
-- This is the unique traced functor from the initial object (Circuit)
-- to the final object (Hyper). The triangle `Hyper.lower . toHyper = reify` holds,
-- making this the map that respects the adjunction.
toHyper :: Circuit (->) (,) a b -> Hyper a b
toHyper (Lift f) = Hyper.lift f
toHyper (Compose f g) = toHyper f . toHyper g
toHyper (Loop f) = Hyper.lift (trace f)

-- | Alias for 'toHyper'.
hyperfy :: Circuit (->) (,) a b -> Hyper a b
hyperfy = toHyper
