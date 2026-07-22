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
import Prelude hiding (id, (.))

-- $setup
-- >> import Circuit.Layer (run)
-- >> import Circuit.Loop (Loop (..))
-- >> import Circuit.Free qualified as F

-- | Encode a 'Free' category into a 'HyperF'.
--
-- The lift of the canonical fold 'run' into the final encoding.
--
-- Law: @'observe' . 'encodeFree' = 'run'@ — the two interpreters
-- from Free agree.
--
-- .> observe (encodeFree (F.Lift (+1))) 5
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
-- .> import Circuit.Layer (run)
-- .> import Circuit.Loop (Loop (..))
-- .> observe (encode (Lift (+1) :: Loop (,) (->) Int Int)) 5
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
-- .> let h = Circuit.Hyper.lift (+ 1)
-- .> run (flatten h) 5
-- 6
--
-- Flatten then encode is not identity — the feedback structure is gone:
--
-- .> let h = Circuit.Hyper.lift (+ 1)
-- .> Circuit.Hyper.observe (encode (flatten h)) 5
-- 6
flatten ::
  (HyperBase arr) =>
  HyperF arr a b ->
  Loop (,) arr a b
flatten h = Lift (mkArr (observeH h))
