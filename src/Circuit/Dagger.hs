{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The dagger/bimonoid layer of circuit wiring.
--
-- This module collects the algebraic structure that every wire carries in a
-- circuit category:
--
-- * 'Additive' — the monoid on channel objects (fan-in of cotangents).
-- * 'Dup' — the comonoid on channel objects (fan-out of values).
-- * 'Linear' — both together, the precondition for 'Circuit.Net.transpose'.
-- * 'Duplex' — the free dagger category over a base arrow, pairing a forward
--   arrow with a backward arrow.
--
-- The four structural rows of 'Circuit.Net' ('Copy', 'Discard', 'Add',
-- 'Zero') are exactly the generators of this bimonoid.  In a dagger setting,
-- copy and add are adjoint, as are discard and zero.  'Duplex' makes that
-- duality explicit: a duplex wire's forward direction copies while its
-- backward direction adds.
module Circuit.Dagger
  ( -- * Additive (monoid)
    Additive (..),

    -- * DerivingVia newtypes
    ViaNum (..),

    -- * Dup (comonoid)
    Dup (..),

    -- * Linear (bimonoid)
    Linear,

    -- * Duplex (dagger)
    Duplex (..),
    transposeDuplex,
  )
where

#if __GLASGOW_HASKELL__ >= 910
import Control.Category
#else
import Circuit.Classes
#endif

import Circuit.Monoidal (MonoidalP (..))
import Circuit.Traced (Trace (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> 1 + 1 :: Int
-- 2
-- >>> import Circuit.Dagger
-- >>> import Circuit.Monoidal (MonoidalP (..))
-- >>> import Circuit.Traced (Trace (..))
-- >>> import Control.Category
-- >>> import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- Additive: monoid structure on channel objects
-- ---------------------------------------------------------------------------

-- | A commutative monoid on channel objects.
--
-- Not the same as arithmetic '+'; this is the operation by which parallel
-- contributions to the same wire combine.  In reverse-mode AD, fan-out on
-- the forward pass becomes fan-in (summation) on the backward pass.
class Additive arr a where
  -- | Combine two values of the channel type.
  plus :: arr (a, a) a

  -- | The neutral element.
  zero :: arr () a

-- | Newtype for deriving 'Additive' from 'Num'.
newtype ViaNum a = ViaNum {unViaNum :: a}

instance (Num a) => Additive (->) (ViaNum a) where
  plus (x, y) = ViaNum (unViaNum x + unViaNum y)
  {-# INLINE plus #-}
  zero _ = ViaNum 0
  {-# INLINE zero #-}

-- | Concrete numeric carriers via 'ViaNum'.
--
-- >>> plus (1, 2) :: Int
-- 3
-- >>> zero () :: Int
-- 0
-- >>> plus (1.0, 2.0) :: Double
-- 3.0
-- >>> zero () :: Double
-- 0.0
deriving via ViaNum Double instance Additive (->) Double
deriving via ViaNum Int    instance Additive (->) Int

-- | The unit type carries the trivial monoid.
--
-- >>> plus ((), ()) :: ()
-- ()
-- >>> zero () :: ()
-- ()
instance Additive (->) () where
  plus _ = ()
  {-# INLINE plus #-}
  zero _ = ()
  {-# INLINE zero #-}

-- | Componentwise addition on pairs.  Vanishing depends on this.
--
-- >>> plus ((3, 4), (5, 6)) :: (Int, Int)
-- (8,10)
instance (Additive (->) a, Additive (->) b) => Additive (->) (a, b) where
  plus ((a, b), (a', b')) = (plus (a, a'), plus (b, b'))
  {-# INLINE plus #-}
  zero u = (zero u, zero u)
  {-# INLINE zero #-}

-- | Lists via elementwise 'plus', padded with 'zero'.  Stream cotangents.
--
-- For lists of unequal length, the shorter list is implicitly extended
-- with 'zero' — the cotangent of an absent value makes no contribution.
--
-- >>> plus ([1, 2], [3, 4, 5]) :: [Int]
-- [4,6,5]
-- >>> plus ([], [3, 4, 5]) :: [Int]
-- [3,4,5]
instance Additive (->) a => Additive (->) [a] where
  plus (xs, ys) = go xs ys
    where
      go [] [] = []
      go [] (y : ys') = plus (zero (), y) : go [] ys'
      go (x : xs') [] = plus (x, zero ()) : go xs' []
      go (x : xs') (y : ys') = plus (x, y) : go xs' ys'
  {-# INLINE plus #-}
  zero _ = repeat (zero ())
  {-# INLINE zero #-}

-- ---------------------------------------------------------------------------
-- Dup: comonoid structure on channel objects
-- ---------------------------------------------------------------------------

-- | A cocommutative comonoid on channel objects.
--
-- Laws:
--
-- @
--   fst . dup = id              -- left unit
--   snd . dup = id              -- right unit
--   (dup × id) . dup = (id × dup) . dup  -- coassociativity
--   swap . dup = dup            -- cocommutativity
-- @
class Dup arr a where
  -- | Copy a value into a pair.
  dup :: arr a (a, a)

  -- | Discard a value.
  discard :: arr a ()

-- | Both the comonoid ('Dup') and monoid ('Additive') on a channel object.
--
-- A constraint synonym — no instance required.  On a linear base arrow,
-- every type carries both structures.  This is the precondition for
-- 'Circuit.Net.transpose' to be total.
type Linear arr a = (Dup arr a, Additive arr a)

-- | Every type copies for free in a cartesian category (Fox's theorem).
--
-- >>> dup (42 :: Int)
-- (42,42)
-- >>> discard (42 :: Int)
-- ()
instance Dup (->) a where
  dup a = (a, a)
  {-# INLINE dup #-}
  discard _ = ()
  {-# INLINE discard #-}

-- ---------------------------------------------------------------------------
-- Duplex: the free dagger category over a base arrow
-- ---------------------------------------------------------------------------

-- | A full-duplex wire: an arrow paired with a designated arrow back.
--
-- @Duplex arr a b@ is a pair of arrows @arr a b@ (forward) and
-- @arr b a@ (backward).  Composition is covariant forward, contravariant
-- backward: @Duplex f g . Duplex f' g' = Duplex (f . f') (g' . g)@.
--
-- Categorically: the free dagger category over @arr@.
--
-- >>> let d = Duplex (+1) (subtract 1) :: Duplex (->) Int Int
-- >>> front d 5
-- 6
-- >>> back d 6
-- 5
data Duplex arr a b = Duplex
  { -- | The forward direction.
    front :: arr a b
  , -- | The backward direction.
    back :: arr b a
  }

-- | The dagger: swap forward and backward.
--
-- Involutive: @transposeDuplex . transposeDuplex = id@.
transposeDuplex :: Duplex arr a b -> Duplex arr b a
transposeDuplex (Duplex f g) = Duplex g f

instance Category arr => Category (Duplex arr) where
  id = Duplex id id
  {-# INLINE id #-}
  Duplex f g . Duplex f' g' = Duplex (f . f') (g' . g)
  {-# INLINE (.) #-}

instance Trace arr t => Trace (Duplex arr) t where
  trace (Duplex f g) = Duplex (trace f) (trace g)
  {-# INLINE trace #-}
  untrace (Duplex f g) = Duplex (untrace f) (untrace g)
  {-# INLINE untrace #-}

-- | Forward copy, backward add — the bimonoid self-duality.
instance (Dup arr a, Additive arr a) => Dup (Duplex arr) a where
  dup = Duplex dup plus
  {-# INLINE dup #-}
  discard = Duplex discard zero
  {-# INLINE discard #-}

-- | Forward add, backward copy.
instance (Dup arr a, Additive arr a) => Additive (Duplex arr) a where
  plus = Duplex plus dup
  {-# INLINE plus #-}
  zero = Duplex zero discard
  {-# INLINE zero #-}

instance MonoidalP arr => MonoidalP (Duplex arr) where
  parA (Duplex f g) (Duplex f' g') = Duplex (parA f f') (parA g g')
  {-# INLINE parA #-}
  swapA = Duplex swapA swapA
  {-# INLINE swapA #-}
