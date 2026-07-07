{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The dagger/bimonoid layer of circuit wiring.
--
-- This module collects the algebraic structure that every wire carries in a
-- circuit category:
--
-- * 'Monoid' — the monoid on channel objects (fan-in of cotangents).
-- * 'Comonoid' — the comonoid on channel objects (fan-out of values).
-- * 'Bimonoid' — both together, the precondition for 'Circuit.Net.transpose'.
-- * 'Dagger' — the free dagger category over a base arrow, pairing a forward
--   arrow with a backward arrow.  'transpose' is the dagger operation.
--
-- The four structural rows of 'Circuit.Net' ('Circuit.Net.Copy',
-- 'Circuit.Net.Discard', 'Circuit.Net.Plus', 'Circuit.Net.Zero') are exactly
-- the generators of this bimonoid.  In a dagger setting,
-- copy and add are adjoint, as are discard and zero.  'Dagger' makes that
-- duality explicit: a dagger wire's forward direction copies while its
-- backward direction adds.
module Circuit.Dagger
  ( -- * Monoid
    Monoid (..),

    -- * Comonoid
    Comonoid (..),

    -- * Bimonoid
    Bimonoid,

    -- * Dagger
    Dagger (..),
    transpose,
  )
where

#ifdef __GLASGOW_HASKELL__
import Control.Category
#else
import Circuit.Classes
#endif

import Circuit.Monoidal (Action (..))
import Circuit.Monoidal.Category (Monoidal (..))
import Circuit.Trace (Traced (..))
import Prelude hiding (Monoid, id, (.))

-- $setup
-- >>> import Circuit.Dagger
-- >>> import Circuit.Monoidal (Action (..))
-- >>> import Circuit.Trace (Traced (..))
-- >>> import Control.Category
-- >>> import Prelude hiding (id, (.), Monoid)

-- ---------------------------------------------------------------------------
-- Monoid: monoid structure on channel objects
-- ---------------------------------------------------------------------------

-- | A commutative monoid on channel objects.
--
-- Not the same as arithmetic '+'; this is the operation by which parallel
-- contributions to the same wire combine.  In reverse-mode AD, fan-out on
-- the forward pass becomes fan-in (summation) on the backward pass.
class Monoid arr a where
  -- | Combine two values of the channel type.
  plus :: arr (a, a) a

  -- | The neutral element.
  zero :: arr () a

-- | The unit type carries the trivial monoid.
--
-- >>> plus ((), ()) :: ()
-- ()
-- >>> zero () :: ()
-- ()
instance Monoid (->) () where
  plus _ = ()
  {-# INLINE plus #-}
  zero _ = ()
  {-# INLINE zero #-}

-- | Numeric carriers.  'plus' is addition, 'zero' is 0.
--
-- >>> plus (1, 2) :: Int
-- 3
-- >>> zero () :: Int
-- 0
-- >>> plus (1.0, 2.0) :: Double
-- 3.0
-- >>> zero () :: Double
-- 0.0
instance Monoid (->) Int where
  plus = uncurry (+)
  {-# INLINE plus #-}
  zero _ = 0
  {-# INLINE zero #-}

instance Monoid (->) Integer where
  plus = uncurry (+)
  {-# INLINE plus #-}
  zero _ = 0
  {-# INLINE zero #-}

instance Monoid (->) Double where
  plus = uncurry (+)
  {-# INLINE plus #-}
  zero _ = 0
  {-# INLINE zero #-}

instance Monoid (->) Float where
  plus = uncurry (+)
  {-# INLINE plus #-}
  zero _ = 0
  {-# INLINE zero #-}

-- | Boolean monoid under disjunction.
--
-- Idempotent: @plus . copy = id@ — the relations/Boolean profile where
-- @True || True = True@.  'Circuit.Trace.Trace' 'Either' loops terminate without
-- truncated iteration because countable sums in an idempotent monoid
-- converge.
--
-- >>> plus (True, False) :: Bool
-- True
-- >>> zero () :: Bool
-- False
instance Monoid (->) Bool where
  plus = uncurry (||)
  {-# INLINE plus #-}
  zero _ = False
  {-# INLINE zero #-}

-- | Componentwise addition on pairs.  Vanishing depends on this.
--
-- >>> plus ((3, 4), (5, 6)) :: (Int, Int)
-- (8,10)
instance (Monoid (->) a, Monoid (->) b) => Monoid (->) (a, b) where
  plus ((a, b), (a', b')) = (plus (a, a'), plus (b, b'))
  {-# INLINE plus #-}
  zero u = (zero u, zero u)
  {-# INLINE zero #-}

-- | Lists via elementwise 'plus', padded with 'zero'.
--
-- For lists of unequal length, the shorter list is implicitly extended
-- with the element 'zero' — the cotangent of an absent value makes no
-- contribution. The unit is the empty list.
--
-- >>> plus ([1, 2], [3, 4, 5]) :: [Int]
-- [4,6,5]
-- >>> plus ([], [3, 4, 5]) :: [Int]
-- [3,4,5]
instance (Monoid (->) a) => Monoid (->) [a] where
  plus (xs, ys) = go xs ys
    where
      go [] [] = []
      go [] (y : ys') = plus (zero (), y) : go [] ys'
      go (x : xs') [] = plus (x, zero ()) : go xs' []
      go (x : xs') (y : ys') = plus (x, y) : go xs' ys'
  {-# INLINE plus #-}
  zero _ = []
  {-# INLINE zero #-}

-- ---------------------------------------------------------------------------
-- Comonoid: comonoid structure on channel objects
-- ---------------------------------------------------------------------------

-- | A cocommutative comonoid on channel objects.
--
-- Laws:
--
-- @
--   fst . copy = id              -- left unit
--   snd . copy = id              -- right unit
--   (copy × id) . copy = (id × copy) . copy  -- coassociativity
--   swap . copy = copy            -- cocommutativity
-- @
class Comonoid arr a where
  -- | Copy a value into a pair.
  copy :: arr a (a, a)

  -- | Discard a value.
  discard :: arr a ()

-- | Both the comonoid and monoid on a channel object.
--
-- A constraint synonym — no instance required.  On a cartesian base arrow,
-- every type carries both structures.  This is the precondition for
-- 'Circuit.Net.transpose' to be total.
type Bimonoid arr a = (Comonoid arr a, Monoid arr a)

-- | Every type copies for free in a cartesian category (Fox's theorem).
--
-- >>> copy (42 :: Int)
-- (42,42)
-- >>> discard (42 :: Int)
-- ()
instance Comonoid (->) a where
  copy a = (a, a)
  {-# INLINE copy #-}
  discard _ = ()
  {-# INLINE discard #-}

-- ---------------------------------------------------------------------------
-- Dagger: the free dagger category over a base arrow
-- ---------------------------------------------------------------------------

-- | The free dagger category over a base arrow.
--
-- @Dagger arr a b@ is a pair of arrows @arr a b@ (forward) and
-- @arr b a@ (backward).  Composition is covariant forward, contravariant
-- backward: @Dagger f g . Dagger f' g' = Dagger (f . f') (g' . g)@.
--
-- >>> let d = Dagger (+1) (subtract 1) :: Dagger (->) Int Int
-- >>> front d 5
-- 6
-- >>> back d 6
-- 5
data Dagger arr a b = Dagger
  { -- | The forward direction.
    front :: arr a b,
    -- | The backward direction.
    back :: arr b a
  }

-- | The dagger operation: swap forward and backward.
--
-- Involutive: @transpose . transpose = id@.
transpose :: Dagger arr a b -> Dagger arr b a
transpose (Dagger f g) = Dagger g f

instance (Category arr) => Category (Dagger arr) where
  id = Dagger id id
  {-# INLINE id #-}
  Dagger f g . Dagger f' g' = Dagger (f . f') (g' . g)
  {-# INLINE (.) #-}

instance (Traced t arr) => Traced t (Dagger arr) where
  trace (Dagger f g) = Dagger (trace f) (trace g)
  {-# INLINE trace #-}
  untrace (Dagger f g) = Dagger (untrace f) (untrace g)
  {-# INLINE untrace #-}

-- | Forward copy, backward add — the bimonoid self-duality.
instance (Comonoid arr a, Monoid arr a) => Comonoid (Dagger arr) a where
  copy = Dagger copy plus
  {-# INLINE copy #-}
  discard = Dagger discard zero
  {-# INLINE discard #-}

-- | Forward add, backward copy.
instance (Comonoid arr a, Monoid arr a) => Monoid (Dagger arr) a where
  plus = Dagger plus copy
  {-# INLINE plus #-}
  zero = Dagger zero discard
  {-# INLINE zero #-}

instance (Action t arr) => Action t (Dagger arr) where
  par (Dagger f g) (Dagger f' g') = Dagger (par f f') (par g g')
  {-# INLINE par #-}
  swap = Dagger swap swap
  {-# INLINE swap #-}

-- | Lift monoidal structure through 'Dagger'.
instance (Monoidal t arr) => Monoidal t (Dagger arr) where
  assoc = Dagger assoc assoc'
  assoc' = Dagger assoc' assoc
  braid = Dagger braid braid
