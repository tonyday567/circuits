{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The dagger/bimonoid layer of circuit wiring.
--
-- This module collects the algebraic structure that every wire carries in a
-- circuit category:
--
-- * 'Copy' / 'Discard' — the comonoid on channel objects (fan-out of values).
-- * 'Merge' / 'Zero' — the monoid on channel objects (fan-in of contributions).
-- * 'Bimonoid' — all four together, the precondition for 'Circuit.Net.transpose'.
-- * @Dagger@ — the free dagger category over a base arrow, pairing a forward
--   arrow with a backward arrow.  'transpose' is the dagger operation.
--
-- The four structural rows of 'Circuit.Net' ('Circuit.Net.Copy',
-- 'Circuit.Net.Discard', 'Circuit.Net.Plus', 'Circuit.Net.Zero') are exactly
-- the generators of this bimonoid.  In a dagger setting,
-- copy and add are adjoint, as are discard and zero.  @Dagger@ makes that
-- duality explicit: a dagger wire's forward direction copies while its
-- backward direction adds.
--
-- The older bundled classes 'CopyDiscard' and 'MergeZero' are retained as
-- constraint synonyms for compatibility, but the four capabilities can now be
-- required independently.  This exposes affine settings where discard is
-- natural but copy is not (or vice versa).
module Circuit.Dagger
  ( -- * Copy
    Copy (..),

    -- * Discard
    Discard (..),

    -- * Merge
    Merge (..),

    -- * Zero
    Zero (..),

    -- * Bundled synonyms
    CopyDiscard,
    MergeZero,
    Bimonoid,

    -- * Dagger
    Dagger (..),
    transpose,
  )
where

import Circuit.Category (Category (..), Discrete (..), ObDict (..), withObDict, (.>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Tensor (Action (..), Tensor (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Dagger
-- >>> import Circuit.Tensor (Action (..), Tensor (..))
-- >>> import Circuit.Channel (Traced (..))
-- >>> import Circuit.Category (Category (..), Discrete (..), (.>))
-- >>> import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- Merge / Zero: monoid structure on channel objects
-- ---------------------------------------------------------------------------

-- | Combine two values of the channel type.
--
-- Not the same as arithmetic '+'; this is the operation by which parallel
-- contributions to the same wire combine.  Fan-out on the forward pass
-- becomes fan-in (summation) on the backward pass.
class Merge arr a where
  plus :: arr (a, a) a

-- | The neutral element for 'plus'.
class Zero arr a where
  zero :: arr () a

-- | The older bundled monoid class, retained as a synonym.
type MergeZero arr a = (Merge arr a, Zero arr a)

-- | The unit type carries the trivial monoid.
--
-- >>> plus ((), ()) :: ()
-- ()
-- >>> zero () :: ()
-- ()
instance Merge (->) () where
  plus _ = ()
  {-# INLINE plus #-}

instance Zero (->) () where
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
instance Merge (->) Int where
  plus = uncurry (+)
  {-# INLINE plus #-}

instance Zero (->) Int where
  zero _ = 0
  {-# INLINE zero #-}

instance Merge (->) Integer where
  plus = uncurry (+)
  {-# INLINE plus #-}

instance Zero (->) Integer where
  zero _ = 0
  {-# INLINE zero #-}

instance Merge (->) Double where
  plus = uncurry (+)
  {-# INLINE plus #-}

instance Zero (->) Double where
  zero _ = 0
  {-# INLINE zero #-}

instance Merge (->) Float where
  plus = uncurry (+)
  {-# INLINE plus #-}

instance Zero (->) Float where
  zero _ = 0
  {-# INLINE zero #-}

-- | Boolean monoid under disjunction.
--
-- Idempotent because @True || True = True@.
--
-- >>> plus (True, False) :: Bool
-- True
-- >>> zero () :: Bool
-- False
instance Merge (->) Bool where
  plus = uncurry (||)
  {-# INLINE plus #-}

instance Zero (->) Bool where
  zero _ = False
  {-# INLINE zero #-}

-- | Componentwise 'plus' on pairs.
--
-- >>> plus ((3, 4), (5, 6)) :: (Int, Int)
-- (8,10)
instance (Merge (->) a, Merge (->) b) => Merge (->) (a, b) where
  plus ((a, b), (a', b')) = (plus (a, a'), plus (b, b'))
  {-# INLINE plus #-}

instance (Zero (->) a, Zero (->) b) => Zero (->) (a, b) where
  zero u = (zero u, zero u)
  {-# INLINE zero #-}

-- | Lists via elementwise 'plus', padded with 'zero'.
--
-- For lists of unequal length, the shorter list is implicitly extended
-- with the element 'zero'. The unit is the empty list.
--
-- >>> plus ([1, 2], [3, 4, 5]) :: [Int]
-- [4,6,5]
-- >>> plus ([], [3, 4, 5]) :: [Int]
-- [3,4,5]
instance (Merge (->) a, Zero (->) a) => Merge (->) [a] where
  plus (xs, ys) = go xs ys
    where
      go [] [] = []
      go [] (y : ys') = plus (zero (), y) : go [] ys'
      go (x : xs') [] = plus (x, zero ()) : go xs' []
      go (x : xs') (y : ys') = plus (x, y) : go xs' ys'
  {-# INLINE plus #-}

instance Zero (->) [a] where
  zero _ = []
  {-# INLINE zero #-}

-- ---------------------------------------------------------------------------
-- Copy / Discard: comonoid structure on channel objects
-- ---------------------------------------------------------------------------

-- | Copy a value into a pair.
--
-- Laws:
--
-- @
--   fst . copy = id              -- left unit
--   snd . copy = id              -- right unit
--   (copy × id) . copy = (id × copy) . copy  -- coassociativity
--   swap . copy = copy            -- cocommutativity
-- @
class Copy arr a where
  copy :: arr a (a, a)

-- | Discard a value.
class Discard arr a where
  discard :: arr a ()

-- | The older bundled comonoid class, retained as a synonym.
type CopyDiscard arr a = (Copy arr a, Discard arr a)

-- | Both the comonoid and monoid on a channel object.
--
-- A constraint synonym — no instance required.  On a cartesian base arrow,
-- every type carries both structures.  This is the precondition for
-- 'Circuit.Net.transpose' to be total.
type Bimonoid arr a = (Copy arr a, Discard arr a, Merge arr a, Zero arr a)

-- | Copy/discard is no longer an ambient assumption on @(->)@.  The
-- exponential slice makes copying an explicit capability: a value of type
-- @!A@ carries a witness, and unmarked @A@ cannot be copied silently.
--
-- The instances below are the concrete copyable types used in the repo and
-- tests.  Adding a new copyable type requires an explicit instance rather
-- than relying on Fox's theorem.

-- | Unit trivially copies and discards.
--
-- >>> copy (() :: ())
-- ((),())
-- >>> discard (() :: ())
-- ()
instance Copy (->) () where
  copy u = (u, u)
  {-# INLINE copy #-}

instance Discard (->) () where
  discard _ = ()
  {-# INLINE discard #-}

-- | Numeric scalars copy and discard pointwise.
--
-- >>> copy (42 :: Int)
-- (42,42)
-- >>> discard (42 :: Int)
-- ()
instance Copy (->) Int where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Int where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) Integer where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Integer where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) Double where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Double where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) Float where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Float where
  discard _ = ()
  {-# INLINE discard #-}

-- | Booleans copy and discard.
--
-- >>> copy True
-- (True,True)
-- >>> discard True
-- ()
instance Copy (->) Bool where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Bool where
  discard _ = ()
  {-# INLINE discard #-}

-- | Products copy and discard as a whole value.
instance Copy (->) (a, b) where
  copy ab = (ab, ab)
  {-# INLINE copy #-}

instance Discard (->) (a, b) where
  discard _ = ()
  {-# INLINE discard #-}

-- | Lists copy and discard as a whole value.
instance Copy (->) [a] where
  copy as = (as, as)
  {-# INLINE copy #-}

instance Discard (->) [a] where
  discard _ = ()
  {-# INLINE discard #-}

-- | Maybe copies and discards as a whole value.
instance Copy (->) (Maybe a) where
  copy m = (m, m)
  {-# INLINE copy #-}

instance Discard (->) (Maybe a) where
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
  type Ob (Dagger arr) a = Ob arr a
  id = Dagger id id
  {-# INLINE id #-}
  Dagger f g . Dagger f' g' = Dagger (f . f') (g' . g)
  {-# INLINE (.) #-}

-- | Dagger of a discrete base is discrete.
instance (Discrete arr) => Discrete (Dagger arr) where
  withOb @a x = withOb @arr @a x

instance (Strength t arr) => Strength t (Dagger arr) where
  strength (Dagger f g) = Dagger (strength f) (strength g)
  {-# INLINE strength #-}
  withStrengthOb ::
    forall a b c r.
    ObDict (Dagger arr) a ->
    ObDict (Dagger arr) b ->
    ObDict (Dagger arr) c ->
    ((Ob (Dagger arr) (t a b), Ob (Dagger arr) (t a c)) => r) ->
    r
  withStrengthOb (dA :: ObDict (Dagger arr) a) (dB :: ObDict (Dagger arr) b) (dC :: ObDict (Dagger arr) c) k =
    withObDict dA $
      withObDict dB $
        withObDict dC $
          withStrengthOb @t @arr (ObDict :: ObDict arr a) (ObDict :: ObDict arr b) (ObDict :: ObDict arr c) k

instance (Traced t arr) => Traced t (Dagger arr) where
  trace (Dagger f g) = Dagger (trace f) (trace g)
  {-# INLINE trace #-}

-- | Forward copy, backward add — the bimonoid self-duality.
instance (Copy arr a, Merge arr a) => Copy (Dagger arr) a where
  copy = Dagger copy plus
  {-# INLINE copy #-}

instance (Discard arr a, Zero arr a) => Discard (Dagger arr) a where
  discard = Dagger discard zero
  {-# INLINE discard #-}

-- | Forward add, backward copy.
instance (Merge arr a, Copy arr a) => Merge (Dagger arr) a where
  plus = Dagger plus copy
  {-# INLINE plus #-}

instance (Zero arr a, Discard arr a) => Zero (Dagger arr) a where
  zero = Dagger zero discard
  {-# INLINE zero #-}

instance (Tensor t arr) => Tensor t (Dagger arr) where
  par (Dagger f g) (Dagger f' g') = Dagger (par f f') (par g g')
  {-# INLINE par #-}
  unitl = Dagger unitl unitl'
  {-# INLINE unitl #-}
  unitl' = Dagger unitl' unitl
  {-# INLINE unitl' #-}
  unitr = Dagger unitr unitr'
  {-# INLINE unitr #-}
  unitr' = Dagger unitr' unitr
  {-# INLINE unitr' #-}

instance (Action t arr) => Action t (Dagger arr) where
  swap = Dagger swap swap
  {-# INLINE swap #-}

-- | Lift monoidal structure through @Dagger@.
instance (Channel t arr) => Channel t (Dagger arr) where
  assoc = Dagger assoc assoc'
  assoc' = Dagger assoc' assoc
  slide = Dagger slide slide
  withTensorOb ::
    forall a b r.
    ObDict (Dagger arr) a ->
    ObDict (Dagger arr) b ->
    ((Ob (Dagger arr) (t a b)) => r) ->
    r
  withTensorOb (dA :: ObDict (Dagger arr) a) (dB :: ObDict (Dagger arr) b) k =
    withObDict dA $
      withObDict dB $
        withTensorOb @t @arr (ObDict :: ObDict arr a) (ObDict :: ObDict arr b) k
