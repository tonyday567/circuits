{-# LANGUAGE CPP #-}

-- | Monoidal structure for the tensors used in traced categories.
--
-- This module collects the braided, cartesian, and cocartesian structure
-- over the standard tensors @(,)@ and 'Either', along with the general
-- 'ambientBy' combinator for threading additional state wires.
--
-- The goal is to keep the core 'Circuit' GADT and 'reify' mechanism
-- independent of these structural details.
module Circuit.Monoidal
  ( Braided (..),
    ambient,
    assoc,
    assoc',
    seed,
    absorb,
    release,
    coassoc,
    coassoc',
    coseed,
    coabsorbL,
    coabsorbR,
    coreleaseL,
    coreleaseR,
    ambientBy,

    -- * Monoidal product on base arrows
    MonoidalP (..),
  )
where

#ifdef __GLASGOW_HASKELL__
import Control.Category (Category)
import Data.Profunctor (Profunctor, dimap)
import Data.Bifunctor (Bifunctor (..))
#else
import Circuit.Classes (Profunctor, Bifunctor (..), Category)
#endif

import Circuit.Circuit (Circuit (..), reify)
import Circuit.Traced (Trace (..))

-- ===========================================================================
-- BRAIDING
-- ===========================================================================

-- | A symmetric braiding for a bifunctor tensor.
--
-- The braid swaps a wire past a nested pair:
--
-- @
--   t x (t y z)  ->  t y (t x z)
-- @
--
-- For @(,)@ this is the cartesian slide.  For @Either@ it is the
-- coproduct slide.  Both are derived from the associator and swap.
class (Bifunctor t) => Braided t where
  braid :: t x (t y z) -> t y (t x z)

-- | Cartesian slide: @(x, (y, z)) -> (y, (x, z))@.
instance Braided (,) where
  braid (x, (y, z)) = (y, (x, z))

-- | Coproduct slide.
--
-- >>> braid (Left "hi" :: Either String (Either Int Bool))
-- Right (Left "hi")
instance Braided Either where
  braid (Left x) = Right (Left x)
  braid (Right (Left y)) = Left y
  braid (Right (Right z)) = Right (Right z)

-- | Thread a state wire through a circuit using the canonical braid.
--
-- This is 'ambientBy' with the braid supplied by the 'Braided' instance.
ambient ::
  (Category arr, Profunctor arr, Trace arr t, Braided t) =>
  Circuit arr t a b -> Circuit arr t (t s a) (t s b)
ambient = ambientBy braid

-- ===========================================================================
-- CARTESIAN STRUCTURE ((,))
-- ===========================================================================

-- | Associator: @(a, (b, c)) -> ((a, b), c)@.
assoc :: (a, (b, c)) -> ((a, b), c)
assoc (a, (b, c)) = ((a, b), c)

-- | Inverse associator: @((a, b), c) -> (a, (b, c))@.
assoc' :: ((a, b), c) -> (a, (b, c))
assoc' ((a, b), c) = (a, (b, c))

-- | Introduce a state wire alongside a payload.
--
-- Given an initial state and a payload value, produce a paired value
-- suitable for feeding into a circuit threaded with 'ambientBy'.
seed :: s -> a -> (s, a)
seed s a = (s, a)

-- | Move a value from the payload into the state wire.
--
-- @absorb f = first (uncurry f) . assoc@
absorb :: (t -> s -> s') -> (s, (t, b)) -> (s', b)
absorb f (s, (t, b)) = (f t s, b)

-- | Move a value from the state wire into the payload.
--
-- @release f = assoc' . first f@
release :: (s -> (s', t)) -> (s, b) -> (s', (t, b))
release f (s, b) = let (s', t) = f s in (s', (t, b))

-- ===========================================================================
-- COCARTESIAN STRUCTURE (Either)
-- ===========================================================================

-- | Coassociator for sums.
--
-- >>> coassoc (Left 1 :: Either Int (Either Bool Char))
-- Left (Left 1)
coassoc :: Either a (Either b c) -> Either (Either a b) c
coassoc (Left a) = Left (Left a)
coassoc (Right (Left b)) = Left (Right b)
coassoc (Right (Right c)) = Right c

-- | Inverse coassociator.
--
-- >>> coassoc' (Left (Left 1) :: Either (Either Int Bool) Char)
-- Left 1
coassoc' :: Either (Either a b) c -> Either a (Either b c)
coassoc' (Left (Left a)) = Left a
coassoc' (Left (Right b)) = Right (Left b)
coassoc' (Right c) = Right (Right c)

-- | Tag a state value onto whichever branch of the sum is active.
--
-- >>> coseed "st" (Left 42 :: Either Int Char)
-- Left ("st",42)
coseed :: s -> Either a b -> Either (s, a) (s, b)
coseed s = bimap (s,) (s,)

-- | If the left branch is taken, move a value from the payload into the state wire.
--
-- >>> coabsorbL (+) (Left (10, (3, 'x')) :: Either (Int, (Int, Char)) Bool)
-- Left (13,'x')
coabsorbL :: (t -> s -> s') -> Either (s, (t, a)) b -> Either (s', a) b
coabsorbL f (Left (s, (t, a))) = Left (f t s, a)
coabsorbL _ (Right b) = Right b

-- | If the right branch is taken, move a value from the payload into the state wire.
--
-- >>> coabsorbR (+) (Right (10, (3, 'x')) :: Either Bool (Int, (Int, Char)))
-- Right (13,'x')
coabsorbR :: (t -> s -> s') -> Either a (s, (t, b)) -> Either a (s', b)
coabsorbR f (Right (s, (t, b))) = Right (f t s, b)
coabsorbR _ (Left a) = Left a

-- | If the left branch is taken, move a value from the state wire into the payload.
--
-- >>> coreleaseL (\s -> (s+1, s*2)) (Left (5, 99) :: Either (Int, Int) Char)
-- Left (6,(10,99))
coreleaseL :: (s -> (s', t)) -> Either (s, a) b -> Either (s', (t, a)) b
coreleaseL f (Left (s, a)) = let (s', t) = f s in Left (s', (t, a))
coreleaseL _ (Right b) = Right b

-- | If the right branch is taken, move a value from the state wire into the payload.
--
-- >>> coreleaseR (\s -> (s+1, s*2)) (Right (5, 99) :: Either Char (Int, Int))
-- Right (6,(10,99))
coreleaseR :: (s -> (s', t)) -> Either a (s, b) -> Either a (s', (t, b))
coreleaseR f (Right (s, b)) = let (s', t) = f s in Right (s', (t, b))
coreleaseR _ (Left a) = Left a

-- ===========================================================================
-- GENERAL AMBIENT STATE THREADING
-- ===========================================================================

-- | Thread a state wire through a Circuit.
--
-- 'ambientBy' threads an additional state component alongside a circuit
-- without the circuit having to mention it. The state wire is braided
-- past the feedback channel so it travels "ambiently".
--
-- The @braid@ function swaps the state wire past the feedback channel:
-- @t x (t s a) -> t s (t x a)@. For @(,)@, this is
-- @\\(x, (s, a)) -> (s, (x, a))@.
--
-- >>> import Circuit.Circuit (Circuit(..), reify)
-- >>> let braid (x, (s, a)) = (s, (x, a))
-- >>> Circuit.Circuit.reify (ambientBy braid (Lift (+1) :: Circuit (->) (,) Int Int)) ("st", 5)
-- ("st",6)
--
-- >>> let step (xs, ()) = (0 : xs, take 3 xs)
-- >>> Circuit.Circuit.reify (ambientBy braid (Knot (Lift step))) ("st", ())
-- ("st",[0,0,0])
ambientBy ::
  (Category arr, Profunctor arr, Trace arr t) =>
  (forall x y z. t x (t y z) -> t y (t x z)) ->
  Circuit arr t a b ->
  Circuit arr t (t s a) (t s b)
ambientBy _br (Lift f) = Lift (untrace f)
ambientBy br (Compose f g) = Compose (ambientBy br f) (ambientBy br g)
ambientBy br (Knot k) = Knot (Lift (dimap br br (untrace (reify k))))

-- ===========================================================================
-- MonoidalP — parallel composition for product categories
-- ===========================================================================

-- | A monoidal product on base arrows.
--
-- 'parA' composes two arrows in parallel (disjoint wires — no interaction,
-- so no 'Additive' constraint).  'swapA' is the symmetric braiding.
class Category arr => MonoidalP arr where
  -- | Parallel composition: run two arrows on disjoint wires.
  --
  -- >>> parA ((+1) :: Int -> Int) ((*2) :: Int -> Int) (3, 4)
  -- (4,8)
  parA :: arr a b -> arr c d -> arr (a, c) (b, d)

  -- | Symmetric braiding.
  --
  -- >>> swapA (3, 4) :: (Int, Int)
  -- (4,3)
  swapA :: arr (a, b) (b, a)

instance MonoidalP (->) where
  parA f g (a, c) = (f a, g c)
  {-# INLINE parA #-}
  swapA (a, b) = (b, a)
  {-# INLINE swapA #-}
