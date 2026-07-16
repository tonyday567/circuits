{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Monoidal structure for the tensors used in traced categories.
--
-- This module collects the braided, cartesian, and cocartesian structure
-- over the standard tensors @(,)@ and 'Either', along with the general
-- 'ambientBy' combinator for threading additional state wires.
--
-- The goal is to keep the core 'Trace' GADT and 'run' mechanism
-- independent of these structural details.
--
-- 'Tensor' / 'Action' are kind-polymorphic so @(+)@ can be a tensor for
-- @MatH@ alongside @Either@ for @Mat@ / @(->)@.
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
    Unit,
    Tensor (..),
    Action (..),
  )
where

import Circuit.Classes (Category (..), Discrete (..), (>>>))
import Circuit.Layer (run)
import Circuit.Monoidal.Category qualified as MC
import Circuit.Trace (Trace (..), Traced (..), untraceD)
import Control.Arrow (Kleisli (..))
import Control.Monad (Monad)
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.Profunctor (Profunctor, dimap)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Trace (Trace (..))
-- >>> import Prelude hiding (id, (.))

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
  braid ~(x, ~(y, z)) = (y, (x, z))

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
  (Braided t, Traced t (->)) =>
  Trace t (->) a b ->
  Trace t (->) (t s a) (t s b)
ambient = ambientBy braid

-- ===========================================================================
-- CARTESIAN STRUCTURE ((,))
-- ===========================================================================

-- | Associator: @(a, (b, c)) -> ((a, b), c)@.
assoc :: (a, (b, c)) -> ((a, b), c)
assoc ~(a, ~(b, c)) = ((a, b), c)

-- | Inverse associator: @((a, b), c) -> (a, (b, c))@.
assoc' :: ((a, b), c) -> (a, (b, c))
assoc' ~(~(a, b), c) = (a, (b, c))

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
-- @\(x, (s, a)) -> (s, (x, a))@.
--
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Trace (Trace(..))
-- >>> let braid (x, (s, a)) = (s, (x, a))
-- >>> run (ambientBy braid (Arr (+1) :: Trace (,) (->) Int Int)) ("st", 5)
-- ("st",6)
--
-- >>> let step (xs, ()) = (0 : xs, take 3 xs)
-- >>> run (ambientBy braid (Knot step)) ("st", ())
-- ("st",[0,0,0])
ambientBy ::
  (Traced t (->)) =>
  (forall x y z. t x (t y z) -> t y (t x z)) ->
  Trace t (->) a b ->
  Trace t (->) (t s a) (t s b)
ambientBy _br (Arr f) = Arr (untrace f)
ambientBy br (Knot k) = Knot (dimap br br (untrace k))

-- ===========================================================================
-- Tensor / Action — tensor action on morphisms
-- ===========================================================================

-- | The unit object for a tensor @t@.
--
-- @t@ is an object-level bifunctor (@Either@, @(,)@, type-level @(+)@, …)
-- with kind @k -> k -> k@, not a morphism tensor.
type family Unit (t :: k -> k -> k) :: k

-- | The tensor action of @t@ on a category @arr@, without braiding.
--
-- 'par' is the tensor product of morphisms (parallel composition on
-- disjoint wires). 'unitl' and 'unitr' witness that the tensor has a unit
-- object. This is the planar fragment: consumers constrained to 'Tensor'
-- cannot invoke a symmetry, even if the underlying value still contains
-- one.
--
-- Kind-polymorphic: @t@ and @arr@ share object kind (inferred via PolyKinds).
class (Category arr) => Tensor t arr where
  -- | Parallel composition: run two arrows on disjoint wires.
  --
  -- >>> par ((+1) :: Int -> Int) ((*2) :: Int -> Int) (3, 4)
  -- (4,8)
  par :: arr a b -> arr c d -> arr (t a c) (t b d)

  -- | Left unitor: @I ⊗ a -> a@.
  unitl :: arr (t (Unit t) a) a

  -- | Inverse left unitor: @a -> I ⊗ a@.
  unitl' :: arr a (t (Unit t) a)

  -- | Right unitor: @a ⊗ I -> a@.
  unitr :: arr (t a (Unit t)) a

  -- | Inverse right unitor: @a -> a ⊗ I@.
  unitr' :: arr a (t a (Unit t))

-- | The action of a tensor @t@ on a category @arr@, extended with a
-- symmetric braiding.
--
-- This is the self-action of a symmetric monoidal category: @t@ acts on
-- @arr@ by taking morphisms to morphisms over paired objects, and 'swap'
-- provides the symmetry.
class (Tensor t arr) => Action t arr where
  -- | Symmetric braiding.
  --
  -- >>> swap (3, 4) :: (Int, Int)
  -- (4,3)
  swap :: arr (t a b) (t b a)

type instance Unit (,) = ()

-- | Cartesian tensor action on functions.
--
-- Laws: 'unitl' = 'snd', 'unitl'' = @((),)@, 'unitr' = 'fst', 'unitr'' = @(,) ()@.
instance Tensor (,) (->) where
  par f g (a, c) = (f a, g c)
  {-# INLINE par #-}
  unitl ~((), a) = a
  {-# INLINE unitl #-}
  unitl' a = ((), a)
  {-# INLINE unitl' #-}
  unitr ~(a, ()) = a
  {-# INLINE unitr #-}
  unitr' a = (a, ())
  {-# INLINE unitr' #-}

-- | Cartesian symmetry on functions.
instance Action (,) (->) where
  swap (a, b) = (b, a)
  {-# INLINE swap #-}

-- | Cartesian tensor on 'Kleisli' (effectful sequential product).
instance (Monad m) => Tensor (,) (Kleisli m) where
  par (Kleisli f) (Kleisli g) =
    Kleisli $ \(a, c) -> do
      b <- f a
      d <- g c
      pure (b, d)
  {-# INLINE par #-}
  unitl = Kleisli $ \((), a) -> pure a
  {-# INLINE unitl #-}
  unitl' = Kleisli $ \a -> pure ((), a)
  {-# INLINE unitl' #-}
  unitr = Kleisli $ \(a, ()) -> pure a
  {-# INLINE unitr #-}
  unitr' = Kleisli $ \a -> pure (a, ())
  {-# INLINE unitr' #-}

instance (Monad m) => Action (,) (Kleisli m) where
  swap = Kleisli $ \(a, b) -> pure (b, a)
  {-# INLINE swap #-}

type instance Unit Either = Void

-- | Coproduct tensor action on functions.
--
-- >>> par ((+1) :: Int -> Int) ((*2) :: Int -> Int) (Left 3 :: Either Int Int)
-- Left 4
--
-- >>> par ((+1) :: Int -> Int) ((*2) :: Int -> Int) (Right 3 :: Either Int Int)
-- Right 6
instance Tensor Either (->) where
  par = bimap
  {-# INLINE par #-}
  unitl = either absurd id
  {-# INLINE unitl #-}
  unitl' = Right
  {-# INLINE unitl' #-}
  unitr = either id absurd
  {-# INLINE unitr #-}
  unitr' = Left
  {-# INLINE unitr' #-}

-- | Coproduct symmetry on functions.
--
-- >>> swap (Left 3 :: Either Int Int) :: Either Int Int
-- Right 3
instance Action Either (->) where
  swap = \case
    Left a -> Right a
    Right b -> Left b
  {-# INLINE swap #-}

-- | Lift 'Tensor'/'Action' through 'Trace' when the feedback tensor matches.
--
-- Two 'Knot's in parallel superpose into one 'Knot' over a paired channel,
-- satisfying the superposing axiom of traced monoidal categories:
--
-- @par (trace f) (trace g) = trace (pre . par f g . post)@
--
-- where @pre@ and @post@ rearrange the paired channel via associators
-- and braiding.
--
-- [Lazy patterns absorbed] For the @(,)@ tensor, the paired channel is a
-- tuple. The lazy-knot 'trace' diverges if any stage on the recursive path
-- forces the channel before emitting its result constructor. All structure
-- maps on the @(,)@ route are irrefutable, and 'untrace' re-emits the
-- channel as a manifest pair of projections, so /top-level strict tuple
-- patterns in user bodies are absorbed at the fusion boundary/ and do not
-- cause a black hole. Bodies that genuinely force the channel's contents
-- before producing output still diverge correctly, and 'cellIO' remains the
-- right tool for strict accumulators.
--
-- [Instance selection] The fused instance is selected when the action tensor
-- equals the feedback tensor. Code polymorphic in the tensor resolves the
-- fallback, so fusion depends on where the 'Action' constraint is discharged.
--
-- >>> let k1 = Circuit.Trace.Knot (\(ns, _) -> (1 : ns, take 3 ns)) :: Circuit.Trace.Trace (,) (->) [Int] [Int]
-- >>> let k2 = Circuit.Trace.Knot (\(ns, _) -> (2 : ns, take 3 ns))
-- >>> Circuit.Layer.run (par k1 k2) ([], [])
-- ([1,1,1],[2,2,2])
-- >>> case par k1 k2 :: Trace (,) (->) ([Int], [Int]) ([Int], [Int]) of Knot _ -> "fused"; Arr _ -> "melted"
-- "fused"
instance {-# OVERLAPPING #-} (Tensor t (->), Traced t (->), MC.Monoidal t (->)) => Tensor t (Trace t (->)) where
  par (Knot f) (Knot g) = Knot $ pre >>> par f g >>> post
    where
      pre = MC.assoc >>> untrace MC.braid >>> MC.assoc'
      post = MC.assoc >>> untrace MC.braid >>> MC.assoc'
  par (Knot f) (Arr g) = Knot (MC.assoc' >>> par f g >>> MC.assoc)
  par (Arr f) (Knot g) = Knot (MC.braid >>> par f g >>> MC.braid)
  par (Arr f) (Arr g) = Arr (par f g)
  unitl = Arr unitl
  unitl' = Arr unitl'
  unitr = Arr unitr
  unitr' = Arr unitr'

instance {-# OVERLAPPING #-} (Action t (->), Traced t (->), MC.Monoidal t (->)) => Action t (Trace t (->)) where
  swap = Arr swap

instance
  {-# OVERLAPPING #-}
  (Monad m, Tensor t (Kleisli m), Traced t (Kleisli m), MC.Monoidal t (Kleisli m)) =>
  Tensor t (Trace t (Kleisli m))
  where
  par (Knot f) (Knot g) = Knot $ pre >>> par f g >>> post
    where
      pre = MC.assoc >>> untrace MC.braid >>> MC.assoc'
      post = MC.assoc >>> untrace MC.braid >>> MC.assoc'
  par (Knot f) (Arr g) = Knot (MC.assoc' >>> par f g >>> MC.assoc)
  par (Arr f) (Knot g) = Knot (MC.braid >>> par f g >>> MC.braid)
  par (Arr f) (Arr g) = Arr (par f g)
  unitl = Arr unitl
  unitl' = Arr unitl'
  unitr = Arr unitr
  unitr' = Arr unitr'

instance
  {-# OVERLAPPING #-}
  (Monad m, Action t (Kleisli m), Traced t (Kleisli m), MC.Monoidal t (Kleisli m)) =>
  Action t (Trace t (Kleisli m))
  where
  swap = Arr swap

-- | Lift 'Tensor'/'Action' through 'Trace' when tensors differ.
--
-- Falls back to independent evaluation — 'trace' is called once per
-- branch.  Correct and black-hole-free, but doesn't fuse the loops.
instance {-# OVERLAPPABLE #-} (Tensor t (->), Traced t' (->)) => Tensor t (Trace t' (->)) where
  par f g = Arr (par (run f) (run g))
  unitl = Arr unitl
  unitl' = Arr unitl'
  unitr = Arr unitr
  unitr' = Arr unitr'

instance {-# OVERLAPPABLE #-} (Action t (->), Traced t' (->)) => Action t (Trace t' (->)) where
  swap = Arr swap
