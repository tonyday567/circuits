{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- | Channel structure for the tensors used in traced categories.
--
-- This module collects the braided, cartesian, and cocartesian structure
-- over the standard tensors @(,)@ and 'Either', along with the general
-- 'ambientBy' combinator for threading additional state wires.
--
-- The goal is to keep the core 'Loop' GADT and 'run' mechanism
-- independent of these structural details.
--
-- Note: the monomorphic 'assocL' and 'assocR' helpers below reassociate
-- /leftward/ and /rightward/ respectively — the opposite direction to
-- 'Circuit.Channel.assoc' and 'Circuit.Channel.assoc''. The 'slide'
-- from 'Braided' is the slide @t a (t b c) -> t b (t a c)@; 'swap' here
-- is the symmetric braiding @t a b -> t b a@. They cohere as
-- @slide = assocR '.>' par swap id '.>' assocL@ wherever the 'Tensor'
-- and 'Action' structure is available.
--
-- 'Tensor' / 'Action' are kind-polymorphic.
module Circuit.Tensor
  ( Braided (..),
    ambient,
    ambientBy,
    superpose,

    -- * Channel product on base arrows
    Unit,
    Tensor (..),
    Action (..),

    -- * Cartesian / cocartesian associators
    assocL,
    assocR,
    coassoc,
    coassoc',
  )
where

import Circuit.Category (Category (..), Discrete (..), (.>))
import Circuit.Channel (Strength (..), Traced (..), strengthD)
import Circuit.Discrete (assocD, assocD', braidD)
import Circuit.Layer (run)
import Circuit.Loop (Loop (..))
import Control.Arrow (Kleisli (..))
import Control.Monad (Monad)
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.Profunctor (Profunctor, dimap)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- $setup
-- >> :set -XLambdaCase
-- >> import Circuit.Layer (run)
-- >> import Circuit.Loop (Loop (..))
-- >> import Control.Arrow (Kleisli (..), runKleisli)
-- >> import Data.Functor.Identity (Identity)
-- >> import Prelude hiding (id, (.))

-- ===========================================================================
-- BRAIDING
-- ===========================================================================

-- | A braiding for a bifunctor tensor.
--
-- The slide swaps a wire past a nested pair:
--
-- @
--   t x (t y z)  ->  t y (t x z)
-- @
--
-- For @(,)@ this is the cartesian slide.  For @Either@ it is the
-- coproduct slide.  Both are derived from the associator and swap.
class (Bifunctor t) => Braided t where
  slide :: t x (t y z) -> t y (t x z)

-- | Cartesian slide: @(x, (y, z)) -> (y, (x, z))@.
instance Braided (,) where
  slide ~(x, ~(y, z)) = (y, (x, z))

-- | Coproduct slide.
--
-- .> slide (Left "hi" :: Either String (Either Int Bool))
-- Right (Left "hi")
instance Braided Either where
  slide (Left x) = Right (Left x)
  slide (Right (Left y)) = Left y
  slide (Right (Right z)) = Right (Right z)

-- | Thread a state wire through a circuit using the canonical slide.
--
-- This is 'ambientBy' with the slide supplied by the 'Braided' instance.
ambient ::
  (Braided t, Strength t (->)) =>
  Loop t (->) a b ->
  Loop t (->) (t s a) (t s b)
ambient = ambientBy slide

-- ===========================================================================
-- CARTESIAN STRUCTURE ((,))
-- ===========================================================================

-- | Leftward associator: @(a, (b, c)) -> ((a, b), c)@.
assocL :: (a, (b, c)) -> ((a, b), c)
assocL ~(a, ~(b, c)) = ((a, b), c)

-- | Rightward associator: @((a, b), c) -> (a, (b, c))@.
assocR :: ((a, b), c) -> (a, (b, c))
assocR ~(~(a, b), c) = (a, (b, c))

-- | Introduce a state wire alongside a payload.
--
-- Given an initial state and a payload value, produce a paired value
-- suitable for feeding into a circuit threaded with 'ambientBy'.
seed :: s -> a -> (s, a)
seed s a = (s, a)

-- | Move a value from the payload into the state wire.
--
-- @absorb f = first (uncurry f) . assocL@
absorb :: (t -> s -> s') -> (s, (t, b)) -> (s', b)
absorb f (s, (t, b)) = (f t s, b)

-- | Move a value from the state wire into the payload.
--
-- @release f = assocR . first f@
release :: (s -> (s', t)) -> (s, b) -> (s', (t, b))
release f (s, b) = let (s', t) = f s in (s', (t, b))

-- ===========================================================================
-- COCARTESIAN STRUCTURE (Either)
-- ===========================================================================

-- | Coassociator for sums.
--
-- .> coassoc (Left 1 :: Either Int (Either Bool Char))
-- Left (Left 1)
coassoc :: Either a (Either b c) -> Either (Either a b) c
coassoc (Left a) = Left (Left a)
coassoc (Right (Left b)) = Left (Right b)
coassoc (Right (Right c)) = Right c

-- | Inverse coassociator.
--
-- .> coassoc' (Left (Left 1) :: Either (Either Int Bool) Char)
-- Left 1
coassoc' :: Either (Either a b) c -> Either a (Either b c)
coassoc' (Left (Left a)) = Left a
coassoc' (Left (Right b)) = Right (Left b)
coassoc' (Right c) = Right (Right c)

-- | Tag a state value onto whichever branch of the sum is active.
--
-- .> coseed "st" (Left 42 :: Either Int Char)
-- Left ("st",42)
coseed :: s -> Either a b -> Either (s, a) (s, b)
coseed s = bimap (s,) (s,)

-- | If the left branch is taken, move a value from the payload into the state wire.
--
-- .> coabsorbL (+) (Left (10, (3, 7)) :: Either (Int, (Int, Int)) Bool)
-- Left (13,7)
coabsorbL :: (t -> s -> s') -> Either (s, (t, a)) b -> Either (s', a) b
coabsorbL f (Left (s, (t, a))) = Left (f t s, a)
coabsorbL _ (Right b) = Right b

-- | If the right branch is taken, move a value from the payload into the state wire.
--
-- .> coabsorbR (+) (Right (10, (3, 7)) :: Either Bool (Int, (Int, Int)))
-- Right (13,7)
coabsorbR :: (t -> s -> s') -> Either a (s, (t, b)) -> Either a (s', b)
coabsorbR f (Right (s, (t, b))) = Right (f t s, b)
coabsorbR _ (Left a) = Left a

-- | If the left branch is taken, move a value from the state wire into the payload.
--
-- .> coreleaseL (\s -> (s+1, s*2)) (Left (5, 99) :: Either (Int, Int) Char)
-- Left (6,(10,99))
coreleaseL :: (s -> (s', t)) -> Either (s, a) b -> Either (s', (t, a)) b
coreleaseL f (Left (s, a)) = let (s', t) = f s in Left (s', (t, a))
coreleaseL _ (Right b) = Right b

-- | If the right branch is taken, move a value from the state wire into the payload.
--
-- .> coreleaseR (\s -> (s+1, s*2)) (Right (5, 99) :: Either Char (Int, Int))
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
-- without the circuit having to mention it. The state wire is slid
-- past the feedback channel so it travels "ambiently".
--
-- The @slide@ function swaps the state wire past the feedback channel:
-- @t x (t s a) -> t s (t x a)@. For @(,)@, this is
-- @\(x, (s, a)) -> (s, (x, a))@.
--
-- .> import Circuit.Layer (run)
-- .> import Circuit.Loop (Loop(..))
-- .> let slide (x, (s, a)) = (s, (x, a))
-- .> run (ambientBy slide (Lift (+1) :: Loop (,) (->) Int Int)) ("st", 5)
-- ("st",6)
--
-- .> let step (xs, ()) = (0 : xs, take 3 xs)
-- .> run (ambientBy slide (Knot step)) ("st", ())
-- ("st",[0,0,0])
ambientBy ::
  (Strength t (->)) =>
  (forall x y z. t x (t y z) -> t y (t x z)) ->
  Loop t (->) a b ->
  Loop t (->) (t s a) (t s b)
ambientBy _br (Lift f) = Lift (strength f)
ambientBy br (Knot k) = Knot (dimap br br (strength k))

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
-- object. This is the planar fragment: 'Tensor' only provides the
-- associator and unitors, not a braiding.
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

-- | Cartesian tensor on @Kleisli@ (effectful sequential product).
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
-- .> par ((+1) :: Int -> Int) ((*2) :: Int -> Int) (Left 3 :: Either Int Int)
-- Left 4
--
-- .> par ((+1) :: Int -> Int) ((*2) :: Int -> Int) (Right 3 :: Either Int Int)
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
-- .> swap (Left 3 :: Either Int Int) :: Either Int Int
-- Right 3
instance Action Either (->) where
  swap = \case
    Left a -> Right a
    Right b -> Left b
  {-# INLINE swap #-}

-- | Coproduct tensor action on @Kleisli@ @m@.
--
-- .> import Control.Arrow (Kleisli(..), runKleisli)
-- .> let f = Kleisli (\n -> pure (n + 1)) :: Kleisli IO Int Int
-- .> let g = Kleisli (\n -> pure (n * 2)) :: Kleisli IO Int Int
-- .> runKleisli (par f g) (Left 3 :: Either Int Int)
-- Left 4
-- .> runKleisli (par f g) (Right 3 :: Either Int Int)
-- Right 6
instance (Monad m) => Tensor Either (Kleisli m) where
  par (Kleisli f) (Kleisli g) =
    Kleisli $ \case
      Left a -> Left <$> f a
      Right c -> Right <$> g c
  {-# INLINE par #-}
  unitl = Kleisli $ either absurd pure
  {-# INLINE unitl #-}
  unitl' = Kleisli $ pure . Right
  {-# INLINE unitl' #-}
  unitr = Kleisli $ either pure absurd
  {-# INLINE unitr #-}
  unitr' = Kleisli $ pure . Left
  {-# INLINE unitr' #-}

-- | Coproduct symmetry on @Kleisli@ @m@.
instance (Monad m) => Action Either (Kleisli m) where
  swap = Kleisli $ pure . swap
  {-# INLINE swap #-}

-- | Lift 'Tensor'/'Action' through 'Loop'.
--
-- This is the single lawful instance: it evaluates each 'Loop' branch
-- independently with 'run' and combines the results using the base arrow's
-- tensor. It is correct and black-hole-free, but does not fuse feedback
-- loops. For the fused superposition of two 'Knot's, use 'superpose'.
instance (Tensor t arr, Traced t' arr, Discrete arr) => Tensor t (Loop t' arr) where
  par :: forall a b c d. Loop t' arr a b -> Loop t' arr c d -> Loop t' arr (t a c) (t b d)
  par f g =
    Lift $
      withOb @arr @a $
        withOb @arr @b $
          withOb @arr @c $
            withOb @arr @d $
              par (run f) (run g)
  unitl = Lift unitl
  unitl' = Lift unitl'
  unitr = Lift unitr
  unitr' = Lift unitr'

instance (Action t arr, Traced t' arr, Discrete arr) => Action t (Loop t' arr) where
  swap = Lift swap

-- | Fused parallel composition for 'Loop' when the feedback tensor matches.
--
-- Two 'Knot's in parallel superpose into one 'Knot' over a paired channel,
-- satisfying the superposing axiom of traced monoidal categories:
--
-- @superpose (trace f) (trace g) = trace (pre . par f g . post)@
--
-- where @pre@ and @post@ rearrange the paired channel via associators
-- and braiding. This preserves sharing for recursive circuits; the lawful
-- 'Tensor' instance falls back to independent evaluation.
--
-- .> let k1 = Circuit.Loop.Knot (\(ns, _) -> (1 : ns, take 3 ns)) :: Circuit.Loop.Loop (,) (->) [Int] [Int]
-- .> let k2 = Circuit.Loop.Knot (\(ns, _) -> (2 : ns, take 3 ns))
-- .> Circuit.Layer.run (superpose k1 k2) ([], [])
-- ([1,1,1],[2,2,2])
--
-- The same fusion works for @Kleisli@, preserving sharing across the
-- recursive channels under @MonadFix@.
--
-- .> let k1 = Circuit.Loop.Knot (Kleisli $ \(ns, _) -> pure (1 : ns, take 3 ns)) :: Circuit.Loop.Loop (,) (Kleisli Identity) [Int] [Int]
-- .> let k2 = Circuit.Loop.Knot (Kleisli $ \(ns, _) -> pure (2 : ns, take 3 ns))
-- .> runKleisli (Circuit.Layer.run (superpose k1 k2)) ([], [])
-- Identity ([1,1,1],[2,2,2])
superpose ::
  forall t arr a b c d.
  (Tensor t arr, Strength t arr, Discrete arr) =>
  Loop t arr a b ->
  Loop t arr c d ->
  Loop t arr (t a c) (t b d)
superpose x y = case (x, y) of
  (Knot @_ @s @_ @_ @_ f, Knot @_ @s1 @_ @_ @_ g) ->
    withOb @arr @(t s s1) $
      withOb @arr @(t (t s s1) (t a c)) $
        withOb @arr @(t (t s s1) (t b d)) $
          Knot $ pre .>> par f g .>> post
  (Knot @_ @s @_ @_ @_ f, Lift g) ->
    withOb @arr @(t s (t a c)) $
      withOb @arr @(t s (t b d)) $
        Knot $ assoc'_ .>> par f g .>> assoc_
  (Lift f, Knot @_ @s @_ @_ @_ g) ->
    withOb @arr @(t s (t a c)) $
      withOb @arr @(t s (t b d)) $
        Knot $ braid_ .>> par f g .>> braid_
  (Lift f, Lift g) -> Lift (par f g)
  where
    (.>>) :: forall x y z. arr x y -> arr y z -> arr x z
    (.>>) f' g' = withOb @arr @x $ withOb @arr @y $ withOb @arr @z $ g' . f'

    assoc_ :: forall x y z. arr (t (t x y) z) (t x (t y z))
    assoc_ = assocD

    assoc'_ :: forall x y z. arr (t x (t y z)) (t (t x y) z)
    assoc'_ = assocD'

    braid_ :: forall x y z. arr (t x (t y z)) (t y (t x z))
    braid_ = braidD

    pre, post :: forall u v w x. arr (t (t u v) (t w x)) (t (t u w) (t v x))
    pre = assoc_ .>> strengthD braid_ .>> assoc'_
    post = assoc_ .>> strengthD braid_ .>> assoc'_
