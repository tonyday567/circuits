{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- | Tensor action and braiding for traced categories.
--
-- This module collects the cartesian and cocartesian structure over the
-- standard tensors @(,)@ and 'Either', plus the tensor action on morphisms.
--
-- The goal is to keep the core 'Loop' GADT and 'run' mechanism
-- independent of these structural details.
--
-- Note: the monomorphic 'assocL' and 'assocR' helpers below reassociate
-- /leftward/ and /rightward/ respectively — the opposite direction to
-- 'Circuit.Channel.assoc' and 'Circuit.Channel.assoc''.
--
-- 'Tensor' / 'Action' are kind-polymorphic.
module Circuit.Tensor
  ( -- * Fused parallel composition
    superpose,

    -- * Schedule bias (also used by additive disjunction)
    Bias (..),

    -- * Channel product on base arrows
    Unit,
    Tensor (..),
    Action (..),

    -- * Cartesian / cocartesian associators
    assocL,
    assocR,
    coassoc,
    coassoc',
    coseed,
    coabsorbL,
    coabsorbR,
    coreleaseL,
    coreleaseR,
  )
where

import Circuit.Category (Category (..), K (..), (.>))
import Circuit.Channel (Strength (..), Traced (..))
import Circuit.Channel qualified as Ch
import Circuit.Layer (run)
import Circuit.Loop (Loop (..))
import Control.Monad (Monad)
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.These (These (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XLambdaCase
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Loop (Loop (..))
-- >>> import Circuit.Category (K (..), runK)
-- >>> import Data.Functor.Identity (Identity)
-- >>> import Prelude hiding (id, (.))

-- ===========================================================================
-- SCHEDULE BIAS
-- ===========================================================================

-- | Bias for ordered choice in scheduling and additive disjunction.
--
-- 'LeftFirst' and 'RightFirst' are used by shared-medium fusion in
-- "Circuit.Shared" and by additive disjunction in "Circuit.Ends".
data Bias = LeftFirst | RightFirst
  deriving (Eq, Show)

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
-- >>> coabsorbL (+) (Left (10, (3, 7)) :: Either (Int, (Int, Int)) Bool)
-- Left (13,7)
coabsorbL :: (t -> s -> s') -> Either (s, (t, a)) b -> Either (s', a) b
coabsorbL f (Left (s, (t, a))) = Left (f t s, a)
coabsorbL _ (Right b) = Right b

-- | If the right branch is taken, move a value from the payload into the state wire.
--
-- >>> coabsorbR (+) (Right (10, (3, 7)) :: Either Bool (Int, (Int, Int)))
-- Right (13,7)
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

-- | Cartesian tensor on @K@ (effectful sequential product).
instance (Monad m) => Tensor (,) (K m) where
  par (K f) (K g) =
    K $ \(a, c) -> do
      b <- f a
      d <- g c
      pure (b, d)
  {-# INLINE par #-}
  unitl = K $ \((), a) -> pure a
  {-# INLINE unitl #-}
  unitl' = K $ \a -> pure ((), a)
  {-# INLINE unitl' #-}
  unitr = K $ \(a, ()) -> pure a
  {-# INLINE unitr #-}
  unitr' = K $ \a -> pure (a, ())
  {-# INLINE unitr' #-}

instance (Monad m) => Action (,) (K m) where
  swap = K $ \(a, b) -> pure (b, a)
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

-- | Coproduct tensor action on @K@ @m@.
--
-- >>> import Circuit.Category (K(..), runK)
-- >>> let f = K (\n -> pure (n + 1)) :: K IO Int Int
-- >>> let g = K (\n -> pure (n * 2)) :: K IO Int Int
-- >>> runK (par f g) (Left 3 :: Either Int Int)
-- Left 4
-- >>> runK (par f g) (Right 3 :: Either Int Int)
-- Right 6
instance (Monad m) => Tensor Either (K m) where
  par (K f) (K g) =
    K $ \case
      Left a -> Left <$> f a
      Right c -> Right <$> g c
  {-# INLINE par #-}
  unitl = K $ either absurd pure
  {-# INLINE unitl #-}
  unitl' = K $ pure . Right
  {-# INLINE unitl' #-}
  unitr = K $ either pure absurd
  {-# INLINE unitr #-}
  unitr' = K $ pure . Left
  {-# INLINE unitr' #-}

-- | Coproduct symmetry on @K@ @m@.
instance (Monad m) => Action Either (K m) where
  swap = K $ pure . swap
  {-# INLINE swap #-}

type instance Unit These = Void

-- | Inclusive tensor action on functions.
--
-- Laws: 'unitl' eliminates a vacuous 'This', 'unitl'' injects with 'That';
-- 'unitr' eliminates a vacuous 'That', 'unitr'' injects with 'This'.
instance Tensor These (->) where
  par = bimap
  {-# INLINE par #-}
  unitl (That a) = a
  unitl (This v) = absurd v
  unitl (These v _) = absurd v
  {-# INLINE unitl #-}
  unitl' = That
  {-# INLINE unitl' #-}
  unitr (This a) = a
  unitr (That v) = absurd v
  unitr (These _ v) = absurd v
  {-# INLINE unitr #-}
  unitr' = This
  {-# INLINE unitr' #-}

-- | Inclusive symmetry on functions.
instance Action These (->) where
  swap (This a) = That a
  swap (That b) = This b
  swap (These a b) = These b a
  {-# INLINE swap #-}

-- | Inclusive tensor action on @K@ @m@.
instance (Monad m) => Tensor These (K m) where
  par (K f) (K g) =
    K $ \case
      This a -> This <$> f a
      That c -> That <$> g c
      These a c -> These <$> f a <*> g c
  {-# INLINE par #-}
  unitl = K $ \case
    That a -> pure a
    This v -> absurd v
    These v _ -> absurd v
  {-# INLINE unitl #-}
  unitl' = K $ pure . That
  {-# INLINE unitl' #-}
  unitr = K $ \case
    This a -> pure a
    That v -> absurd v
    These _ v -> absurd v
  {-# INLINE unitr #-}
  unitr' = K $ pure . This
  {-# INLINE unitr' #-}

-- | Inclusive symmetry on @K@ @m@.
instance (Monad m) => Action These (K m) where
  swap =
    K $
      pure . \case
        This a -> That a
        That b -> This b
        These a b -> These b a
  {-# INLINE swap #-}

-- | Lift 'Tensor'/'Action' through 'Loop'.
--
-- This is the single lawful instance: it evaluates each 'Loop' branch
-- independently with 'run' and combines the results using the base arrow's
-- tensor. It is correct and black-hole-free, but does not fuse feedback
-- loops. For the fused superposition of two 'Knot's, use 'superpose'.
instance (Tensor t arr, Traced t' arr) => Tensor t (Loop t' arr) where
  par f g = Lift (par (run f) (run g))
  unitl = Lift unitl
  unitl' = Lift unitl'
  unitr = Lift unitr
  unitr' = Lift unitr'

instance (Action t arr, Traced t' arr) => Action t (Loop t' arr) where
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
-- >>> let k1 = Circuit.Loop.Knot (\(ns, _) -> (1 : ns, take 3 ns)) :: Circuit.Loop.Loop (,) (->) [Int] [Int]
-- >>> let k2 = Circuit.Loop.Knot (\(ns, _) -> (2 : ns, take 3 ns))
-- >>> Circuit.Layer.run (superpose k1 k2) ([], [])
-- ([1,1,1],[2,2,2])
--
-- The same fusion works for @K@, preserving sharing across the
-- recursive channels under @MonadFix@.
--
-- >>> let k1 = Circuit.Loop.Knot (K $ \(ns, _) -> pure (1 : ns, take 3 ns)) :: Circuit.Loop.Loop (,) (K Identity) [Int] [Int]
-- >>> let k2 = Circuit.Loop.Knot (K $ \(ns, _) -> pure (2 : ns, take 3 ns))
-- >>> runK (Circuit.Layer.run (superpose k1 k2)) ([], [])
-- Identity ([1,1,1],[2,2,2])
superpose ::
  forall t arr a b c d.
  (Tensor t arr, Strength t arr) =>
  Loop t arr a b ->
  Loop t arr c d ->
  Loop t arr (t a c) (t b d)
superpose x y =
  case (x, y) of
    (Knot @_ @_ @_ @_ @_ f, Knot @_ @_ @_ @_ @_ g) ->
      Knot $
        pre .>> par f g .>> post
    (Knot @_ @_ @_ @_ @_ f, Lift g) ->
      Knot $
        assoc' .>> par f g .>> assoc
    (Lift f, Knot @_ @_ @_ @_ @_ g) ->
      Knot $
        braid .>> par f g .>> braid
    (Lift f, Lift g) -> Lift (par f g)
  where
    (.>>) :: forall x y z. arr x y -> arr y z -> arr x z
    (.>>) = (.>)

    assoc :: forall x y z. arr (t (t x y) z) (t x (t y z))
    assoc = Ch.assoc

    assoc' :: forall x y z. arr (t x (t y z)) (t (t x y) z)
    assoc' = Ch.assoc'

    braid :: forall x y z. arr (t x (t y z)) (t y (t x z))
    braid = Ch.slide

    pre, post :: forall u v w x. arr (t (t u v) (t w x)) (t (t u w) (t v x))
    pre = assoc .>> strength braid .>> assoc'
    post = assoc .>> strength braid .>> assoc'
