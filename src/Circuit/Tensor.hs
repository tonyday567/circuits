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
-- The goal is to keep the core 'Trace' syntax and 'Circuit.Syntax.eval' fold
-- independent of these structural details.
--
-- Note: the monomorphic 'assocL' and 'assocR' helpers below reassociate
-- /leftward/ and /rightward/ respectively — the opposite direction to
-- 'Circuit.Traced.assoc' and 'Circuit.Traced.assoc''.
--
-- 'Tensor' / 'Action' are kind-polymorphic.
module Circuit.Tensor
  ( -- * Fused parallel composition
    superpose,

    -- * Schedule bias (also used by additive disjunction)
    Bias (..),

    -- * Channel product on base arrows
    Unit,
    Unital (..),
    Tensor (..),
    Action (..),
    TensorSeed (..),

    -- * Distributivity of two tensors (multiplicative over additive)
    Distributive (..),

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
import Circuit.Category qualified as Cat (Op (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), TraceC, Yank (..))
import Circuit.Traced qualified as Ch
import Circuit.Syntax (Syntax (..), eval, (:+:) (..))
import Circuit.Trace (SigYank (..), Trace, base)
import Control.Monad (Monad)
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.These (These (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XLambdaCase
-- >>> import Circuit.Trace (Trace, base)
-- >>> import Circuit.Traced (yank)
-- >>> import Circuit.Syntax (eval)
-- >>> import Circuit.Category (K (..), runK)
-- >>> import Data.Functor.Identity (Identity)
-- >>> import Prelude hiding (id, (.))

-- * Schedule bias

-- | Bias for ordered choice in scheduling and additive disjunction.
--
-- 'LeftFirst' and 'RightFirst' are used by shared-medium fusion in
-- "Circuit.Shared" and by additive disjunction in "Circuit.Poles".
data Bias = LeftFirst | RightFirst
  deriving (Eq, Show)

-- * Cartesian structure ((,))

-- | Leftward associator: @(a, (b, c)) -> ((a, b), c)@.
assocL :: (a, (b, c)) -> ((a, b), c)
assocL ~(a, ~(b, c)) = ((a, b), c)

-- | Rightward associator: @((a, b), c) -> (a, (b, c))@.
assocR :: ((a, b), c) -> (a, (b, c))
assocR ~(~(a, b), c) = (a, (b, c))

-- Introduce a channel wire alongside a payload.
seed :: s -> a -> (s, a)
seed s a = (s, a)

-- Move a value from the payload into the channel wire.
--
-- absorb f = first (uncurry f) . assocL
absorb :: (t -> s -> s') -> (s, (t, b)) -> (s', b)
absorb f (s, (t, b)) = (f t s, b)

-- Move a value from the channel wire into the payload.
--
-- release f = assocR . first f
release :: (s -> (s', t)) -> (s, b) -> (s', (t, b))
release f (s, b) = let (s', t) = f s in (s', (t, b))

-- * Cocartesian structure (Either)

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

-- | Tag a channel value onto whichever branch of the sum is active.
--
-- >>> coseed "st" (Left 42 :: Either Int Char)
-- Left ("st",42)
coseed :: s -> Either a b -> Either (s, a) (s, b)
coseed s = bimap (s,) (s,)

-- | If the left branch is taken, move a value from the payload into the channel wire.
--
-- >>> coabsorbL (+) (Left (10, (3, 7)) :: Either (Int, (Int, Int)) Bool)
-- Left (13,7)
coabsorbL :: (t -> s -> s') -> Either (s, (t, a)) b -> Either (s', a) b
coabsorbL f (Left (s, (t, a))) = Left (f t s, a)
coabsorbL _ (Right b) = Right b

-- | If the right branch is taken, move a value from the payload into the channel wire.
--
-- >>> coabsorbR (+) (Right (10, (3, 7)) :: Either Bool (Int, (Int, Int)))
-- Right (13,7)
coabsorbR :: (t -> s -> s') -> Either a (s, (t, b)) -> Either a (s', b)
coabsorbR f (Right (s, (t, b))) = Right (f t s, b)
coabsorbR _ (Left a) = Left a

-- | If the left branch is taken, move a value from the channel wire into the payload.
--
-- >>> coreleaseL (\s -> (s+1, s*2)) (Left (5, 99) :: Either (Int, Int) Char)
-- Left (6,(10,99))
coreleaseL :: (s -> (s', t)) -> Either (s, a) b -> Either (s', (t, a)) b
coreleaseL f (Left (s, a)) = let (s', t) = f s in Left (s', (t, a))
coreleaseL _ (Right b) = Right b

-- | If the right branch is taken, move a value from the channel wire into the payload.
--
-- >>> coreleaseR (\s -> (s+1, s*2)) (Right (5, 99) :: Either Char (Int, Int))
-- Right (6,(10,99))
coreleaseR :: (s -> (s', t)) -> Either a (s, b) -> Either a (s', (t, b))
coreleaseR f (Right (s, b)) = let (s', t) = f s in Right (s', (t, b))
coreleaseR _ (Left a) = Left a

-- * Tensor / Action — tensor action on morphisms

-- | The unit object for a tensor @t@.
--
-- @t@ is an object-level bifunctor (@Either@, @(,)@, type-level @(+)@, …)
-- with kind @k -> k -> k@, not a morphism tensor.
type family Unit (t :: k -> k -> k) :: k

-- | Value-level pairing for a tensor @t@.
--
-- 'Tensor' gives the action of @t@ on morphisms; 'TensorSeed' names the
-- canonical way to combine two values into a value of type @t a b@.  It is
-- needed by constructions (such as 'Circuit.Body.SomeBody') that store a
-- concrete channel value alongside a body.
--
-- Not every tensor has a canonical pairing: @(,)@ has the pair constructor,
-- but 'Either' has no unbiased way to combine @a@ and @b@ into
-- @Either a b@.  Consequently 'TensorSeed' is a separate class.
class TensorSeed (t :: Type -> Type -> Type) where
  seedPair :: a -> b -> t a b

-- | Cartesian pairing.
instance TensorSeed (,) where
  seedPair = (,)
  {-# INLINE seedPair #-}

-- | The unit object structure of a tensor @t@ on a category @arr@.
--
-- 'unitl' and 'unitr' witness that the tensor has a unit object. This is
-- the planar fragment without the morphism-level tensor product: arrows
-- that are merely unital can introduce and eliminate the unit, but cannot
-- parallel-compose two arbitrary morphisms.
--
-- Splitting this out from 'Tensor' matters for premonoidal arrows such as
-- @Circuit.Prob@: the unitors are deterministic and embed cleanly, while
-- the general tensor product @tensor@ is not canonical.
--
-- Kind-polymorphic: @t@ and @arr@ share object kind (inferred via PolyKinds).
class (Category arr) => Unital t arr where
  -- | Left unitor: @I ⊗ a -> a@.
  unitl :: arr (t (Unit t) a) a

  -- | Inverse left unitor: @a -> I ⊗ a@.
  unitl' :: arr a (t (Unit t) a)

  -- | Right unitor: @a ⊗ I -> a@.
  unitr :: arr (t a (Unit t)) a

  -- | Inverse right unitor: @a -> a ⊗ I@.
  unitr' :: arr a (t a (Unit t))

-- | The tensor action of @t@ on a category @arr@, without braiding.
--
-- 'tensor' is the tensor product of morphisms (parallel composition on
-- disjoint wires). The unitors live in the 'Unital' superclass.
--
-- Kind-polymorphic: @t@ and @arr@ share object kind (inferred via PolyKinds).
class (Unital t arr) => Tensor t arr where
  -- | Parallel composition: run two arrows on disjoint wires.
  --
  -- >>> tensor ((+1) :: Int -> Int) ((*2) :: Int -> Int) (3, 4)
  -- (4,8)
  tensor :: arr a b -> arr c d -> arr (t a c) (t b d)

-- | The action of a tensor @t@ on a category @arr@, extended with a
-- symmetric braiding.
--
-- This is the self-action of a symmetric monoidal category: @t@ acts on
-- @arr@ by taking morphisms to morphisms over paired objects, and 'braid'
-- provides the symmetry.
class (Tensor t arr) => Action t arr where
  -- | Symmetric braiding.
  --
  -- >>> braid (3, 4) :: (Int, Int)
  -- (4,3)
  braid :: arr (t a b) (t b a)

-- * Distributivity

-- | Distributivity of a multiplicative tensor @d@ over an additive tensor @t@.
--
-- In a distributive monoidal category the product distributes over the sum:
-- @d a (t b c) ≅ t (d a b) (d a c)@ and @d (t a b) c ≅ t (d a c) (d b c)@,
-- and the additive unit is annihilated: @d a (Unit t) ≅ Unit t@.
--
-- For @d = (,)@ and @t = Either@ this is the ordinary distributivity of
-- cartesian product over coproduct, with @(a, Void) ≅ Void@.
class (Tensor d arr, Tensor t arr) => Distributive d t arr where
  -- | Left distributor: @d a (t b c) -> t (d a b) (d a c)@.
  distl :: arr (d a (t b c)) (t (d a b) (d a c))

  -- | Inverse left distributor.
  distl' :: arr (t (d a b) (d a c)) (d a (t b c))

  -- | Right distributor: @d (t a b) c -> t (d a c) (d b c)@.
  distr :: arr (d (t a b) c) (t (d a c) (d b c))

  -- | Inverse right distributor.
  distr' :: arr (t (d a c) (d b c)) (d (t a b) c)

  -- | Left annihilator: @d a (Unit t) -> Unit t@.
  annih :: arr (d a (Unit t)) (Unit t)

  -- | Inverse left annihilator.
  annih' :: arr (Unit t) (d a (Unit t))

type instance Unit (,) = ()

-- | Cartesian unit structure on functions.
--
-- Laws: 'unitl' = 'snd', 'unitl'' = @((),)@, 'unitr' = 'fst', 'unitr'' = @(,) ()@.
instance Unital (,) (->) where
  unitl ~((), a) = a
  {-# INLINE unitl #-}
  unitl' a = ((), a)
  {-# INLINE unitl' #-}
  unitr ~(a, ()) = a
  {-# INLINE unitr #-}
  unitr' a = (a, ())
  {-# INLINE unitr' #-}

-- | Cartesian tensor action on functions.
instance Tensor (,) (->) where
  tensor f g (a, c) = (f a, g c)
  {-# INLINE tensor #-}

-- | Cartesian symmetry on functions.
instance Action (,) (->) where
  braid (a, b) = (b, a)
  {-# INLINE braid #-}

-- | Distributivity of @(,)@ over 'Either' on functions.
--
-- >>> distl ('x', Left 1 :: Either Int Bool) :: Either (Char, Int) (Char, Bool)
-- Left ('x',1)
--
-- >>> distl ('x', Right True) :: Either (Char, Int) (Char, Bool)
-- Right ('x',True)
instance Distributive (,) Either (->) where
  distl (a, Left b) = Left (a, b)
  distl (a, Right c) = Right (a, c)
  {-# INLINE distl #-}
  distl' = \case
    Left (a, b) -> (a, Left b)
    Right (a, c) -> (a, Right c)
  {-# INLINE distl' #-}
  distr (Left a, c) = Left (a, c)
  distr (Right b, c) = Right (b, c)
  {-# INLINE distr #-}
  distr' = \case
    Left (a, c) -> (Left a, c)
    Right (b, c) -> (Right b, c)
  {-# INLINE distr' #-}
  annih = absurd . snd
  {-# INLINE annih #-}
  annih' = absurd
  {-# INLINE annih' #-}

-- | Cartesian unit structure on @K@ (effectful sequential product).
instance (Monad m) => Unital (,) (K m) where
  unitl = K $ \((), a) -> pure a
  {-# INLINE unitl #-}
  unitl' = K $ \a -> pure ((), a)
  {-# INLINE unitl' #-}
  unitr = K $ \(a, ()) -> pure a
  {-# INLINE unitr #-}
  unitr' = K $ \a -> pure (a, ())
  {-# INLINE unitr' #-}

-- | Cartesian tensor on @K@ (effectful sequential product).
instance (Monad m) => Tensor (,) (K m) where
  tensor (K f) (K g) =
    K $ \(a, c) -> do
      b <- f a
      d <- g c
      pure (b, d)
  {-# INLINE tensor #-}

instance (Monad m) => Action (,) (K m) where
  braid = K $ \(a, b) -> pure (b, a)
  {-# INLINE braid #-}

-- | Distributivity of @(,)@ over 'Either' on @K m@.
instance (Monad m) => Distributive (,) Either (K m) where
  distl =
    K $
      pure . \case
        (a, Left b) -> Left (a, b)
        (a, Right c) -> Right (a, c)
  {-# INLINE distl #-}
  distl' =
    K $
      pure . \case
        Left (a, b) -> (a, Left b)
        Right (a, c) -> (a, Right c)
  {-# INLINE distl' #-}
  distr =
    K $
      pure . \case
        (Left a, c) -> Left (a, c)
        (Right b, c) -> Right (b, c)
  {-# INLINE distr #-}
  distr' =
    K $
      pure . \case
        Left (a, c) -> (Left a, c)
        Right (b, c) -> (Right b, c)
  {-# INLINE distr' #-}
  annih = K $ pure . absurd . snd
  {-# INLINE annih #-}
  annih' = K $ pure . absurd
  {-# INLINE annih' #-}

type instance Unit Either = Void

-- | Coproduct unit structure on functions.
--
-- Laws: 'unitl' eliminates 'Left', 'unitl'' injects 'Right'; 'unitr'
-- eliminates 'Right', 'unitr'' injects 'Left'.
instance Unital Either (->) where
  unitl = either absurd id
  {-# INLINE unitl #-}
  unitl' = Right
  {-# INLINE unitl' #-}
  unitr = either id absurd
  {-# INLINE unitr #-}
  unitr' = Left
  {-# INLINE unitr' #-}

-- | Coproduct tensor action on functions.
--
-- >>> tensor ((+1) :: Int -> Int) ((*2) :: Int -> Int) (Left 3 :: Either Int Int)
-- Left 4
--
-- >>> tensor ((+1) :: Int -> Int) ((*2) :: Int -> Int) (Right 3 :: Either Int Int)
-- Right 6
instance Tensor Either (->) where
  tensor = bimap
  {-# INLINE tensor #-}

-- | Coproduct symmetry on functions.
--
-- >>> braid (Left 3 :: Either Int Int) :: Either Int Int
-- Right 3
instance Action Either (->) where
  braid = \case
    Left a -> Right a
    Right b -> Left b
  {-# INLINE braid #-}

-- | Coproduct unit structure on @K@ @m@.
instance (Monad m) => Unital Either (K m) where
  unitl = K $ either absurd pure
  {-# INLINE unitl #-}
  unitl' = K $ pure . Right
  {-# INLINE unitl' #-}
  unitr = K $ either pure absurd
  {-# INLINE unitr #-}
  unitr' = K $ pure . Left
  {-# INLINE unitr' #-}

-- | Coproduct tensor action on @K@ @m@.
--
-- >>> import Circuit.Category (K(..), runK)
-- >>> let f = K (\n -> pure (n + 1)) :: K IO Int Int
-- >>> let g = K (\n -> pure (n * 2)) :: K IO Int Int
-- >>> runK (tensor f g) (Left 3 :: Either Int Int)
-- Left 4
-- >>> runK (tensor f g) (Right 3 :: Either Int Int)
-- Right 6
instance (Monad m) => Tensor Either (K m) where
  tensor (K f) (K g) =
    K $ \case
      Left a -> Left <$> f a
      Right c -> Right <$> g c
  {-# INLINE tensor #-}

-- | Coproduct symmetry on @K@ @m@.
instance (Monad m) => Action Either (K m) where
  braid = K $ pure . braid
  {-# INLINE braid #-}

type instance Unit These = Void

-- | Inclusive unit structure on functions.
--
-- Laws: 'unitl' eliminates a vacuous 'This', 'unitl'' injects with 'That';
-- 'unitr' eliminates a vacuous 'That', 'unitr'' injects with 'This'.
instance Unital These (->) where
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

-- | Inclusive tensor action on functions.
instance Tensor These (->) where
  tensor = bimap
  {-# INLINE tensor #-}

-- | Inclusive symmetry on functions.
instance Action These (->) where
  braid (This a) = That a
  braid (That b) = This b
  braid (These a b) = These b a
  {-# INLINE braid #-}

-- | Inclusive unit structure on @K@ @m@.
instance (Monad m) => Unital These (K m) where
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

-- | Inclusive tensor action on @K@ @m@.
instance (Monad m) => Tensor These (K m) where
  tensor (K f) (K g) =
    K $ \case
      This a -> This <$> f a
      That c -> That <$> g c
      These a c -> These <$> f a <*> g c
  {-# INLINE tensor #-}

-- | Inclusive symmetry on @K@ @m@.
instance (Monad m) => Action These (K m) where
  braid =
    K $
      pure . \case
        This a -> That a
        That b -> This b
        These a b -> These b a
  {-# INLINE braid #-}

-- | Lift 'Unital' through 'Trace'.
instance (Unital t arr) => Unital t (Trace t' arr) where
  unitl = base unitl
  unitl' = base unitl'
  unitr = base unitr
  unitr' = base unitr'

-- | Opposite category: unitors are reversed along with the base arrow.
instance (Unital t arr) => Unital t (Cat.Op arr) where
  unitl = Cat.Op unitl'
  unitl' = Cat.Op unitl
  unitr = Cat.Op unitr'
  unitr' = Cat.Op unitr

-- | Lift 'Tensor'/'Action' through 'Trace'.
--
-- This is the single lawful instance: it evaluates each 'Trace' branch
-- independently with 'Circuit.Syntax.eval' and combines the results using the
-- base arrow's tensor. It is correct and black-hole-free, but does not fuse
-- feedback loops. For the fused superposition of two 'Circuit.Trace.yank's,
-- use 'superpose'.
instance (Tensor t arr, Yank t' arr) => Tensor t (Trace t' arr) where
  tensor f g = base (tensor (eval f) (eval g))

instance (Action t arr, Yank t' arr) => Action t (Trace t' arr) where
  braid = base braid

-- | Fused parallel composition for 'Trace' when the feedback tensor matches.
--
-- Two 'Circuit.Traced.yank's in parallel superpose into one 'Circuit.Traced.yank' over a paired channel,
-- satisfying the superposing axiom of traced monoidal categories:
--
-- @superpose (trace f) (trace g) = trace (pre . tensor f g . post)@
--
-- where @pre@ and @post@ rearrange the paired channel via associators
-- and braiding. This preserves sharing for recursive circuits; the lawful
-- 'Tensor' instance falls back to independent evaluation.
--
-- >>> let k1 = yank (base (\(ns, _) -> (1 : ns, take 3 ns))) :: Trace (,) (->) [Int] [Int]
-- >>> let k2 = yank (base (\(ns, _) -> (2 : ns, take 3 ns)))
-- >>> eval (superpose k1 k2) ([], [])
-- ([1,1,1],[2,2,2])
--
-- The same fusion works for @K@, preserving sharing across the
-- recursive channels under @MonadFix@.
--
-- >>> let k1 = yank (base (K $ \(ns, _) -> pure (1 : ns, take 3 ns))) :: Trace (,) (K Identity) [Int] [Int]
-- >>> let k2 = yank (base (K $ \(ns, _) -> pure (2 : ns, take 3 ns)))
-- >>> runK (eval (superpose k1 k2)) ([], [])
-- Identity ([1,1,1],[2,2,2])
superpose ::
  forall t arr a b c d.
  (Tensor t arr, TraceC t arr) =>
  Trace t arr a b ->
  Trace t arr c d ->
  Trace t arr (t a c) (t b d)
superpose x y =
  case (x, y) of
    (Lift f, Lift g) ->
      base (tensor f g)
    (Oper (R (YankBody f)), Lift g) ->
      yank (base assoc . base (tensor (eval f) g) . base assoc')
    (Lift f, Oper (R (YankBody g))) ->
      yank (base shuffle . base (tensor f (eval g)) . base shuffle)
    (Oper (R (YankBody f)), Oper (R (YankBody g))) ->
      yank (base post . base (tensor (eval f) (eval g)) . base pre)
    -- Non-normal forms fall back to the lawful independent-evaluation instance.
    _ ->
      base (tensor (eval x) (eval y))
  where
    reassoc :: forall x y z. arr (t (t x y) z) (t x (t y z))
    reassoc = Ch.assoc

    reassoc' :: forall x y z. arr (t x (t y z)) (t (t x y) z)
    reassoc' = Ch.assoc'

    shuffle :: forall x y z. arr (t x (t y z)) (t y (t x z))
    shuffle = Ch.slide

    pre, post :: forall u v w x. arr (t (t u v) (t w x)) (t (t u w) (t v x))
    pre = reassoc .> strength shuffle .> reassoc'
    post = reassoc .> strength shuffle .> reassoc'
