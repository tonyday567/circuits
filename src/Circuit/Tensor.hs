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

module Circuit.Tensor
  ( superpose,
    Bias (..),
    Unit,
    Unital (..),
    SemiTensor (..),
    Tensor,
    Action (..),
    Distributive (..),
    Const (..),
    reassocL,
    reassocR,
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
import Circuit.Syntax (Syntax (..), eval, evalInto, (:+:) (..))
import Circuit.Trace (Knot (..), SigYank (..), Trace)
import Circuit.Traced (Assoc (..), Strength (..), TraceC, Yank (..))
import Circuit.Traced qualified as Ch
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.These (These (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

data Bias = LeftFirst | RightFirst
  deriving (Eq, Show)

reassocL :: (a, (b, c)) -> ((a, b), c)
reassocL ~(a, ~(b, c)) = ((a, b), c)

reassocR :: ((a, b), c) -> (a, (b, c))
reassocR ~(~(a, b), c) = (a, (b, c))

seed :: s -> a -> (s, a)
seed s a = (s, a)

absorb :: (t -> s -> s') -> (s, (t, b)) -> (s', b)
absorb f (s, (t, b)) = (f t s, b)

release :: (s -> (s', t)) -> (s, b) -> (s', (t, b))
release f (s, b) = let (s', t) = f s in (s', (t, b))

coassoc :: Either a (Either b c) -> Either (Either a b) c
coassoc (Left a) = Left (Left a)
coassoc (Right (Left b)) = Left (Right b)
coassoc (Right (Right c)) = Right c

coassoc' :: Either (Either a b) c -> Either a (Either b c)
coassoc' (Left (Left a)) = Left a
coassoc' (Left (Right b)) = Right (Left b)
coassoc' (Right c) = Right (Right c)

coseed :: s -> Either a b -> Either (s, a) (s, b)
coseed s = bimap (s,) (s,)

coabsorbL :: (t -> s -> s') -> Either (s, (t, a)) b -> Either (s', a) b
coabsorbL f (Left (s, (t, a))) = Left (f t s, a)
coabsorbL _ (Right b) = Right b

coabsorbR :: (t -> s -> s') -> Either a (s, (t, b)) -> Either a (s', b)
coabsorbR f (Right (s, (t, b))) = Right (f t s, b)
coabsorbR _ (Left a) = Left a

coreleaseL :: (s -> (s', t)) -> Either (s, a) b -> Either (s', (t, a)) b
coreleaseL f (Left (s, a)) = let (s', t) = f s in Left (s', (t, a))
coreleaseL _ (Right b) = Right b

coreleaseR :: (s -> (s', t)) -> Either a (s, b) -> Either a (s', (t, b))
coreleaseR f (Right (s, b)) = let (s', t) = f s in Right (s', (t, b))
coreleaseR _ (Left a) = Left a

type family Unit (t :: k -> k -> k) :: k

class (Category arr) => Unital t arr where
  unitl :: arr (t (Unit t) a) a

  unitl' :: arr a (t (Unit t) a)

  unitr :: arr (t a (Unit t)) a

  unitr' :: arr a (t a (Unit t))

class (Category arr, Assoc t arr) => SemiTensor t arr where
  tensor :: arr a b -> arr c d -> arr (t a c) (t b d)

class (Unital t arr, SemiTensor t arr) => Tensor t arr

class (Tensor t arr) => Action t arr where
  braid :: arr (t a b) (t b a)

data Const ch i = Const i
  deriving (Eq, Show)

instance Assoc Const (->) where
  assoc (Const x) = Const (Const x)
  assoc' (Const (Const x)) = Const x

instance SemiTensor Const (->) where
  tensor _f g (Const x) = Const (g x)

class (Tensor d arr, Tensor t arr) => Distributive d t arr where
  distl :: arr (d a (t b c)) (t (d a b) (d a c))

  distl' :: arr (t (d a b) (d a c)) (d a (t b c))

  distr :: arr (d (t a b) c) (t (d a c) (d b c))

  distr' :: arr (t (d a c) (d b c)) (d (t a b) c)

  annih :: arr (d a (Unit t)) (Unit t)

  annih' :: arr (Unit t) (d a (Unit t))

type instance Unit (,) = ()

instance Unital (,) (->) where
  unitl ~((), a) = a
  {-# INLINE unitl #-}
  unitl' a = ((), a)
  {-# INLINE unitl' #-}
  unitr ~(a, ()) = a
  {-# INLINE unitr #-}
  unitr' a = (a, ())
  {-# INLINE unitr' #-}

instance SemiTensor (,) (->) where
  tensor f g (a, c) = (f a, g c)
  {-# INLINE tensor #-}

instance Tensor (,) (->)

instance Action (,) (->) where
  braid (a, b) = (b, a)
  {-# INLINE braid #-}

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

instance (Monad m) => Unital (,) (K m) where
  unitl = K $ \((), a) -> pure a
  {-# INLINE unitl #-}
  unitl' = K $ \a -> pure ((), a)
  {-# INLINE unitl' #-}
  unitr = K $ \(a, ()) -> pure a
  {-# INLINE unitr #-}
  unitr' = K $ \a -> pure (a, ())
  {-# INLINE unitr' #-}

instance (Monad m) => SemiTensor (,) (K m) where
  tensor (K f) (K g) =
    K $ \(a, c) -> do
      b <- f a
      d <- g c
      pure (b, d)
  {-# INLINE tensor #-}

instance (Monad m) => Tensor (,) (K m)

instance (Monad m) => Action (,) (K m) where
  braid = K $ \(a, b) -> pure (b, a)
  {-# INLINE braid #-}

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

instance Unital Either (->) where
  unitl = either absurd id
  {-# INLINE unitl #-}
  unitl' = Right
  {-# INLINE unitl' #-}
  unitr = either id absurd
  {-# INLINE unitr #-}
  unitr' = Left
  {-# INLINE unitr' #-}

instance SemiTensor Either (->) where
  tensor = bimap
  {-# INLINE tensor #-}

instance Tensor Either (->)

instance Action Either (->) where
  braid = \case
    Left a -> Right a
    Right b -> Left b
  {-# INLINE braid #-}

instance (Monad m) => Unital Either (K m) where
  unitl = K $ either absurd pure
  {-# INLINE unitl #-}
  unitl' = K $ pure . Right
  {-# INLINE unitl' #-}
  unitr = K $ either pure absurd
  {-# INLINE unitr #-}
  unitr' = K $ pure . Left
  {-# INLINE unitr' #-}

instance (Monad m) => SemiTensor Either (K m) where
  tensor (K f) (K g) =
    K $ \case
      Left a -> Left <$> f a
      Right c -> Right <$> g c
  {-# INLINE tensor #-}

instance (Monad m) => Tensor Either (K m)

instance (Monad m) => Action Either (K m) where
  braid = K $ pure . braid
  {-# INLINE braid #-}

type instance Unit These = Void

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

instance SemiTensor These (->) where
  tensor = bimap
  {-# INLINE tensor #-}

instance Tensor These (->)

instance Action These (->) where
  braid (This a) = That a
  braid (That b) = This b
  braid (These a b) = These b a
  {-# INLINE braid #-}

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

instance (Monad m) => SemiTensor These (K m) where
  tensor (K f) (K g) =
    K $ \case
      This a -> This <$> f a
      That c -> That <$> g c
      These a c -> These <$> f a <*> g c
  {-# INLINE tensor #-}

instance (Monad m) => Tensor These (K m)

instance (Monad m) => Action These (K m) where
  braid =
    K $
      pure . \case
        This a -> That a
        That b -> This b
        These a b -> These b a
  {-# INLINE braid #-}

instance (Unital t arr) => Unital t (Trace t' arr) where
  unitl = Lift unitl
  unitl' = Lift unitl'
  unitr = Lift unitr
  unitr' = Lift unitr'

instance (Unital t arr) => Unital t (Cat.Op arr) where
  unitl = Cat.Op unitl'
  unitl' = Cat.Op unitl
  unitr = Cat.Op unitr'
  unitr' = Cat.Op unitr

instance
  (SemiTensor t arr, Yank t' arr, Assoc t (Trace t' arr)) =>
  SemiTensor t (Trace t' arr)
  where
  tensor f g = Lift (tensor (eval f) (eval g))

instance
  (Tensor t arr, Yank t' arr, Assoc t (Trace t' arr)) =>
  Tensor t (Trace t' arr)

instance
  (Action t arr, Yank t' arr, Assoc t (Trace t' arr)) =>
  Action t (Trace t' arr)
  where
  braid = Lift braid

superpose ::
  forall t arr a b c d.
  (Tensor t arr, TraceC t arr) =>
  Trace t arr a b ->
  Trace t arr c d ->
  Trace t arr (t a c) (t b d)
superpose x y =
  case (toKnot x, toKnot y) of
    (Arr f, Arr g) ->
      Lift (tensor f g)
    (Knot f, Arr g) ->
      yank (Lift (reassoc' .> tensor f g .> reassoc))
    (Arr f, Knot g) ->
      yank (Lift (shuffle .> tensor f g .> shuffle))
    (Knot f, Knot g) ->
      yank (Lift (pre .> tensor f g .> post))
  where
    toKnot :: Trace t arr u v -> Knot t arr u v
    toKnot = evalInto Arr

    reassoc :: forall x y z. arr (t (t x y) z) (t x (t y z))
    reassoc = Ch.assoc

    reassoc' :: forall x y z. arr (t x (t y z)) (t (t x y) z)
    reassoc' = Ch.assoc'

    shuffle :: forall x y z. arr (t x (t y z)) (t y (t x z))
    shuffle = Ch.slide

    pre, post :: forall u v w x. arr (t (t u v) (t w x)) (t (t u w) (t v x))
    pre = reassoc .> strength shuffle .> reassoc'
    post = reassoc .> strength shuffle .> reassoc'
