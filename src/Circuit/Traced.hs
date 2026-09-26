{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Circuit.Traced
  ( Assoc (..),
    Slide (..),
    Strength (..),
    Yank (..),
    TraceC,
  )
where

import Circuit.Category (Category (..), K (..), Op (..))
import Control.Monad.Fix (MonadFix, mfix)
import Data.Kind (Type)
import Data.These (These (..))
import GHC.Exts (PromptTag#, control0#, newPromptTag#, prompt#)
import GHC.IO (IO (..))
import Prelude hiding (id, (.))

class
  (Category arr) =>
  Assoc (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type)
  where
  assoc ::
    arr (t (t a b) c) (t a (t b c))

  assoc' ::
    arr (t a (t b c)) (t (t a b) c)

instance Assoc (,) (->) where
  assoc ~(~(a, b), c) = (a, (b, c))
  assoc' ~(a, ~(b, c)) = ((a, b), c)

instance Assoc Either (->) where
  assoc (Left (Left a)) = Left a
  assoc (Left (Right b)) = Right (Left b)
  assoc (Right c) = Right (Right c)
  assoc' (Left a) = Left (Left a)
  assoc' (Right (Left b)) = Left (Right b)
  assoc' (Right (Right c)) = Right c

instance Assoc These (->) where
  assoc (This (This a)) = This a
  assoc (This (That b)) = That (This b)
  assoc (This (These a b)) = These a (This b)
  assoc (That c) = That (That c)
  assoc (These (This a) c) = These a (That c)
  assoc (These (That b) c) = That (These b c)
  assoc (These (These a b) c) = These a (These b c)
  assoc' (This a) = This (This a)
  assoc' (That (This b)) = This (That b)
  assoc' (That (That c)) = That c
  assoc' (That (These b c)) = These (That b) c
  assoc' (These a (This b)) = This (These a b)
  assoc' (These a (That c)) = These (This a) c
  assoc' (These a (These b c)) = These (These a b) c

instance (Assoc t arr) => Assoc t (Op arr) where
  assoc = Op assoc'
  assoc' = Op assoc

class
  (Category arr) =>
  Slide (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type)
  where
  slide ::
    arr (t a (t b c)) (t b (t a c))

instance Slide (,) (->) where
  slide ~(a, ~(b, c)) = (b, (a, c))

instance Slide Either (->) where
  slide (Left a) = Right (Left a)
  slide (Right (Left b)) = Left b
  slide (Right (Right c)) = Right (Right c)

instance Slide These (->) where
  slide (This a) = That (This a)
  slide (That (This b)) = This b
  slide (That (That c)) = That (That c)
  slide (That (These b c)) = These b (That c)
  slide (These a (This b)) = These b (This a)
  slide (These a (That c)) = That (These a c)
  slide (These a (These b c)) = These b (These a c)

instance (Slide t arr) => Slide t (Op arr) where
  slide = Op slide

class (Assoc t arr, Slide t arr) => Strength (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) where
  strength ::
    arr b c ->
    arr (t a b) (t a c)

instance Strength (,) (->) where
  strength f p = (fst p, f (snd p))

instance Strength Either (->) where
  strength = fmap

instance Strength These (->) where
  strength _ (This a) = This a
  strength f (That b) = That (f b)
  strength f (These a b) = These a (f b)

instance (Strength t arr) => Strength t (Op arr) where
  strength (Op f) = Op (strength f)

class (Strength t arr) => Yank (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) where
  yank ::
    arr (t a b) (t a c) ->
    arr b c

type TraceC t arr = (Assoc t arr, Slide t arr, Strength t arr, Yank t arr)

instance Yank (,) (->) where
  yank f b = let ~(a, c) = f (a, b) in c

instance Yank Either (->) where
  yank f b = go (Right b)
    where
      go x = case f x of
        Right c -> c
        Left a -> go (Left a)

instance Yank These (->) where
  yank f b = go (That b)
    where
      go x = case f x of
        That c -> c
        This s -> go (This s)
        These _ c -> c

instance (Monad m) => Assoc (,) (K m) where
  assoc = K $ \ ~(~(a, b), c) -> pure (a, (b, c))
  assoc' = K $ \ ~(a, ~(b, c)) -> pure ((a, b), c)

instance (Monad m) => Assoc Either (K m) where
  assoc = K $ \case
    Left (Left a) -> pure (Left a)
    Left (Right b) -> pure (Right (Left b))
    Right c -> pure (Right (Right c))
  assoc' = K $ \case
    Left a -> pure (Left (Left a))
    Right (Left b) -> pure (Left (Right b))
    Right (Right c) -> pure (Right c)

instance (Monad m) => Assoc These (K m) where
  assoc =
    K $
      pure . \case
        This (This a) -> This a
        This (That b) -> That (This b)
        This (These a b) -> These a (This b)
        That c -> That (That c)
        These (This a) c -> These a (That c)
        These (That b) c -> That (These b c)
        These (These a b) c -> These a (These b c)
  assoc' =
    K $
      pure . \case
        This a -> This (This a)
        That (This b) -> This (That b)
        That (That c) -> That c
        That (These b c) -> These (That b) c
        These a (This b) -> This (These a b)
        These a (That c) -> These (This a) c
        These a (These b c) -> These (These a b) c

instance (Monad m) => Slide (,) (K m) where
  slide = K $ \ ~(a, ~(b, c)) -> pure (b, (a, c))

instance (Monad m) => Slide Either (K m) where
  slide = K $ \case
    Left a -> pure (Right (Left a))
    Right (Left b) -> pure (Left b)
    Right (Right c) -> pure (Right (Right c))

instance (Monad m) => Slide These (K m) where
  slide =
    K $
      pure . \case
        This a -> That (This a)
        That (This b) -> This b
        That (That c) -> That (That c)
        That (These b c) -> These b (That c)
        These a (This b) -> These b (This a)
        These a (That c) -> That (These a c)
        These a (These b c) -> These b (These a c)

instance (Monad m) => Strength (,) (K m) where
  strength (K f) =
    K
      ( \p -> do
          c <- f (snd p)
          pure (fst p, c)
      )

instance (MonadFix m) => Yank (,) (K m) where
  yank (K f) =
    K
      ( \b -> do
          (_, c) <- mfix $ \ ~(s, _) -> f (s, b)
          pure c
      )

instance (Monad m) => Strength Either (K m) where
  strength (K f) =
    K $ \case
      Left a -> pure (Left a)
      Right b -> Right <$> f b

instance (Monad m) => Strength These (K m) where
  strength (K f) =
    K $ \case
      This a -> pure (This a)
      That b -> That <$> f b
      These a b -> These a <$> f b

instance {-# OVERLAPPABLE #-} (Monad m) => Yank Either (K m) where
  yank (K f) =
    K $ \b -> go (Right b)
    where
      go x =
        f x >>= \case
          Right c -> pure c
          Left a -> go (Left a)

data PromptTag a = PromptTag (PromptTag# a)

newPromptTag :: IO (PromptTag a)
newPromptTag =
  IO
    ( \s ->
        case newPromptTag# s of
          (# s', t #) -> (# s', PromptTag t #)
    )

prompt :: PromptTag a -> IO a -> IO a
prompt (PromptTag t) (IO m) = IO (prompt# t m)

control0 :: forall a b. PromptTag a -> ((IO b -> IO a) -> IO a) -> IO b
control0 (PromptTag t) f = IO (control0# t arg)
  where
    arg f# s = case f (\(IO x) -> IO (f# x)) of IO m -> m s

instance {-# OVERLAPPING #-} Yank Either (K IO) where
  yank (K body) =
    K
      ( \initial -> do
          tag <- newPromptTag
          let go x =
                prompt tag $
                  body x
                    >>= ( \case
                            Right c -> pure c
                            Left a -> control0 tag (\k -> k (go (Left a)))
                        )
          go (Right initial)
      )

instance (Yank t arr) => Yank t (Op arr) where
  yank :: forall a b c. Op arr (t a b) (t a c) -> Op arr b c
  yank (Op f) = Op (yank f)
