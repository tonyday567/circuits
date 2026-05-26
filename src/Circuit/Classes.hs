{-# LANGUAGE CPP #-}

-- | On GHC, Category, Bifunctor, and Profunctor come from packages.
-- On other compilers (e.g. MicroHs), we define them locally.
module Circuit.Classes where

#ifndef __GLASGOW_HASKELL__

import Prelude hiding (id, (.))

class Category cat where
  id :: cat a a
  (.) :: cat b c -> cat a b -> cat a c

instance Category (->) where
  id x = x
  (f . g) x = f (g x)

class Bifunctor p where
  bimap :: (a -> b) -> (c -> d) -> p a c -> p b d
  first :: (a -> b) -> p a c -> p b c
  second :: (b -> c) -> p a b -> p a c
  bimap f g = first f . second g
  first f = bimap f id
  second = bimap id

instance Bifunctor (,) where
  bimap f g (a, b) = (f a, g b)

instance Bifunctor Either where
  bimap f _ (Left a) = Left (f a)
  bimap _ g (Right b) = Right (g b)

class Profunctor p where
  dimap :: (a -> b) -> (c -> d) -> p b c -> p a d
  lmap :: (a -> b) -> p b c -> p a c
  rmap :: (b -> c) -> p a b -> p a c
  dimap f g = lmap f . rmap g
  lmap f = dimap f id
  rmap = dimap id

#endif
