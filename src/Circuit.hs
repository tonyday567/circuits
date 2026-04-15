{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Circuit
  ( -- * Circuit
    Circuit (..),
    Trace (..),
    run,
  )
where

import Control.Category (Category (..), id, (.))
import Data.Bifunctor ()
import Data.Functor ()
import Data.Profunctor
import Data.Profunctor.Strong ()
import Prelude hiding (id, (.))

class Trace arr t where
  trace :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)

instance {-# OVERLAPPABLE #-} Trace (->) (,) where
  trace f b = let (a, c) = f (a, b) in c
  untrace = fmap

instance {-# OVERLAPPING #-} Trace (->) Either where
  -- trace f b = fix (\go x -> either (go . Left) id (f x)) (Right b)
  trace f b = go (Right b)
    where
      go x = case f x of
        Right c -> c
        Left a -> go (Left a)
  untrace = fmap

instance {-# OVERLAPPABLE #-} (Costrong p, Strong p) => Trace p (,) where
  trace = unsecond
  untrace = second'

instance (Cochoice p, Choice p) => Trace p Either where
  trace = unright
  untrace = right'

data Circuit arr t a b where
  Lift :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  Loop :: arr (t a b) (t a c) -> Circuit arr t b c

instance (Category arr) => Category (Circuit arr t) where
  id = Lift id
  (.) = Compose

instance Functor (Circuit (->) t a) where
  fmap f = Compose (Lift f)

instance Profunctor (Circuit (->) t) where
  dimap f g a = Compose (Lift g) (Compose a (Lift f))
  lmap f a = Compose a (Lift f)
  rmap g = Compose (Lift g)

instance (Trace (->) t) => Applicative (Circuit (->) t x) where
  pure a = Lift (const a)
  f <*> v = Lift $ \x -> run f x (run v x)

instance (Trace (->) t) => Monad (Circuit (->) t x) where
  m >>= k = Lift $ \x -> run (k (run m x)) x

run :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
run (Lift f) = f
run (Compose (Loop f) g) = trace (f . untrace (run g))
run (Compose f g) = run f . run g
run (Loop k) = trace k
