{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The free traced monoidal category over any base category
module Traced
  ( -- * Traced
    TracedA (..)
  , Traced
  , Trace(..)
    -- * operators
  , (⊙)
  , (⊲)
  , (↬)

  -- * runner
  , run
  , (⊢)
  ) where

import Prelude hiding (id, (.))
import Control.Category (Category(..), id, (.))
import Data.Profunctor.Strong (Costrong (..), Strong(..))
import Data.Profunctor
import Data.Functor (Functor(..))
import Data.Bifunctor
import Data.Tuple (swap)

-- | the Trace action being eliminated goes on the left of the (co)product:
-- A Trace is an adjunction:
-- untrace | trace
-- where trace eliminates the action channel and untrace injects into the underlying type.  
--
-- - (a,)  for pairs
-- - Either a for Either
-- - These a for These
--
-- This is opposite to the profunctors convention.
--
class Trace arr t where
  trace :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)

-- | unsecond
instance {-# OVERLAPPING #-} Trace (->) (,) where
  trace f b = let (a, c) = f (a, b) in c
  untrace = fmap

-- | unright
-- trace f b = fix (\go x -> either (go . Left) id (f x)) (Right b)
instance {-# OVERLAPPING #-} Trace (->) Either where
  trace f b = go (Right b)
    where
      go x = case f x of
        Right c -> c    
        Left a -> go (Left a)
  untrace = fmap

-- | Costrong profunctor instance: trace via unsecond
instance (Category p, Costrong p, Strong p) => Trace p (,) where
  trace k = unsecond k
  untrace k = second' k

-- | Cochoice profunctor instance: trace via unright
instance (Category p, Cochoice p, Choice p) => Trace p Either where
  trace k = unright k
  untrace k = right' k

-- | The Free Traced Monoidal Category
data TracedA arr t a b where
  Lift :: arr a b -> TracedA arr t a b
  Compose :: TracedA arr t b c -> TracedA arr t a b -> TracedA arr t a c
  Knot :: arr (t a b) (t a c) -> TracedA arr t b c

type a ↝ b = TracedA (->) (,) a b 

(⊙) :: (b ↝ c) -> (a ↝ b)-> (a ↝ c)
(⊙) = Compose

(⊲) :: (a -> b) -> (a ↝ b) 
(⊲) = Lift

(↬) :: ((c,a) -> (c,b)) -> (a ↝ b)
(↬) = Knot

instance (Category arr) => Category (TracedA arr t) where
  id = Lift id
  (.) = Compose

-- | Map a function over the output type: sequential composition with the mapped arrow.
-- This satisfies functor laws by the category laws of composition.
--
-- >>> let f = Lift (+ 1) :: Traced Int Int
-- >>> let fmapped = fmap (* 2) f :: Traced Int Int
-- >>> run fmapped 5
-- 12
instance Functor (TracedA (->) t a) where
  fmap f g = Compose (Lift f) g

-- | Profunctor: contravariant in input, covariant in output.
-- Prepend a transformation on input, append a transformation on output.
--
-- >>> import Data.Profunctor
-- >>> let f = Lift (\x -> x * 2) :: Traced Int Int
-- >>> let f' = dimap (+ 1) (+ 100) f :: Traced Int Int
-- >>> run f' 5
-- 112
instance Profunctor (TracedA (->) t) where
  dimap f g a = Compose (Lift g) (Compose a (Lift f))
  lmap f a = Compose a (Lift f)
  rmap g a = Compose (Lift g) a

-- | Applicative: combine two traced computations from the same context.
-- Like Reader, both traced values depend on the same starting point.
--
-- >>> let f = Lift (\x -> \y -> x + y) :: Traced Int (Int -> Int)
-- >>> let v = Lift (\x -> x * 2) :: Traced Int Int
-- >>> run (f <*> v) 5
-- 15
instance Trace (->) t => Applicative (TracedA (->) t x) where
  pure a = Lift (const a)
  f <*> v = Lift $ \x -> run f x (run v x)

-- | Monad: sequence two traced computations, threading the result.
--
-- >>> let m = Lift (\x -> x * 2) :: Traced Int Int
-- >>> let k a = Lift (const (a + 1))
-- >>> run (m >>= k) 5
-- 11
instance Trace (->) t => Monad (TracedA (->) t x) where
  m >>= k = Lift $ \x -> run (k (run m x)) x

-- | The classical product traced of ArrowLoop
type Traced = TracedA (->) (,)

-- | Evaluate a traced arrow to its underlying arrow.
--
-- >>> let f = Compose (Lift (+ 1)) (Lift (* 2)) :: Traced Int Int
-- >>> run f 5
-- 11
--
-- >>> let g = Knot (\(fibs, i) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs !! i)) :: Traced Int Int
-- >>> run g 10
-- 55
run :: (Category arr, Trace arr t) => TracedA arr t x y -> arr x y
run (Lift f) = f
run (Compose (Knot f) g) = trace (f . untrace (run g))
run (Compose f g) = run f . run g
run (Knot k) = trace k

(⊢) :: x ↝ y -> x -> y
(⊢) = run
