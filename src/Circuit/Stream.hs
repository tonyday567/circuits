{-# LANGUAGE AllowAmbiguousTypes #-}

module Circuit.Stream
  ( These (..),
    Uncons (..),
    Cons (..),
    Snoc (..),
  )
where

import Data.These (These (..))

instance Uncons [a] a where
  uncons [] = That []
  uncons [x] = This x
  uncons (x : xs) = These x xs
  nil = []

instance Cons [a] a where
  cons = (:)
  consNil = []

instance Snoc [a] a where
  snoc xs x = xs ++ [x]
  snocNil = []

class Uncons f s where
  uncons :: f -> These s f
  nil :: f

class Cons f s where
  cons :: s -> f -> f

  consNil :: f

class Snoc f s where
  snoc :: f -> s -> f

  snocNil :: f
