{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Stream algebra and coalgebra for token streams.
--
-- This module holds the neutral stream interface used by both parsers and
-- agents: 'Uncons' destructs a stream, 'Snoc' constructs one.  It knows nothing
-- about parse results, posts, or agents — only about streams @f@ of tokens
-- @s@.
module Circuit.Stream
  ( -- * Boundary result
    These (..),

    -- * Stream coalgebra
    Uncons (..),

    -- * Stream algebra (left construction dual)
    Cons (..),

    -- * Stream algebra (right construction dual)
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

-- | Stream coalgebra with explicit boundary.
--
-- @uncons [x] = This x@ announces the final element at extraction. The
-- 'nil' value is the stream-specific empty used to continue after a 'This'
-- result.
class Uncons f s where
  uncons :: f -> These s f
  nil :: f

-- | Stream algebra: construct a stream by prepending one token on the left.
--
-- This is the construction dual of 'Uncons'.  Together they let code move
-- back and forth between tokens and streams using the same coalgebra.
class Cons f s where
  -- | Prepend one token to the left of a stream.
  cons :: s -> f -> f
  -- | The empty stream.
  consNil :: f

-- | Stream algebra: construct a stream by appending one token on the right.
--
-- This is the right-handed dual of 'Uncons'.
class Snoc f s where
  -- | Append one token to the right of a stream.
  snoc :: f -> s -> f
  -- | The empty stream.
  snocNil :: f
