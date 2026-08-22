{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}

-- | Occurrence-tokens for values.
--
-- A 'Stamped' value pairs an occurrence token (a /stamp/) with a payload.
-- The stamp is an observation receipt: an id, a timestamp, a line number,
-- or any other token that names the occurrence without changing the
-- payload's meaning.
--
-- === Free theorem
--
-- The stamp is untouched by payload mapping:
--
-- @
-- stamp (fmap f s) = stamp s
-- stamped (fmap f s) = f (stamped s)
-- @
--
-- >>> let s = Stamped 42 "hello"
-- >>> stamp (fmap reverse s)
-- 42
-- >>> stamped (fmap reverse s)
-- "olleh"
module Circuit.Stamped
  ( Stamped (..),
  )
where

import Data.Bifunctor (Bifunctor (..))

-- | A value @a@ labelled by an occurrence token @r@.
data Stamped r a = Stamped
  { -- | Occurrence token / receipt.  Not touched by 'fmap'.
    stamp :: r,
    -- | The labelled payload.
    stamped :: a
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Bifunctor Stamped where
  bimap f g (Stamped r a) = Stamped (f r) (g a)
