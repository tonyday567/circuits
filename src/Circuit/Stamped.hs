-- | A value together with an occurrence token — the core residue of a stamp.
--
-- The token @r@ is metadata: it labels the value but is never part of the
-- value's payload.  The defining law is the free theorem for 'fmap': mapping
-- over the payload cannot change the stamp.
--
-- This is the generic form.  The agent-side @Stamped@ in
-- @Circuit.Agent.Framing@ is the specialisation to bus posts, where the stamp
-- is a @(UTCTime, PostId)@ pair and the payload is a @Post a@.
module Circuit.Stamped
  ( Stamped (..),
  )
where

import Data.Bifunctor (Bifunctor (..))

-- $setup
-- >>> import Circuit.Stamped

-- | A value @a@ labelled by an occurrence token @r@.
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
data Stamped r a = Stamped
  { -- | Occurrence token / receipt.  Not touched by 'fmap'.
    stamp :: r,
    -- | The labelled payload.
    stamped :: a
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Bifunctor Stamped where
  bimap f g (Stamped r a) = Stamped (f r) (g a)
