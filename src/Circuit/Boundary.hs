{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

-- | The free boundary @K + payload@.
--
-- A token on the boundary is either a mark from a finite alphabet @k@ or a
-- payload value @a@.  This is the level-0 grammar of process boundaries and
-- stamping offices: marks are the control tokens, payloads are the data.
module Circuit.Boundary
  ( Boundary (..),
    isMark,
    isPayload,

    -- * Stamped values
    Stamped (..),

    -- * Linearity marks
    Linear (..),
    IsLinear,
    NotLinear,
  )
where

import Data.Bifunctor (Bifunctor (..))

-- $setup
-- >>> import Circuit.Boundary

-- | A single boundary token: either a mark from @k@ or a payload of @a@.
--
-- This is the additive disjunction @k ⊕ a@ at the boundary: every token is
-- /tagged/ as one or the other.  'fmap' acts only on the payload side; marks
-- are carried through unchanged.
--
-- >>> fmap length (Payload "hi")
-- Payload 2
-- >>> fmap length (Mark "halt")
-- Mark "halt"
data Boundary k a
  = -- | Control token from the finite mark alphabet.
    Mark k
  | -- | Data-carrying payload.
    Payload a
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Bifunctor Boundary where
  bimap f _ (Mark k) = Mark (f k)
  bimap _ g (Payload a) = Payload (g a)

-- | True iff the token is a 'Mark'.
isMark :: Boundary k a -> Bool
isMark (Mark _) = True
isMark (Payload _) = False

-- | True iff the token is a 'Payload'.
isPayload :: Boundary k a -> Bool
isPayload (Mark _) = False
isPayload (Payload _) = True

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

-- ---------------------------------------------------------------------------
-- Linearity marks
-- ---------------------------------------------------------------------------

-- | A compile-time marker that a payload is linear: it must be used exactly
-- once and cannot be silently copied or discarded.
--
-- Wrapping a value in 'Linear' changes its type-level 'IsLinear' status to
-- @'True@.  Combinators that need to copy, discard, or swap a payload should
-- require 'NotLinear'.
--
-- The intended use is for quantifier-swap operations such as a future
-- @SwapQ@: a channel carrying @Linear a@ will refuse @SwapQ@ at compile
-- time because 'Linear a' does not satisfy 'NotLinear'.
newtype Linear a = Linear {unLinear :: a}
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | Type-level predicate: is this type marked linear?
type family IsLinear a :: Bool where
  IsLinear (Linear _) = 'True
  IsLinear _ = 'False

-- | Constraint that a type is not marked linear.
--
-- Copy/discard/swap combinators should require this on their payload.
type NotLinear a = IsLinear a ~ 'False
