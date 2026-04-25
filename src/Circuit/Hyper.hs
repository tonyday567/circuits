{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Hyperfunctions: the final encoding of traced monoidal categories.
--
-- A Hyper is a Church encoding of a Circuit. The feedback channel is
-- structural in the type rather than explicit, so the sliding axiom
-- is inherent to composition rather than enforced by pattern matching.

module Circuit.Hyper
  ( Hyper (..),

    -- * Core operations
    run,
    base,
    lift,
    push,

    -- * Interpretation
    lower,
  )
where

import Control.Category (Category (..), id)
import Prelude hiding (id, (.))

-- | Hyper a b is a hyperfunction from a to b.
--
-- Defined as a function that invokes its own dual to produce a value.
-- The self-referential duality unifies the forward and backward directions
-- through a single continuation argument.
newtype Hyper a b = Hyper {invoke :: Hyper b a -> b}

instance {-# OVERLAPPING #-} Category Hyper where
  id = lift id
  f . g = Hyper $ \h -> invoke f (g . h)

-- | Tie the knot on the diagonal: run a hyperfunction of type (a ↬ a) to get a value of type a.
--
-- This closes the feedback loop by invoking the hyperfunction with itself
-- repackaged as a continuation. The recursive definition:
--
-- > run h = invoke h (Hyper run)
--
-- creates the self-referential fixed point at the heart of coinductive hyperfunction semantics.
run :: Hyper a a -> a
run h = invoke h (Hyper run)

-- | Lift a constant into a hyperfunction.
--
-- > base a = Hyper (const a)
--
-- The resulting hyperfunction ignores its continuation and always returns the constant.
base :: a -> Hyper b a
base a = Hyper (const a)

-- | Embed a plain function into a hyperfunction.
--
-- Defined recursively by prepending to itself:
--
-- > lift f = push f (lift f)
--
-- This unfolds the function application lazily, supporting arbitrary recursion depth.
lift :: (a -> b) -> Hyper a b
lift f = push f (lift f)

-- | Prepend a function to a hyperfunction (push in the stack).
--
-- > push f h = Hyper (\k -> f (invoke k h))
--
-- This threads the continuation through the prepended function,
-- allowing feedback-aware composition of functions.
push :: (a -> b) -> Hyper a b -> Hyper a b
push f h = Hyper (\k -> f (invoke k h))

-- | Observe a hyperfunction by supplying it with a constant continuation.
--
-- > lower h a = invoke h (base a)
--
-- This extracts a plain function from a hyperfunction by asking:
-- "what output do you produce when the feedback channel feeds back
-- the constant input a?"
lower :: Hyper a b -> (a -> b)
lower h a = invoke h (base a)
