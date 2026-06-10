{-# LANGUAGE CPP #-}

-- | Reverse-mode automatic differentiation via a lens-shaped base arrow.
--
-- 'D' is a differentiable function @a -> b@ that carries its own pullback:
-- given a cotangent @db@ on the output, produce a cotangent @da@ on the input.
-- This is the same shape as Conal Elliott's \"Simple Essence of AD\" reverse
-- mode, lifted into a 'Category' so it can be used as the base arrow for
-- 'Circuit'.
--
-- With the 'Trace' @(,)@ instance, 'reify' \"Circuit D\" runs forward and
-- pulls back — reverse-mode AD with no GADT changes.  The backward pass
-- through a 'Knot' uses a lazy fixpoint (the implicit function theorem):
-- the gradient at a fixed point solves its own affine equation.
--
-- = Example
--
-- Differentiating @x²@ through a circuit:
--
-- >>> let f = Lift (D (\x -> (x * x, \dx' -> 2 * x * dx'))) :: Circuit D (,) Double Double
-- >>> let (y, pullback) = runD (reify f) 3.0
-- >>> y
-- 9.0
-- >>> pullback 1.0
-- 6.0
module Circuit.AD
  ( -- * Differentiable arrow
    D (..),
  )
where

#ifdef __GLASGOW_HASKELL__
import Control.Category
#else
import Circuit.Classes
#endif

import Circuit.Traced (Trace (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit (Circuit (..), reify)
-- >>> import Prelude hiding (id, (.))

-- | A reverse-mode differentiable function.
--
-- @runD f a@ returns a pair @(b, pullback)@ where @b = f a@ and @pullback@
-- maps a cotangent @db@ on the output to a cotangent @da@ on the input.
newtype D a b = D
  { -- | Run the forward pass and return the backward pullback.
    runD :: a -> (b, b -> a)
  }

instance Category D where
  id = D (\a -> (a, id))
  D f . D g = D $ \a ->
    let (b, gb) = g a
        (c, fc) = f b
     in (c, gb . fc)

-- | 'Trace' for 'D' with the @(,)@ tensor.
--
-- The forward pass ties the standard lazy knot:
--
-- @
-- let (a, c) = body (a, b) in c
-- @
--
-- The backward pass ties an /affine/ fixpoint on the channel cotangent.
-- Given @dc@ on the output, the channel cotangent @da@ satisfies:
--
-- @
-- da = fst (backward (da, dc))
-- @
--
-- where @backward@ is the pullback of @body@.  This is the implicit function
-- theorem in operation: the gradient at a fixed point solves its own affine
-- equation.  For linear backward maps (the common case), this is a Neumann
-- series computed lazily.
instance Trace D (,) where
  trace (D body) = D $ \b ->
    let -- Forward: standard lazy knot
        ~((a, c), backward) = body (a, b)
        -- Backward: affine fixpoint on channel cotangent
        pullback dc =
          let da = fst (backward (da, dc))
           in snd (backward (da, dc))
     in (c, pullback)

  untrace (D f) = D $ \(a, b) ->
    let (c, back) = f b
     in ((a, c), \(da, dc) -> (da, back dc))
