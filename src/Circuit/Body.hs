{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The knot-body category and its cartesian instance.
--
-- This is the crystal from which the unification thesis is built:
--
-- @
--   Body t arr s a b  =  arr (t s a) (t s b)
--   SArr s a b        =  Body (,) (->) s a b
-- @
--
-- 'Body' is the category that 'Circuit.Loop.Knot' wraps before tracing.
-- Every other stateful view — 'Circuit.Poly.System', 'Circuit.Process.Process',
-- 'Circuit.Ends.Med' — is a specialisation or projection of it.
module Circuit.Body
  ( -- * Cartesian ambient-state arrow
    SArr (..),
    SomeSArr (..),
    runSomeSArr,

    -- * Knot-body category
    Body (..),
    SomeBody (..),
    bodyToLoop,
    bodyToSArr,
    sArrToBody,

    -- * Loop as ambient-state arrow
    loopToSomeSArr,
    loopEitherToSomeSArr,
  )
where

import Circuit.Category (Category (..), (.>))
import Circuit.Layer (run)
import Circuit.Loop (Loop (..))
import Data.Bifunctor (second)
import Prelude hiding (id, (.))

-- | The ambient-state arrow: a morphism that threads a state wire @s@.
--
-- This is the cartesian instance of the knot-body category. Composition
-- threads the state sequentially.
newtype SArr s a b = SArr {runSArr :: (s, a) -> (s, b)}

instance Category (SArr s) where
  id :: SArr s a a
  id = SArr id
  {-# INLINE id #-}

  (.) :: SArr s b c -> SArr s a b -> SArr s a c
  SArr g . SArr f = SArr $ \(s, a) ->
    let (s', b) = f (s, a)
     in g (s', b)
  {-# INLINE (.) #-}

-- | The knot-body category: morphisms @arr (t s a) (t s b)@ for a fixed
-- feedback/state type @s@, base arrow @arr@, and tensor @t@.
--
-- Composition is just @arr@ composition; no @Channel@, @Strength@, or @Traced@
-- structure is required. This is the category 'Circuit.Loop.Knot' hides before
-- tracing.
--
-- @SArr s = Body (,) (->) s@ is the cartesian instance.
newtype Body t arr s a b = Body {runBody :: arr (t s a) (t s b)}

instance (Category arr) => Category (Body t arr s) where
  id :: forall a. Body t arr s a a
  id = Body id
  {-# INLINE id #-}

  (.) :: forall a b c. Body t arr s b c -> Body t arr s a b -> Body t arr s a c
  Body g . Body f = Body (g . f)
  {-# INLINE (.) #-}

-- | Cartesian instance: @SArr s@ is exactly @Body (,) (->) s@.
sArrToBody :: SArr s a b -> Body (,) (->) s a b
sArrToBody (SArr f) = Body f

bodyToSArr :: Body (,) (->) s a b -> SArr s a b
bodyToSArr (Body f) = SArr f

-- | A 'Body' with its state type hidden, for the same reason 'SomeSArr'
-- exists.
data SomeBody t arr a b where
  SomeBody :: s -> Body t arr s a b -> SomeBody t arr a b

-- | Lift a knot body into a 'Loop' by hiding the state wire.
bodyToLoop ::
  Body t arr s a b ->
  Loop t arr a b
bodyToLoop (Body f) = Knot f

-- | An existentially-quantified ambient-state arrow.
--
-- This is the packing that lets us treat a 'Process' as a value of the form
-- @exists s. SArr s a b@.
data SomeSArr a b where
  SomeSArr :: s -> SArr s a b -> SomeSArr a b

-- | Run an existentially-packed stateful arrow over a list of inputs.
runSomeSArr :: SomeSArr a b -> [a] -> [b]
runSomeSArr (SomeSArr s0 (SArr f)) xs =
  let (_, bs) = foldl (\(s, acc) a -> let (s', b) = f (s, a) in (s', b : acc)) (s0, []) xs
   in reverse bs

-- | View a 'Loop (,) (->)' as an existentially-quantified 'SArr'.
--
-- The hidden feedback channel of the loop becomes the ambient unit state of the
-- 'SArr'; the runner is just 'run' on the underlying traced category.
loopToSomeSArr :: Loop (,) (->) a b -> SomeSArr a b
loopToSomeSArr loop = SomeSArr () $ SArr $ second (run loop)

-- | View a 'Loop Either (->)' as an existentially-quantified 'SArr'.
--
-- Same idea as 'loopToSomeSArr' for the iteration tensor: the loop is
-- interpreted into functions, then wrapped in a trivial ambient state.
loopEitherToSomeSArr :: Loop Either (->) a b -> SomeSArr a b
loopEitherToSomeSArr loop = SomeSArr () $ SArr $ second (run loop)
