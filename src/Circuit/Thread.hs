{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}

-- | The knot-body category and its cartesian instance.
--
-- This is the crystal from which the unification thesis is built:
--
-- @
--   Thread t arr s a b  =  arr (t s a) (t s b)
--   SArr s a b          =  Thread (,) (->) s a b
-- @
--
-- 'Thread' is the category that 'Circuit.Loop.Knot' wraps before tracing.
-- Every other stateful view — 'Circuit.Poly.System', 'Circuit.Process.Machine',
-- 'Circuit.Ends.Med' — is a specialisation or projection of it.
module Circuit.Thread
  ( -- * Cartesian ambient-state arrow
    SArr (..),
    SomeSArr (..),
    runSomeSArr,

    -- * Knot-body category
    Thread (..),
    SomeThread (..),
    threadToLoop,
    threadToSArr,
    sArrToThread,

    -- * Loop as ambient-state arrow
    loopToSomeSArr,
    loopEitherToSomeSArr,
  )
where

import Circuit.Category (Category (..), Discrete (..), (.>))
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
  type Ob (SArr s) a = ()

  id :: SArr s a a
  id = SArr id
  {-# INLINE id #-}

  (.) :: SArr s b c -> SArr s a b -> SArr s a c
  SArr g . SArr f = SArr $ \(s, a) ->
    let (s', b) = f (s, a)
     in g (s', b)
  {-# INLINE (.) #-}

-- | @SArr s@ has trivial object constraints, so it is discrete.
instance Discrete (SArr s) where
  withOb x = x

-- | The knot-body category: morphisms @arr (t s a) (t s b)@ for a fixed
-- feedback/state type @s@, base arrow @arr@, and tensor @t@.
--
-- Composition is just @arr@ composition; no @Channel@, @Strength@, or @Traced@
-- structure is required. This is the category 'Circuit.Loop.Knot' hides before
-- tracing.
--
-- @SArr s = Thread (,) (->) s@ is the cartesian instance.
newtype Thread t arr s a b = Thread {runThread :: arr (t s a) (t s b)}

instance (Category arr) => Category (Thread t arr s) where
  type Ob (Thread t arr s) a = Ob arr (t s a)

  id :: forall a. (Ob arr (t s a)) => Thread t arr s a a
  id = Thread id
  {-# INLINE id #-}

  (.) :: forall a b c. (Ob arr (t s a), Ob arr (t s b), Ob arr (t s c)) => Thread t arr s b c -> Thread t arr s a b -> Thread t arr s a c
  Thread g . Thread f = Thread (g . f)
  {-# INLINE (.) #-}

-- | @Thread t arr s@ has the same discreteness as its base arrow.
instance (Discrete arr) => Discrete (Thread t arr s) where
  withOb @a = withOb @arr @(t s a)

-- | Cartesian instance: @SArr s@ is exactly @Thread (,) (->) s@.
sArrToThread :: SArr s a b -> Thread (,) (->) s a b
sArrToThread (SArr f) = Thread f

threadToSArr :: Thread (,) (->) s a b -> SArr s a b
threadToSArr (Thread f) = SArr f

-- | A 'Thread' with its state type hidden, for the same reason 'SomeSArr'
-- exists.
data SomeThread t arr a b where
  SomeThread :: s -> Thread t arr s a b -> SomeThread t arr a b

-- | Lift a knot body into a 'Loop' by hiding the state wire.
threadToLoop ::
  (Ob arr s, Ob arr (t s a), Ob arr (t s b)) =>
  Thread t arr s a b ->
  Loop t arr a b
threadToLoop (Thread f) = Knot f

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
