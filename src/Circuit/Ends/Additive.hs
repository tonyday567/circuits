-- | Additive connectives on 'Circuit.Ends.Ends'.
--
-- These combinators lift the additive conjunction @&@ and additive
-- disjunction @⊕@ to channel ends.  The schedule bias of the disjunctive
-- combinators is explicit in the term ("left first" vs "right first")
-- rather than being silently baked into the implementation.
module Circuit.Ends.Additive
  ( -- * Additive conjunction (with / await)
    pairEnds,

    -- * Additive disjunction (plus / race)
    Bias (..),
    IsSilent (..),
    HasSilent (..),
    raceEnds,
    raceMediator,

    -- * Structural helpers
    CartesianPar (..),
  )
where

import Circuit.Dagger (CopyDiscard (..))
import Circuit.Ends (Ends (..), ends0, splay0)
import Circuit.Mediate (Mediator (..))
import Control.Arrow (Kleisli (..))
import Data.Maybe (isNothing)
import Data.Void (Void)
import Prelude

-- $setup
-- >>> import Circuit.Ends
-- >>> import Circuit.Ends.Additive
-- >>> import Circuit.Layer (run)

-- | Parallel product of two morphisms on a pair.
--
-- This is the cartesian product, renamed from 'Par' to avoid collision with
-- the multiplicative disjunction 'Circuit.Par.Par'.
class CartesianPar arr where
  parP :: arr a b -> arr c d -> arr (a, c) (b, d)

instance CartesianPar (->) where
  parP f g (x, y) = (f x, g y)

instance (Monad m) => CartesianPar (Kleisli m) where
  parP (Kleisli f) (Kleisli g) = Kleisli $ \(x, y) -> (,) <$> f x <*> g y

-- | Values that can be tested for silence.
class IsSilent b where
  -- | True iff the value is silent.
  isSilent :: b -> Bool

instance IsSilent [a] where
  isSilent = null

instance IsSilent (Maybe a) where
  isSilent = isNothing

instance IsSilent Void where
  isSilent = const True

-- | Values that carry a canonical silent value.
class (IsSilent b) => HasSilent b where
  -- | The canonical silent value.
  silent :: b

instance HasSilent [a] where
  silent = []

instance HasSilent (Maybe a) where
  silent = Nothing

-- | Schedule bias for disjunctive composition.
data Bias = LeftFirst | RightFirst
  deriving (Eq, Show)

-- | Additive conjunction: both sub-ends receive the same input and their
-- outputs are paired.
--
-- This is the @&@ connective / 'await' fragment: every branch sees the
-- input, and the composite emits all of their results.
--
-- >>> let e1 = ends0 (const ()) (const 1 :: () -> Int) :: Ends (->) () Int
-- >>> let e2 = ends0 (const ()) (const 2 :: () -> Int) :: Ends (->) () Int
-- >>> run (box @(,) (pairEnds e1 e2)) ()
-- (1,2)
pairEnds ::
  (CopyDiscard (->) a) =>
  Ends (->) a b ->
  Ends (->) a c ->
  Ends (->) a (b, c)
pairEnds e1 e2 =
  let (w1, r1) = splay0 e1
      (w2, r2) = splay0 e2
      w = discard . parP w1 w2 . copy
      r = parP r1 r2 . copy
   in ends0 w r

-- | Additive disjunction / race: both sub-ends receive the same input, but
-- only the first non-silent output (according to the bias) is emitted.
--
-- The bias is explicit in the term rather than silently left-biased.  The
-- picking logic is the additive disjunction mediator: a state machine whose
-- residual is the first non-silent value it has seen.
--
-- >>> let eL = ends0 (const ()) (const (Just 1)) :: Ends (->) () (Maybe Int)
-- >>> let eR = ends0 (const ()) (const (Just 2)) :: Ends (->) () (Maybe Int)
-- >>> run (box @(,) (raceEnds LeftFirst eL eR)) ()
-- Just 1
-- >>> run (box @(,) (raceEnds RightFirst eL eR)) ()
-- Just 2
raceEnds ::
  (CopyDiscard (->) a, IsSilent b) =>
  Bias ->
  Ends (->) a b ->
  Ends (->) a b ->
  Ends (->) a b
raceEnds bias e1 e2 =
  let (w1, r1) = splay0 e1
      (w2, r2) = splay0 e2
      w = discard . parP w1 w2 . copy
      r = pick bias . parP r1 r2 . copy
   in ends0 w r
  where
    pick LeftFirst (x, y) = if isSilent x then y else x
    pick RightFirst (x, y) = if isSilent y then x else y

-- | Additive disjunction as a mediator.
--
-- The residual is the first non-silent value seen.  Once set, every further
-- input is ignored and the chosen value is emitted repeatedly.  This is the
-- same picking logic as 'raceEnds', expressed in the @?@-policy vocabulary.
raceMediator :: (IsSilent b) => Bias -> Mediator (Maybe b) (b, b) b
raceMediator bias =
  Mediator Nothing $ \s (x, y) ->
    case s of
      Just z -> (Just z, Just z)
      Nothing ->
        let z = pick bias (x, y)
         in (Just z, Just z)
  where
    pick LeftFirst (x, y) = if isSilent x then y else x
    pick RightFirst (x, y) = if isSilent y then x else y
