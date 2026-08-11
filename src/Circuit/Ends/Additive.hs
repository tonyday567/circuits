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
    Silence (..),
    raceEnds,

    -- * Structural helpers
    Diag (..),
    Par (..),
  )
where

import Circuit.Ends (Ends (..), ends0, splay0)
import Control.Arrow (Kleisli (..))
import Data.Maybe (isNothing)
import Data.Void (Void)
import Prelude

-- $setup
-- >>> import Circuit.Ends
-- >>> import Circuit.Ends.Additive
-- >>> import Circuit.Layer (run)

-- | Cartesian diagonal: duplicate and discard values in the base arrow.
--
-- This is the structural fragment needed to share an input between two
-- additive branches without depending on the full bimonoid layer.
class Diag arr a where
  -- | Duplicate a value.
  copyA :: arr a (a, a)

  -- | Discard a value.
  discardA :: arr a ()

instance Diag (->) a where
  copyA x = (x, x)
  discardA _ = ()

instance (Monad m) => Diag (Kleisli m) a where
  copyA = Kleisli $ \x -> pure (x, x)
  discardA = Kleisli $ \_ -> pure ()

-- | Parallel product of two morphisms on a pair.
class Par arr where
  par :: arr a b -> arr c d -> arr (a, c) (b, d)

instance Par (->) where
  par f g (x, y) = (f x, g y)

instance (Monad m) => Par (Kleisli m) where
  par (Kleisli f) (Kleisli g) = Kleisli $ \(x, y) -> (,) <$> f x <*> g y

-- | Values that can be "silent" — the race combinators use silence as the
-- fallback signal.
class Silence b where
  -- | The canonical silent value.
  silent :: b

  -- | True iff the value is silent.
  isSilent :: b -> Bool

instance Silence [a] where
  silent = []
  isSilent = null

instance Silence (Maybe a) where
  silent = Nothing
  isSilent = isNothing

instance Silence Void where
  silent = error "silence: Void has no inhabitants"
  isSilent = const True

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
  Ends (->) a b ->
  Ends (->) a c ->
  Ends (->) a (b, c)
pairEnds e1 e2 =
  let (w1, r1) = splay0 e1
      (w2, r2) = splay0 e2
      w = discardA . par w1 w2 . copyA
      r = par r1 r2 . copyA
   in ends0 w r

-- | Additive disjunction / race: both sub-ends receive the same input, but
-- only the first non-silent output (according to the bias) is emitted.
--
-- The bias is explicit in the term rather than silently left-biased.
--
-- >>> let eL = ends0 (const ()) (const (Just 1)) :: Ends (->) () (Maybe Int)
-- >>> let eR = ends0 (const ()) (const (Just 2)) :: Ends (->) () (Maybe Int)
-- >>> run (box @(,) (raceEnds LeftFirst eL eR)) ()
-- Just 1
-- >>> run (box @(,) (raceEnds RightFirst eL eR)) ()
-- Just 2
raceEnds ::
  (Silence b) =>
  Bias ->
  Ends (->) a b ->
  Ends (->) a b ->
  Ends (->) a b
raceEnds bias e1 e2 =
  let (w1, r1) = splay0 e1
      (w2, r2) = splay0 e2
      w = discardA . par w1 w2 . copyA
      r = pick bias . par r1 r2 . copyA
   in ends0 w r
  where
    pick LeftFirst (x, y) = if isSilent x then y else x
    pick RightFirst (x, y) = if isSilent y then x else y
