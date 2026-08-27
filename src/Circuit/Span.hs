-- | Finite spans as the residual-remembering rung of the equipment ladder.
--
-- A span @A ←s— X —t→ B@ is two functions out of a shared apex @X@.  In the
-- equipment-optics story the apex is the residual of the interface.  In
-- "Span" equipments that residual is remembered on the nose: composition is a
-- pullback of apexes, and an optic between spans is just an apex map
-- commuting with the legs.  In @circuits@ the same shape appears as
-- @Body t ch arr a b@, with the channel @ch@ playing the role of the apex.
module Circuit.Span
  ( Span (..),
    pairs,
    companion,
    conjoint,
    composeS,
    identityS,
    presentS,
  )
where

import Control.Category (id, (.))
import Prelude hiding (id, (.))

-- | A finite span with apex @x@ hidden existentially.
--
-- The apex must be 'Eq' so that pullback composition is computable.  Unlike
-- the relation view, the apex is part of the value: two spans with the same
-- boundary relation but different apexes are different spans.  This is the
-- "residual remembered on the nose" rung of the ladder.
data Span a b = forall x. (Eq x) => Span [x] (x -> a) (x -> b)

-- | View a span as its list of boundary pairs.  This forgets the apex; the
-- 'Eq' on the returned list is the relation-level view (the Rel rung).
instance (Show a, Show b) => Show (Span a b) where
  show = show . pairs

-- | Forget the apex and return the boundary pairs.
pairs :: Span a b -> [(a, b)]
pairs (Span xs s t) = [(s x, t x) | x <- xs]

-- | The companion of a function: its graph read forward.
--
-- @companion xs f@ is the span @A ←id— A —f→ B@.
companion :: (Eq a) => [a] -> (a -> b) -> Span a b
companion xs f = Span xs id f

-- | The conjoint of a function: its graph read backward.
--
-- @conjoint xs f@ is the span @B ←f— A —id→ A@.
conjoint :: (Eq a) => [a] -> (a -> b) -> Span b a
conjoint xs f = Span xs f id

-- | Pullback composition of spans.  The new apex is the set of pairs that
-- agree on the shared boundary.
composeS :: (Eq b) => Span b c -> Span a b -> Span a c
composeS (Span ys h k) (Span xs f g) =
  Span [(x, y) | x <- xs, y <- ys, g x == h y] (\(x, _) -> f x) (\(_, y) -> k y)

-- | The identity span on a finite type, given by its enumeration.
identityS :: (Eq a) => [a] -> Span a a
identityS xs = companion xs id

-- | Present a span as its own two legs: @⟨s,t⟩ = s* ⊙ t_*@.
--
-- The result has the same boundary pairs as the original, but its apex is
-- the diagonal pulled back along identity — the same span up to apex
-- isomorphism, never up to quotient.
presentS :: Span a b -> Span a b
presentS (Span xs s t) = composeS (companion xs t) (conjoint xs s)
