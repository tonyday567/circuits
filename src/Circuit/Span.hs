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
    companionSpan,
    conjointSpan,
    composeS,
    identityS,
    presentS,

    -- * 2-cells between spans
    refinesS,

    -- * Body bridges
    bodyFromSpan,
    spanFromBody,
    someBodyFromSpan,

    -- * Metric optics
    spanDistance,
  )
where

import Circuit.Body (Body (..), SomeBody (..), runSomeBody)
import Control.Category (id, (.))
import Data.Maybe (fromMaybe)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Span
-- >>> import Control.Category (id)
-- >>> import Prelude hiding (id, (.))

-- | A finite span with apex @x@ hidden existentially.
--
-- The apex must be 'Eq' so that pullback composition is computable.  Unlike
-- the relation view, the apex is part of the value: two spans with the same
-- boundary relation but different apexes are different spans.  This is the
-- "residual remembered on the nose" rung of the ladder.
data Span a b = forall x. (Eq x) => Span [x] (x -> a) (x -> b)

-- | View a span as its list of boundary pairs.
--
-- Note that this deliberately forgets the apex, so two spans that are not
-- isomorphic can 'show' alike.  That is the Rel rung looking at a Span-rung
-- value, not an accident.
instance (Show a, Show b) => Show (Span a b) where
  show = show . pairs

-- | Forget the apex and return the boundary pairs.
pairs :: Span a b -> [(a, b)]
pairs (Span xs s t) = [(s x, t x) | x <- xs]

-- | The companionSpan of a function: its graph read forward.
--
-- @companionSpan xs f@ is the span @A ←id— A —f→ B@.
companionSpan :: (Eq a) => [a] -> (a -> b) -> Span a b
companionSpan xs = Span xs id

-- | The conjointSpan of a function: its graph read backward.
--
-- @conjointSpan xs f@ is the span @B ←f— A —id→ A@.
conjointSpan :: (Eq a) => [a] -> (a -> b) -> Span b a
conjointSpan xs f = Span xs f id

-- | Pullback composition of spans.  The new apex is the set of pairs that
-- agree on the shared boundary.
composeS :: (Eq b) => Span b c -> Span a b -> Span a c
composeS (Span ys h k) (Span xs f g) =
  Span [(x, y) | x <- xs, y <- ys, g x == h y] (\(x, _) -> f x) (\(_, y) -> k y)

-- | The identity span on a finite type, given by its enumeration.
identityS :: (Eq a) => [a] -> Span a a
identityS xs = companionSpan xs id

-- | Present a span as its own two legs: @⟨s,t⟩ = s* ⊙ t_*@.
--
-- The result has the same boundary pairs as the original, but its apex is
-- the diagonal pulled back along identity — the same span up to apex
-- isomorphism, never up to quotient.
presentS :: Span a b -> Span a b
presentS (Span xs s t) = composeS (companionSpan xs t) (conjointSpan xs s)

-- | Does a span 2-cell from the first span to the second exist?
--
-- A 2-cell is an apex map @h@ with @a . h = s@ and @b . h = t@.  Over finite
-- enumerations such an @h@ exists exactly when every boundary pair of the
-- source occurs in the target, so existence is decidable from the 'pairs'
-- view alone — no access to the apexes required.
--
-- This is the existence statement; checking a /given/ witness needs the
-- apexes and lives with the caller that built them.  The gap between the two
-- is the ladder: @refinesS@ is what the Rel rung can see, and it is strictly
-- less than the Span rung, which distinguishes non-isomorphic apexes with the
-- same pairs.
--
-- >>> let p = Span [1 :: Int, 2] id id :: Span Int Int
-- >>> let q = Span [1 :: Int, 2, 3] id id :: Span Int Int
-- >>> (refinesS p q, refinesS q p)
-- (True,False)
refinesS :: (Eq a, Eq b) => Span a b -> Span a b -> Bool
refinesS p q = all (`elem` pairs q) (pairs p)

-- * Body bridges

-- | View a finite span as a lookup body over the left-leg enumeration.
--
-- The channel is @[a]@ (the left-boundary values of the span) and the internal
-- computation selects the matching right-boundary value.  This is the Rel-rung
-- bridge: the original apex is forgotten, only the boundary pairs remain.
--
-- The result is partial on inputs that do not occur as a left leg; the caller
-- is responsible for supplying valid inputs.
bodyFromSpan :: (Eq a) => Span a b -> Body (,) [a] (->) a b
bodyFromSpan sp =
  Body $ \(ch, a) ->
    let b = fromMaybe (error "bodyFromSpan: input not in left leg") (lookup a (pairs sp))
     in (ch, b)

-- | Extract a span from a body whose channel is the left-leg enumeration.
--
-- The supplied list @as@ is taken as the apex; the left leg is the identity and
-- the right leg runs the body.  This is a partial inverse to 'bodyFromSpan' up
-- to the Rel-rung quotient (same 'pairs').
spanFromBody :: (Eq a) => [a] -> Body (,) [a] (->) a b -> Span a b
spanFromBody as (Body f) = Span as id (snd . f . (as,))

-- | View a finite span as a 'SomeBody' whose hidden channel is the apex list.
--
-- This is the Span-rung bridge: the apex list is carried as the body channel
-- and the internal computation looks up the input in the left leg.  The apex
-- type is hidden by the existential packaging.
someBodyFromSpan :: (Eq a) => Span a b -> SomeBody (,) (->) a b
someBodyFromSpan sp@(Span xs _ _) =
  SomeBody xs $ Body $ \(ch, a) ->
    let b = fromMaybe (error "someBodyFromSpan: input not in left leg") (lookup a (pairs sp))
     in (ch, b)

-- | Directed Hausdorff distance between two spans over a common boundary:
--
-- @
--   d((s,t),(a,b)) = sup_x inf_y [ d(s x, a y) + d(b y, t x) ]
-- @
--
-- The @sup@ ranges over the /domain/ apex and the @inf@ over the /codomain/
-- apex.  Those are not two spellings of the same thing: in
-- @([0,∞], ≥)@-enrichment limits are suprema and colimits are infima, so the
-- @sup@ is the end and the @inf@ is the coend.  This function is therefore
-- the general @∫_x ∫^y@ shape made concrete, not merely a metric analogue of
-- it — which is also why it cannot be written in a bare semiring: for the
-- tropical scalar the @inf@ is the semiring addition but the @sup@ belongs to
-- the dual semiring.
--
-- The two units are the degenerate cases and must be supplied:
--
-- * @bot@ is the value of a @sup@ over an empty domain apex (@0@ for a
--   tropical scalar) — a span with no apex points is distance @bot@ from
--   anything;
-- * @top@ is the value of an @inf@ over an empty codomain apex (@+∞@) —
--   nothing can be approximated by a span with no apex points.
--
-- Passing them explicitly is what keeps this total; folding with 'maximum'
-- and 'minimum' would throw on either empty enumeration.
--
-- >>> let dist x y = abs (fromIntegral x - fromIntegral y) :: Double
-- >>> let sA = Span [0 :: Int, 1] id id
-- >>> let sB = Span [0 :: Int] id id
-- >>> spanDistance 0 (1 / 0) (+) dist dist sA sA
-- 0.0
-- >>> spanDistance 0 (1 / 0) (+) dist dist sA sB
-- 2.0
--
-- The empty codomain apex is total, not an exception:
--
-- >>> spanDistance 0 (1 / 0) (+) dist dist sA (Span ([] :: [Int]) id id)
-- Infinity
spanDistance ::
  (Ord d) =>
  -- | @bot@: the supremum over an empty domain apex.
  d ->
  -- | @top@: the infimum over an empty codomain apex.
  d ->
  -- | Addition of the forward and backward costs.
  (d -> d -> d) ->
  -- | Distance on the left boundary.
  (a -> a -> d) ->
  -- | Distance on the right boundary.
  (b -> b -> d) ->
  Span a b ->
  Span a b ->
  d
spanDistance bot top add da db (Span xs s1 t1) (Span ys s2 t2) =
  foldr
    max
    bot
    [ foldr min top [add (da (s1 x) (s2 y)) (db (t2 y) (t1 x)) | y <- ys]
    | x <- xs
    ]
