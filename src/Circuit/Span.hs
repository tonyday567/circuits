module Circuit.Span
  ( Span (..),
    pairs,
    companionSpan,
    conjointSpan,
    composeS,
    identityS,
    presentS,
    refinesS,
    bodyFromSpan,
    spanFromBody,
    spanDistance,
  )
where

import Circuit.Category (id, (.))
import Circuit.GMachine (Stratum (..))
import Data.Maybe (fromMaybe)
import Prelude hiding (id, (.))

data Span a b = forall x. (Eq x) => Span [x] (x -> a) (x -> b)

instance (Show a, Show b) => Show (Span a b) where
  show = show . pairs

pairs :: Span a b -> [(a, b)]
pairs (Span xs s t) = [(s x, t x) | x <- xs]

companionSpan :: (Eq a) => [a] -> (a -> b) -> Span a b
companionSpan xs = Span xs id

conjointSpan :: (Eq a) => [a] -> (a -> b) -> Span b a
conjointSpan xs f = Span xs f id

composeS :: (Eq b) => Span b c -> Span a b -> Span a c
composeS (Span ys h k) (Span xs f g) =
  Span [(x, y) | x <- xs, y <- ys, g x == h y] (\(x, _) -> f x) (\(_, y) -> k y)

identityS :: (Eq a) => [a] -> Span a a
identityS xs = companionSpan xs id

presentS :: Span a b -> Span a b
presentS (Span xs s t) = composeS (companionSpan xs t) (conjointSpan xs s)

refinesS :: (Eq a, Eq b) => Span a b -> Span a b -> Bool
refinesS p q = all (`elem` pairs q) (pairs p)

bodyFromSpan :: (Eq a) => Span a b -> Stratum (,) [a] (->) a b
bodyFromSpan sp =
  Stratum $ \(ch, a) ->
    let b = fromMaybe (error "bodyFromSpan: input not in left leg") (lookup a (pairs sp))
     in (ch, b)

spanFromBody :: (Eq a) => [a] -> Stratum (,) [a] (->) a b -> Span a b
spanFromBody as (Stratum f) = Span as id (snd . f . (as,))

spanDistance ::
  (Ord d) =>
  d ->
  d ->
  (d -> d -> d) ->
  (a -> a -> d) ->
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
