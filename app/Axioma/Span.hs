-- | Span oracles — finite spans as the residual-remembering rung.
module Axioma.Span
  ( spanTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Span (Span (..), composeS, identityS, pairs, presentS)
import Control.Category (id)
import Control.Monad (when)
import Prelude hiding (id, (.))

data Wire = W1 | W2 | W3 deriving (Eq, Show, Enum, Bounded)

data Pin = P1 | P2 deriving (Eq, Show, Enum, Bounded)

data Sig = Hi | Lo deriving (Eq, Show, Enum, Bounded)

data Bit = O | I deriving (Eq, Show, Enum, Bounded)

spL :: Wire -> Pin
spL = \case W1 -> P1; _ -> P2

spR :: Wire -> Sig
spR = \case W3 -> Hi; _ -> Lo

sp :: Span Pin Sig
sp = Span [W1, W2, W3] spL spR

sqR :: Pin -> Sig
sqR _ = Lo

sqL :: Pin -> Pin
sqL = id

isOptic ::
  (Eq a, Eq b) =>
  [x] ->
  (x -> y) ->
  (y -> a) ->
  (x -> a) ->
  (y -> b) ->
  (x -> b) ->
  Bool
isOptic xs h a s b t = all (\x -> a (h x) == s x && b (h x) == t x) xs

spanTopic :: Verbosity -> IO [Bool]
spanTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Span oracles"
  sequence
    [ checkV verbosity "identity left preserves pairs" $
        pairs (identityS [Hi, Lo] `composeS` sp) == pairs sp,
      checkV verbosity "identity right preserves pairs" $
        pairs (sp `composeS` identityS [P1, P2]) == pairs sp,
      checkV verbosity "presentS round-trips at the pairs view" $
        pairs (presentS sp) == pairs sp,
      checkV verbosity "isOptic rejects an apex map that fails the right triangle" $
        let h0 P1 = W1; h0 P2 = W3
         in not (isOptic [P1, P2] h0 spL sqL spR sqR),
      checkV verbosity "isOptic accepts an apex map that makes both triangles commute" $
        let h1 P1 = W1; h1 P2 = W2
         in isOptic [P1, P2] h1 spL sqL spR sqR,
      checkV verbosity "associativity of span composition" $
        let p :: Span Pin Bit
            p = Span [W1, W2, W3] spL (\case W1 -> O; W2 -> O; W3 -> I)
            q :: Span Bit Sig
            q =
              Span
                [P1, P2]
                (\case P1 -> O; P2 -> I)
                (\case P1 -> Lo; P2 -> Hi)
            r :: Span Sig ()
            r = Span [Hi, Lo] id (\_ -> ())
         in pairs ((r `composeS` q) `composeS` p)
              == pairs (r `composeS` (q `composeS` p))
    ]
