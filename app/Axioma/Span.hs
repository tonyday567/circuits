-- | Span oracles — finite spans as the residual-remembering rung.
module Axioma.Span
  ( spanTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Machine (Step (..), moore, scan)
import Circuit.Span
  ( Span (..),
    bodyFromSpan,
    composeS,
    identityS,
    pairs,
    presentS,
    spanFromBody,
  )
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
              == pairs (r `composeS` (q `composeS` p)),
      -- Step-bridge oracles (use an injective left leg so the lookup is faithful)
      checkV verbosity "bodyFromSpan runs the span as a lookup body" $
        let sp0 = Span [W1, W2, W3] id spR
            Step f = bodyFromSpan sp0
            inputs = [W1, W2, W3]
         in snd (f (inputs, W1)) == spR W1
              && snd (f (inputs, W3)) == spR W3,
      checkV verbosity "spanFromBody recovers the pairs view" $
        let sp0 = Span [W1, W2, W3] id spR
            inputs = [W1, W2, W3]
            sp' = spanFromBody inputs (bodyFromSpan sp0)
         in pairs sp' == pairs sp0,
      checkV verbosity "bodyFromSpan runs the apex-list channel" $
        let sp0 = Span [W1, W2, W3] id spR
            inputs = [W1, W2, W3]
            Step f = bodyFromSpan sp0
            mac = moore (\a -> f (inputs, a)) (\(s, _) a' -> f (s, a')) snd
         in scan mac inputs == map spR [W1, W2, W3],
      checkV verbosity "span composition agrees with the step cascade on pairs" $
        let p :: Span Pin Bit
            p = Span [W1, W2, W3] spL (\case W1 -> O; W2 -> O; W3 -> I)
            q :: Span Bit Sig
            q =
              Span
                [P1, P2]
                (\case P1 -> O; P2 -> I)
                (\case P1 -> Lo; P2 -> Hi)
            inputs = map spL [W1, W2, W3]
            qInputs = [O, I]
            Step direct = bodyFromSpan (q `composeS` p)
            Step runQ = bodyFromSpan q
            Step runP = bodyFromSpan p
            cascaded :: Step (,) (,) ([Pin], [Bit]) ([Pin], [Bit]) (->) Pin Sig
            cascaded =
              Step $ \((chP, chQ), a) ->
                let (chP', b) = runP (chP, a)
                    (chQ', c) = runQ (chQ, b)
                 in ((chP', chQ'), c)
            Step cascadedFn =
              cascaded
         in all
              (\a -> snd (direct (inputs, a)) == snd (cascadedFn ((inputs, qInputs), a)))
              inputs
    ]
