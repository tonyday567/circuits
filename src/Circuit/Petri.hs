-- | Ordinary Petri nets with fixed place and transition sets.
--
-- Places label the positions of a marking. Transition input and output arcs
-- are vectors in that same place order. Firing is atomic: an enabled
-- transition consumes all its inputs and produces all its outputs in one
-- step. No machine, tensor, timing, or stochastic semantics is implied.
--
-- >>> let net = PetriNet ["ready", "done"] [("finish", Transition [1,0] [0,1])]
-- >>> fire net "finish" (Marking [1,0])
-- Just (Marking {tokens = [0,1]})
-- >>> enabledTransitions net (Marking [0,1])
-- []
-- >>> reachable net (Marking [1,0])
-- [Marking {tokens = [0,1]},Marking {tokens = [1,0]}]
module Circuit.Petri
  ( PetriNet (..),
    Transition (..),
    Marking (..),
    enabled,
    enabledTransitions,
    fire,
    fireSequence,
    reachable,
  )
where

import Control.Monad (foldM)
import Data.List (sort)
import Data.Maybe (isJust)
import Numeric.Natural (Natural)

-- | A finite net. Arc vectors and markings use the order of 'netPlaces'.
data PetriNet p t = PetriNet
  { netPlaces :: [p],
    netTransitions :: [(t, Transition)]
  }
  deriving (Eq, Show)

-- | Tokens consumed and produced at every place, in net place order.
data Transition = Transition
  { consume :: [Natural],
    produce :: [Natural]
  }
  deriving (Eq, Ord, Show)

-- | A global token distribution, in net place order.
newtype Marking = Marking
  { tokens :: [Natural]
  }
  deriving (Eq, Ord, Show)

-- | Whether a named transition can fire. Unknown transitions and
-- dimension-mismatched arcs or markings are not enabled.
enabled :: (Eq t) => PetriNet p t -> t -> Marking -> Bool
enabled net name marking = isJust (fire net name marking)

-- | All transitions enabled at a marking, in declaration order.
enabledTransitions :: PetriNet p t -> Marking -> [t]
enabledTransitions net marking =
  [ name
  | (name, transition) <- netTransitions net,
    isJust (applyTransition net transition marking)
  ]

-- | Fire a named transition atomically, or return 'Nothing' when it is not
-- enabled.
fire :: (Eq t) => PetriNet p t -> t -> Marking -> Maybe Marking
fire net name marking =
  lookup name (netTransitions net) >>= \transition ->
    applyTransition net transition marking

-- | Fire transitions from left to right. The sequence fails at its first
-- disabled transition and returns no partial marking.
fireSequence :: (Eq t) => PetriNet p t -> [t] -> Marking -> Maybe Marking
fireSequence net names marking =
  foldM (\current name -> fire net name current) marking names

-- | Every marking reachable from an initial marking, sorted and without
-- duplicates. Cycles are visited once. This is exhaustive when the
-- reachability graph is finite; an unbounded net need not terminate.
reachable :: PetriNet p t -> Marking -> [Marking]
reachable net initial = sort (go [initial] [])
  where
    go [] seen = seen
    go (marking : rest) seen
      | marking `elem` seen = go rest seen
      | otherwise = go (successors marking ++ rest) (marking : seen)

    successors marking =
      [ next
      | (_, transition) <- netTransitions net,
        Just next <- [applyTransition net transition marking]
      ]

applyTransition :: PetriNet p t -> Transition -> Marking -> Maybe Marking
applyTransition net (Transition pre post) (Marking counts) =
  if validDimensions && and (zipWith (>=) counts pre)
    then Just (Marking (zipWith3 step counts pre post))
    else Nothing
  where
    width = length (netPlaces net)
    validDimensions =
      length counts == width
        && length pre == width
        && length post == width
    step available consumed produced = available - consumed + produced
