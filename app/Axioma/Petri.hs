-- | Finite Petri-net oracles, including the mutual-exclusion witness.
module Axioma.Petri
  ( petriTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Petri (Marking (..), PetriNet (..), Transition (..), enabledTransitions, fire, fireSequence, reachable)
import Data.List (sort)
import Data.Maybe (isNothing)

data Place = IdleA | IdleB | Lock | CritA | CritB
  deriving (Eq, Show)

data Change = EnterA | ExitA | EnterB | ExitB
  deriving (Eq, Show)

mutualExclusion :: PetriNet Place Change
mutualExclusion =
  PetriNet
    [IdleA, IdleB, Lock, CritA, CritB]
    [ (EnterA, Transition [1, 0, 1, 0, 0] [0, 0, 0, 1, 0]),
      (ExitA, Transition [0, 0, 0, 1, 0] [1, 0, 1, 0, 0]),
      (EnterB, Transition [0, 1, 1, 0, 0] [0, 0, 0, 0, 1]),
      (ExitB, Transition [0, 0, 0, 0, 1] [0, 1, 1, 0, 0])
    ]

initial, criticalA, criticalB, forbidden :: Marking
initial = Marking [1, 1, 1, 0, 0]
criticalA = Marking [0, 1, 0, 1, 0]
criticalB = Marking [1, 0, 0, 0, 1]
forbidden = Marking [0, 0, 0, 1, 1]

expected :: [Marking]
expected = [initial, criticalA, criticalB]

actual :: [Marking]
actual = reachable mutualExclusion initial

replaceTransition :: (Eq t) => t -> Transition -> PetriNet p t -> PetriNet p t
replaceTransition name replacement net =
  net
    { netTransitions =
        [ if current == name then (current, replacement) else (current, transition)
        | (current, transition) <- netTransitions net
        ]
    }

withoutLock :: PetriNet Place Change
withoutLock =
  replaceTransition EnterA (Transition [1, 0, 0, 0, 0] [0, 0, 0, 1, 0]) mutualExclusion

duplicatedLock :: PetriNet Place Change
duplicatedLock =
  replaceTransition EnterA (Transition [1, 0, 1, 0, 0] [0, 0, 1, 1, 0]) mutualExclusion

brokenExit :: PetriNet Place Change
brokenExit =
  replaceTransition ExitA (Transition [0, 0, 0, 1, 0] [1, 0, 0, 0, 0]) mutualExclusion

petriTopic :: Verbosity -> IO [Bool]
petriTopic verbosity =
  sequence
    [ checkV verbosity "petri firing is atomic and disabled firing fails" $
        fire mutualExclusion EnterA initial == Just criticalA
          && fire mutualExclusion ExitA criticalA == Just initial
          && isNothing (fire mutualExclusion EnterA criticalA),
      checkV verbosity "petri enabled transitions are exact at every expected marking" $
        enabledTransitions mutualExclusion initial == [EnterA, EnterB]
          && enabledTransitions mutualExclusion criticalA == [ExitA]
          && enabledTransitions mutualExclusion criticalB == [ExitB],
      checkV verbosity "petri mutual exclusion has exactly the three expected reachable markings" $
        actual == sort expected,
      checkV verbosity "petri both critical markings are reachable and simultaneous critical occupancy is not" $
        all (`elem` actual) [criticalA, criticalB]
          && forbidden `notElem` actual,
      checkV verbosity "petri exit restores the lock and a second enter cannot bypass it" $
        fireSequence mutualExclusion [EnterA, ExitA, EnterB] initial == Just criticalB
          && isNothing (fireSequence mutualExclusion [EnterA, EnterB] initial),
      checkV verbosity "petri falsifier: dropping lock inputs admits the forbidden marking" $
        fireSequence withoutLock [EnterA, EnterB] initial == Just forbidden,
      checkV verbosity "petri falsifier: duplicating the lock changes firing and admits the forbidden marking" $
        fire duplicatedLock EnterA initial /= fire mutualExclusion EnterA initial
          && fireSequence duplicatedLock [EnterA, EnterB] initial == Just forbidden,
      checkV verbosity "petri falsifier: miswiring exitA breaks the enter-exit-enter sequence" $
        isNothing (fireSequence brokenExit [EnterA, ExitA, EnterB] initial)
    ]
