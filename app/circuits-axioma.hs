module Main (main) where

import Axioma.Channel (channelTopic)
import Axioma.Effect (effectTopic)
import Axioma.FinRel (finRelTopic)
import Axioma.Poles (polesTopic)
import Axioma.Process (processTopic)
import Axioma.Shared (sharedTopic)
import Options.Applicative
import Prelude hiding (id, (.))

data Topic
  = All
  | FinRel
  | Process
  | Poles
  | Shared
  | Effect
  | Channel
  deriving (Show, Eq, Bounded, Enum)

topicName :: Topic -> String
topicName All = "all"
topicName FinRel = "finrel"
topicName Process = "process"
topicName Poles = "poles"
topicName Shared = "shared"
topicName Effect = "effect"
topicName Channel = "channel"

topicDesc :: Topic -> String
topicDesc All = "run all topics"
topicDesc FinRel = "FinRel bimonoid, dagger, and trace oracles"
topicDesc Process = "Process, Mealy, Body, Trace, and Net oracles"
topicDesc Poles = "Poles, Stamped, Boundary, and markSystem oracles"
topicDesc Shared = "Shared-medium scheduling, centrality, and Channel These oracles"
topicDesc Effect = "Effectful K IO and Trace (,) (K IO) oracles"
topicDesc Channel = "Par / linear distributivity and Poly.Channel oracles"

topicParser :: Parser Topic
topicParser =
  subparser $
    foldr
      (<>)
      (commandGroup "Topics:")
      [ command
          (topicName t)
          (info (pure t <**> helper) (progDesc (topicDesc t)))
      | t <- [minBound .. maxBound],
        t /= All
      ]
      <> command
        "all"
        (info (pure All <**> helper) (progDesc (topicDesc All)))

opts :: ParserInfo Topic
opts =
  info
    (topicParser <**> helper)
    ( fullDesc
        <> progDesc "Run circuits oracles by topic"
        <> header "circuits-axioma — topic-selectable axiom oracles"
    )

runTopic :: Topic -> IO [Bool]
runTopic All = concat <$> mapM runTopic [FinRel, Process, Poles, Shared, Effect, Channel]
runTopic FinRel = finRelTopic
runTopic Process = processTopic
runTopic Poles = polesTopic
runTopic Shared = sharedTopic
runTopic Effect = effectTopic
runTopic Channel = channelTopic

main :: IO ()
main = do
  topic <- execParser opts
  results <- runTopic topic
  if and results
    then putStrLn "\nAll tests passed."
    else error "Some tests failed."
