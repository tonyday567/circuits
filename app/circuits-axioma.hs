module Main (main) where

import Axioma.Channel (channelTopic)
import Axioma.Common (Verbosity (..))
import Axioma.Effect (effectTopic)
import Axioma.FinRel (finRelTopic)
import Axioma.Poles (polesTopic)
import Axioma.Process (processTopic)
import Axioma.Shared (sharedTopic)
import Control.Category ((.))
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

verbosityParser :: Parser Verbosity
verbosityParser =
  option
    (eitherReader readVerbosity)
    ( long "verbosity"
        <> short 'v'
        <> metavar "LEVEL"
        <> value Axioms
        <> showDefault
        <> help "package | topic | axioms"
    )
  where
    readVerbosity "package" = Right Package
    readVerbosity "topic" = Right Topic
    readVerbosity "axioms" = Right Axioms
    readVerbosity other = Left ("unknown verbosity: " ++ other)

data Options = Options Topic Verbosity

optionsParser :: Parser Options
optionsParser = Options <$> topicParser <*> verbosityParser

opts :: ParserInfo Options
opts =
  info
    (optionsParser <**> helper)
    ( fullDesc
        <> progDesc "Run circuits oracles by topic"
        <> header "circuits-axioma — topic-selectable axiom oracles"
    )

runTopic :: Topic -> Verbosity -> IO [Bool]
runTopic FinRel = finRelTopic
runTopic Process = processTopic
runTopic Poles = polesTopic
runTopic Shared = sharedTopic
runTopic Effect = effectTopic
runTopic Channel = channelTopic
runTopic All = error "runTopic All is handled by the dispatcher"

allTopics :: [Topic]
allTopics = [FinRel, Process, Poles, Shared, Effect, Channel]

greenCircle :: String
greenCircle = "🟢"

redCircle :: String
redCircle = "🔴"

printCircle :: Bool -> IO ()
printCircle ok = putStr (if ok then greenCircle else redCircle)

runAxioms :: Topic -> IO ()
runAxioms topic = do
  results <- case topic of
    All -> concat <$> mapM (\t -> putStrLn ("=== " ++ topicName t ++ " ===") *> runTopic t Axioms) allTopics
    t -> runTopic t Axioms
  if and results
    then putStrLn "\nAll tests passed."
    else error "Some tests failed."

runTopicLevel :: Topic -> IO ()
runTopicLevel topic = do
  ok <- case topic of
    All -> do
      results <- mapM (\t -> (t,) <$> runTopic t Topic) allTopics
      mapM_ (\(t, rs) -> putStr (topicName t ++ " ") *> printCircle (and rs) *> putStrLn "") results
      pure (all (and . snd) results)
    t -> do
      results <- runTopic t Topic
      putStr (topicName t ++ " ")
      printCircle (and results)
      putStrLn ""
      pure (and results)
  putStrLn (if ok then "All tests passed." else "Some tests failed.")

runPackage :: Topic -> IO ()
runPackage topic = do
  results <- case topic of
    All -> concat <$> mapM (\t -> runTopic t Package) allTopics
    t -> runTopic t Package
  printCircle (and results)
  putStrLn ""

main :: IO ()
main = do
  Options topic verbosity <- execParser opts
  case verbosity of
    Axioms -> runAxioms topic
    Topic -> runTopicLevel topic
    Package -> runPackage topic
