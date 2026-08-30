module Main (main) where

import Axioma.Circ (circTopic)
import Axioma.Common (Verbosity (..))
import Axioma.Effect (effectTopic)
import Axioma.FinRel (finRelTopic)
import Axioma.Moore (mooreTopic)
import Axioma.Optic (opticTopic)
import Axioma.Poles (polesTopic)
import Axioma.Process (processTopic)
import Axioma.Shared (sharedTopic)
import Axioma.Span (spanTopic)
import Control.Category ((.))
import Options.Applicative
import Prelude hiding (id, (.))

data Topic
  = All
  | Circ
  | Moore
  | Effect
  | FinRel
  | Optic
  | Poles
  | Process
  | Shared
  | Span
  deriving (Show, Eq, Bounded, Enum)

topicName :: Topic -> String
topicName All = "all"
topicName Circ = "circ"
topicName Moore = "moore"
topicName Effect = "effect"
topicName FinRel = "finrel"
topicName Optic = "optic"
topicName Poles = "poles"
topicName Process = "process"
topicName Shared = "shared"
topicName Span = "span"

topicDesc :: Topic -> String
topicDesc All = "run all topics"
topicDesc Circ = "Circ bicategory and intertwiner oracles"
topicDesc Moore = "Moore machine oracles"
topicDesc Effect = "Effectful K IO and Trace (,) (K IO) oracles"
topicDesc FinRel = "FinRel bimonoid, dagger, and trace oracles"
topicDesc Optic = "Mixed equipment-optic oracles"
topicDesc Poles = "Poles, Stamped, Boundary, and markMoore oracles"
topicDesc Process = "Process, Mealy, Body, Trace, and Net oracles"
topicDesc Shared = "Shared-medium scheduling, centrality, and Channel These oracles"
topicDesc Span = "Finite-span equipment oracles"

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
runTopic Circ = circTopic
runTopic Moore = mooreTopic
runTopic Effect = effectTopic
runTopic FinRel = finRelTopic
runTopic Optic = opticTopic
runTopic Poles = polesTopic
runTopic Process = processTopic
runTopic Shared = sharedTopic
runTopic Span = spanTopic
runTopic All = error "runTopic All is handled by the dispatcher"

allTopics :: [Topic]
allTopics = [Circ, Effect, FinRel, Moore, Optic, Poles, Process, Shared, Span]

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
