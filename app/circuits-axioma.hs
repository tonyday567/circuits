module Main (main) where

import Axioma.BiK (biKTopic)
import Axioma.Common (Verbosity (..))
import Axioma.Container (containerTopic)
import Axioma.Effect (effectTopic)
import Axioma.GMachine (gMachineTopic)
import Axioma.Poles (polesTopic)
import Axioma.Pullback (pullbackTopic)
import Axioma.SemiTensor (semiTensorTopic)
import Axioma.Shared (sharedTopic)
import Axioma.Span (spanTopic)
import Axioma.These (theseTopic)
import Axioma.Traced (tracedTopic)
import Control.Category ((.))
import Options.Applicative
import Prelude hiding (id, (.))

data Topic
  = All
  | BiK
  | Container
  | GMachine
  | Effect
  | Poles
  | Pullback
  | Shared
  | SemiTensor
  | Span
  | These
  | Traced
  deriving (Show, Eq, Bounded, Enum)

topicName :: Topic -> String
topicName All = "all"
topicName BiK = "bik"
topicName Container = "container"
topicName GMachine = "gmachine"
topicName Effect = "effect"
topicName Poles = "poles"
topicName Pullback = "pullback"
topicName Shared = "shared"
topicName SemiTensor = "semitensor"
topicName Span = "span"
topicName These = "these"
topicName Traced = "traced"

topicDesc :: Topic -> String
topicDesc All = "run all topics"
topicDesc BiK = "BiK oracles: biaction category laws, the strength spend, and the Either bridge"
topicDesc Container = "Container oracles: fibred view, skeleton positions, flat/fibre bridges"
topicDesc GMachine = "GMachine oracles"
topicDesc Effect = "Effectful K IO and Trace (,) (K IO) oracles"
topicDesc Poles = "Poles oracles: write/read legs, closing, and leg-mapping"
topicDesc Pullback = "Pullback oracles: chain rule under feedback for cotangent nets"
topicDesc Shared = "Shared-medium scheduling, centrality, and Channel These oracles"
topicDesc SemiTensor = "SemiTensor oracles: Const, the forgetful semigroupoidal tensor"
topicDesc Span = "Finite-span equipment oracles"
topicDesc These = "These oracles: hand-written instances vs the derived (,) + Either reference"
topicDesc Traced = "Traced oracles: base structural laws and their composite spends"

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
runTopic BiK = biKTopic
runTopic Container = containerTopic
runTopic GMachine = gMachineTopic
runTopic Effect = effectTopic
runTopic Poles = polesTopic
runTopic Pullback = pullbackTopic
runTopic Shared = sharedTopic
runTopic SemiTensor = semiTensorTopic
runTopic Span = spanTopic
runTopic These = theseTopic
runTopic Traced = tracedTopic
runTopic All = error "runTopic All is handled by the dispatcher"

allTopics :: [Topic]
allTopics = [BiK, Container, Effect, GMachine, Poles, Pullback, Shared, SemiTensor, Span, These, Traced]

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
