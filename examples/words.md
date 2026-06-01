# words — a worked example

Counting word frequencies from a file, reporting the commons. A pipeline
built from named components, composed with Circuit's three constructors,
metered in one line.

Copy code blocks into the repl:

```
cabal repl circuits
```

## the circuit

```mermaid
flowchart TD
    B["Right ()"] --> C["init Map.empty"]
        C --> D{"hIsEOF ?"}
        D -->|"no"| E["hGetLine\nString"]
        E --> F["words\n[String]"]
        F --> G["map toLower\n[String] → [String]"]
        G --> H["filter (not . null)\n[String] → [String]"]
        H --> I["foldl' insertCount\nMap String Int → Map String Int"]
        I --> J["Left (new Map)"]
        J -.->|"feedback"| D

    D -->|"yes"| K["Map.toList\n[(String, Int)]"]
    K --> L["sortOn (Down . snd)\n[(String, Int)]"]
    L --> M["take 5\n[(String, Int)]"]
    M --> N["fmt: w ++ ': ' ++ show c\nString"]
    N --> O["unlines\nString"]
    O --> P["putStr\nIO ()"]
```

Ten named functions. Each can be tested in isolation, rearranged, or replaced.
The dashed edge is the feedback channel — the Knot constructor keeps it open
so stages can be inserted, metered, or inspected before the loop closes.

## components

Every function has one job. Paste any of these into the repl, feed it an
input, check the output.

```haskell
import Control.Arrow (Kleisli (..), runKleisli)
import Control.Category ((>>>))
import Data.Char (toLower)
import Data.List (sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Ord (Down (..))
import System.IO (Handle, IOMode (ReadMode), hGetLine, hIsEOF, withFile)

import Circuit

-- * loop body components (runs once per line)

hGetLineIO :: Handle -> IO String
hGetLineIO = hGetLine

splitWords :: String -> [String]
splitWords = words

lowerWords :: [String] -> [String]
lowerWords = map (map toLower)

noEmpties :: [String] -> [String]
noEmpties = filter (not . null)

insertCount :: Map String Int -> String -> Map String Int
insertCount acc w =
  Map.insertWith (+) w (1 :: Int) acc

foldCounts :: [String] -> Map String Int -> Map String Int
foldCounts = flip (foldl insertCount)

-- * output components

assocList :: Map String Int -> [(String, Int)]
assocList = Map.toList

sortFreq :: [(String, Int)] -> [(String, Int)]
sortFreq = sortOn (Down . snd)

topN :: Int -> [(String, Int)] -> [(String, Int)]
topN n = take n

fmtRow :: (String, Int) -> String
fmtRow (w, c) = w <> ": " <> show c

fmtTable :: [(String, Int)] -> String
fmtTable = unlines . map fmtRow
```

## the loop body

Compose the per-line components. This function is what the `Knot`
constructor wraps — it takes `Either state ()` and returns
`Either state result`, where `Left` means "more lines to read" and
`Right` means "done".

```haskell
loopBody
  :: Handle
  -> Either (Map String Int) ()
  -> IO (Either (Map String Int) (Map String Int))
loopBody h (Right ()) = loopBody h (Left Map.empty)
loopBody h (Left acc) = do
  eof <- hIsEOF h
  if eof
    then pure (Right acc)
    else do
      line <- hGetLineIO h
      let ws = line
            & splitWords
            & lowerWords
            & noEmpties
          acc' = foldCounts ws acc
      pure (Left acc')
```

The `Handle` is captured in the closure — it's available on every
iteration without riding the feedback channel. Only the accumulator
`Map String Int` loops back.

## the pipeline

Three constructors. `Knot` holds the loop open. `Lift` bookends it
with the format-and-print stage.

```haskell
wordPipeline
  :: Handle
  -> Circuit (Kleisli IO) Either () ()
wordPipeline h =
  Knot (Kleisli (loopBody h))
    >>> Lift (Kleisli $ \acc -> do
        let out = acc
              & assocList
              & sortFreq
              & topN 5
              & fmtTable
        putStr out
      )
```

## running it

```haskell
wordCount :: FilePath -> IO ()
wordCount path =
  withFile path ReadMode $ \h ->
    runKleisli (reify (wordPipeline h)) ()

-- >>> wordCount "other/alice.md"
-- the: 1523
-- and: 779
-- to: 720
-- a: 616
-- she: 501
```

`withFile` handles resource bracketing here. circuits-io lifts this pattern into the circuit itself — `openFile` and `hClose` become Lift stages with bracket semantics, so resource lifecycle is composed rather than wrapped.

## metering

With circuits-meter, timing is a one-liner. Wrap each `Lift` stage with
`meterIO` and the diagram gains a column:

```mermaid
flowchart TD
    B["Right ()"] --> C["init Map.empty"]
        C --> D{"hIsEOF ? ⏱ 0.1ms"}
        D -->|"no"| E["hGetLine ⏱ 1.2ms"]
        E --> F["words ⏱ 0.01ms"]
        F --> G["map toLower ⏱ 0.02ms"]
        G --> H["filter (not . null) ⏱ 0.01ms"]
        H --> I["foldl' insertCount ⏱ 0.05ms"]
        I --> J["Left"]
        J -.->|"feedback"| D

    D -->|"yes"| K["Map.toList ⏱ 0.01ms"]
    K --> L["sortOn Down ⏱ 0.1ms"]
    L --> M["take 5 "]
    M --> N["fmtRow"]
    N --> O["unlines"]
    O --> P["putStr ⏱ total: 62ms"]
```

The code change is wrapping each component:

```haskell
-- import Circuit.Meter.Time (meterIO)

meteredLine :: Kleisli IO Handle String
meteredLine = meterIO (Kleisli hGetLineIO)

-- then use meteredLine in place of hGetLineIO inside loopBody
```

For wall-clock timing of the entire pipeline:

```haskell
-- (wall, ()) <- runKleisli (reify (meterIO wordPipeline)) h
-- putStrLn $ show (fromIntegral wall / 1e6) <> " ms"
```

Every component can be metered independently — the Circuit structure
makes it obvious where to insert measurement.

## references

- [circuits](../readme.md) — the library
- [circuits-parser](https://github.com/tonyday567/circuits-parser) — parser combinators
- [circuits-io](https://github.com/tonyday567/circuits-io) — resource management and queues
- [circuits-meter](https://github.com/tonyday567/circuits-meter) — performance measurement
