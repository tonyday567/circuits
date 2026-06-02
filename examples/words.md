# words — a worked example

Counting word frequencies from a file, reporting the top 5. A pipeline built
from named components, composed with Circuit's three constructors, metered in
one line.

The full runnable source is in
[`words/app/Main.hs`](https://github.com/tonyday567/words/blob/main/app/Main.hs).

## the circuit

```mermaid
flowchart TD
    B["Right ()"] --> C["init Map.empty"]
        C --> D{"hIsEOF ? ⏱ <0.001ms"}
        D -->|"no"| E["hGetLine ⏱ <0.001ms"]
        E --> F["words ⏱ 0.002ms"]
        F --> G["map toLower ⏱ <0.001ms"]
        G --> H["filter (not . null) ⏱ <0.001ms"]
        H --> I["foldl' insertCount ⏱ 0.002ms"]
        I --> J["Left"]
        J -.->|"feedback"| D

    D -->|"yes"| K["Map.toList ⏱ <0.001ms"]
    K --> L["sortOn Down ⏱ 0.626ms"]
    L --> M["take 5"]
    M --> N["fmtRow"]
    N --> O["unlines"]
    O --> P["putStr ⏱ total: 0.008ms"]
```

Ten named functions. Each can be tested in isolation, rearranged, or replaced.
The dashed edge is the feedback channel — the `Knot` constructor keeps it open
so stages can be inserted, metered, or inspected before the loop closes.

Timings above are averaged per-line (or total for single-shot stages) from a
run against `other/alice.md`. The `timedRun` function at the bottom of this file
generates the diagram from real measurements.

## components

Every function has one job. Paste any of these into the repl, feed it an
input, check the output.

```haskell
import Circuit
import Circuit.Meter (meterAction)
import Circuit.Meter.Time (meterIO, Nanos, reifyC, timeM)
import Control.Arrow (Kleisli (..), runKleisli)
import Control.Category ((>>>))
import Control.DeepSeq (NFData, force)
import Control.Exception (evaluate)
import Data.Bool (bool)
import Data.Char (toLower)
import Data.List (sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Ord (Down (..))
import Numeric (showFFloat)
import System.IO (Handle, IOMode (ReadMode), hGetLine, hIsEOF, withFile)

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
insertCount acc w = Map.insertWith (+) w (1 :: Int) acc

foldCounts :: [String] -> Map String Int -> Map String Int
foldCounts = flip (foldl' insertCount)

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

No do-notation: only `>>=`, `bool`, `either`, and point-free composition.

```haskell
loopBody
  :: Handle
  -> Kleisli IO (Either (Map String Int) ()) (Either (Map String Int) (Map String Int))
loopBody h = Kleisli (either go (const (go Map.empty)))
  where
    go acc = hIsEOF h >>= bool (step acc) (pure (Right acc))
    step acc =
      runKleisli meteredHGetLine h
        >>= pure . Left . flip foldCounts acc . noEmpties . lowerWords . splitWords . snd
```

The `Handle` is captured in the closure — it's available on every
iteration without riding the feedback channel. Only the accumulator
`Map String Int` loops back.

## the pipeline

Three constructors. `Knot` holds the loop open. `Lift` bookends it
with the format-and-print stage. `>>>` composes them.

```haskell
wordPipeline
  :: Handle
  -> Circuit (Kleisli IO) Either () ()
wordPipeline h =
  Knot (loopBody h)
    >>> Lift (Kleisli (putStr . fmtTable . topN 5 . sortFreq . assocList))
```

## running it

`withFileC` lifts `withFile` into the circuit, so resource bracketing is
composed rather than wrapped around the outside.

```haskell
withFileC :: Trace (Kleisli IO) t => FilePath -> IOMode -> (Handle -> Circuit (Kleisli IO) t a b) -> Circuit (Kleisli IO) t a b
withFileC path mode f = Lift (Kleisli (\a -> withFile path mode (\h -> runKleisli (reify (f h)) a)))

wordCount :: FilePath -> IO ()
wordCount path = runKleisli (reify (withFileC path ReadMode wordPipeline)) ()
```

Expected output (run against `other/alice.md`):

```
the: 1614
and: 767
to: 706
a: 619
she: 518
```

## metering

### component-level

`meterIO` is polymorphic in the tensor `t`, so the same meter can be
lifted into `Either`-based `Knot` loops as well as `(,)` pipelines.  The
type application makes this explicit:

```haskell
meteredHGetLine :: Kleisli IO Handle (Nanos, String)
meteredHGetLine = reify (meterIO hGetLineIO :: Circuit (Kleisli IO) Either Handle (Nanos, String))
```

The loop body above uses `meteredHGetLine` in place of plain `hGetLine`.

### whole-pipeline

`meterAction timeM` builds a circuit that brackets an arrow with clock
reads. `reifyC` extracts the `Kleisli` using the cartesian tensor:

```haskell
perfTest :: FilePath -> IO ()
perfTest path = do
  (t, ()) <- runKleisli (reifyC (meterAction timeM (Kleisli (\_ -> wordCount path)))) ()
  let ms = fromIntegral t / 1_000_000 :: Double
  putStrLn $ " wall: " <> show ms <> " ms"
```

A typical run on `other/alice.md` reports ~32–36 ms wall time.

### instrumented run

For a per-stage breakdown, `timedRun` threads `TimingLog` through the
loop state (no `IORef`) and emits a mermaid diagram. The repeated
"meter and accumulate" pattern is factored into `meterIO'`, `meterPure'`,
and `meterList'`:

```haskell
data TimingLog = TimingLog
  { tIsEOF :: !Nanos,
    tHGetLine :: !Nanos,
    tWords :: !Nanos,
    tLower :: !Nanos,
    tFilter :: !Nanos,
    tFold :: !Nanos,
    tToList :: !Nanos,
    tSort :: !Nanos,
    tTake :: !Nanos,
    tFmt :: !Nanos,
    tPutStr :: !Nanos,
    nLinesRead :: !Int,
    nIterations :: !Int
  }

emptyLog :: TimingLog
emptyLog = TimingLog 0 0 0 0 0 0 0 0 0 0 0 0 0

meterIO' :: (a -> IO b) -> (TimingLog -> Nanos -> TimingLog) -> TimingLog -> a -> IO (TimingLog, b)
meterIO' f upd tlog a = do
  (t, b) <- runKleisli (reifyC (meterAction timeM (Kleisli f))) a
  pure (upd tlog t, b)

meterPure' :: (a -> b) -> (TimingLog -> Nanos -> TimingLog) -> TimingLog -> a -> IO (TimingLog, b)
meterPure' f upd tlog a = do
  (t, b) <- runKleisli (reifyC (meterAction timeM (Kleisli (evaluate . f)))) a
  pure (upd tlog t, b)

meterList' :: NFData b => (a -> [b]) -> (TimingLog -> Nanos -> TimingLog) -> TimingLog -> a -> IO (TimingLog, [b])
meterList' f upd tlog a = do
  (t, b) <- runKleisli (reifyC (meterAction timeM (Kleisli (evaluate . force . f)))) a
  pure (upd tlog t, b)

-- Loop body that carries TimingLog in the feedback state.
loopBodyLogged
  :: Handle
  -> Kleisli IO (Either (TimingLog, Map String Int) ()) (Either (TimingLog, Map String Int) (TimingLog, Map String Int))
loopBodyLogged h = Kleisli (either go (const (go (emptyLog, Map.empty))))
  where
    go (tlog, acc) = hIsEOF h >>= bool (step (tlog, acc)) (pure (Right (tlog, acc)))
    step (tlog, acc) = do
      (tlog, eof) <- meterIO' (\_ -> hIsEOF h) (\l t -> l { tIsEOF = tIsEOF l + t, nIterations = nIterations l + 1 }) tlog ()
      if eof
        then pure (Right (tlog, acc))
        else do
          (tlog, line) <- meterIO' (\_ -> hGetLine h) (\l t -> l { tHGetLine = tHGetLine l + t, nLinesRead = nLinesRead l + 1 }) tlog ()
          (tlog, ws) <- meterList' words (\l t -> l { tWords = tWords l + t }) tlog line
          (tlog, wsLower) <- meterList' (map (map toLower)) (\l t -> l { tLower = tLower l + t }) tlog ws
          (tlog, wsFiltered) <- meterList' (filter (not . null)) (\l t -> l { tFilter = tFilter l + t }) tlog wsLower
          (tlog, acc') <- meterPure' (flip foldCounts acc) (\l t -> l { tFold = tFold l + t }) tlog wsFiltered
          pure (Left (tlog, acc'))

-- Post-processing stages, each metered and logging.
postProcess :: TimingLog -> Map String Int -> IO (TimingLog, String)
postProcess tlog m = do
  (tlog, list) <- meterPure' Map.toList (\l t -> l { tToList = tToList l + t }) tlog m
  (tlog, sorted) <- meterPure' (sortOn (Down . snd)) (\l t -> l { tSort = tSort l + t }) tlog list
  (tlog, top5) <- meterPure' (take 5) (\l t -> l { tTake = tTake l + t }) tlog sorted
  (tlog, output) <- meterPure' fmtTable (\l t -> l { tFmt = tFmt l + t }) tlog top5
  (tlog, ()) <- meterIO' putStr (\l t -> l { tPutStr = tPutStr l + t }) tlog output
  pure (tlog, output)

fmtMs :: Nanos -> String
fmtMs n =
  let ms = fromIntegral n / 1_000_000 :: Double
   in if ms < 0.001 then "<0.001ms" else showFFloat (Just 3) ms "ms"

avgMs :: Nanos -> Int -> String
avgMs t n = fmtMs (t `div` fromIntegral (max 1 n))

mermaidDiagram :: TimingLog -> String
mermaidDiagram l =
  let n = max 1 (nLinesRead l)
   in unlines
        [ "flowchart TD",
          "    B[\"Right ()\"] --> C[\"init Map.empty\"]",
          "        C --> D{\"hIsEOF ? ⏱ " <> avgMs (tIsEOF l) (nIterations l) <> "\"}",
          "        D -->|\"no\"| E[\"hGetLine ⏱ " <> avgMs (tHGetLine l) n <> "\"]",
          "        E --> F[\"words ⏱ " <> avgMs (tWords l) n <> "\"]",
          "        F --> G[\"map toLower ⏱ " <> avgMs (tLower l) n <> "\"]",
          "        G --> H[\"filter (not . null) ⏱ " <> avgMs (tFilter l) n <> "\"]",
          "        H --> I[\"foldl' insertCount ⏱ " <> avgMs (tFold l) n <> "\"]",
          "        I --> J[\"Left\"]",
          "        J -.->|\"feedback\"| D",
          "",
          "    D -->|\"yes\"| K[\"Map.toList ⏱ " <> fmtMs (tToList l) <> "\"]",
          "    K --> L[\"sortOn Down ⏱ " <> fmtMs (tSort l) <> "\"]",
          "    L --> M[\"take 5\"]",
          "    M --> N[\"fmtRow\"]",
          "    N --> O[\"unlines\"]",
          "    O --> P[\"putStr ⏱ total: " <> fmtMs (tPutStr l) <> "\"]"
        ]

timedRun :: FilePath -> IO ()
timedRun path = withFile path ReadMode $ \h -> do
  (tlog, result) <- runKleisli (trace (loopBodyLogged h)) ()
  (tlog', _) <- postProcess tlog result
  putStrLn (mermaidDiagram tlog')
```

## references

- [circuits](../readme.md) — the library
- [circuits-meter](https://github.com/tonyday567/circuits-meter) — performance measurement
