{-# LANGUAGE ScopedTypeVariables #-}

-- | Core Channel and canonical Moore-runner oracles.
module Axioma.Machine
  ( machineTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Category (K (..), runK, (.>))
import Circuit.Channel (Body, Channel (..), Moore, Step (..), foldM, fuse, scanM)
import Circuit.Tensor (Const (..), unConst)
import Control.Exception (evaluate)
import Control.Monad (when)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import System.Timeout (timeout)

-- | A named 'Body' at the @(Const, (,))@ corner: 'commit' writes the
-- channel from the input alone (its length) — the @Const@ tick source
-- has no channel slot — and 'emit' emits the channel update alongside
-- the output. The leg types are chosen so the threading falsifier — a
-- step-2 commit reading step 1's emitted package — is a type error at
-- 'commit', not a silent carry.
memBody :: Body Const (,) Int Int (->) String Int
memBody = Channel (\(Const s) -> length s) (\ch -> (ch + 1, ch * 10))

-- | The two-step run, spelt out: each step commits its channel from its
-- own input alone; step 1's emitted package is bound and deliberately
-- dead. That dead binding is the memorylessness claim — a threading
-- runner would route it into step 2's commit.
twoStep :: Body Const (,) ch ch' (->) i o -> i -> i -> (o, o)
twoStep (Channel x g) i1 i2 =
  let (_c1', o1) = g (x (Const i1))
      (_c2', o2) = g (x (Const i2))
   in (o1, o2)

-- | Memorylessness, pinned by the run: step 2 is the fresh commit/emit
-- of @i2@ alone — swapping step 1's input changes step 1's output only.
-- The falsifier is any threading of the emitted channel into the next
-- commit: impossible at the @Const@-sourced leg's type, and the anchors
-- @(20, 40)@ vs @(30, 40)@ would break under any runner that carried
-- state forward.
threading :: Bool
threading =
  twoStep memBody "ab" "cdef" == (20, 40)
    && twoStep memBody "xyz" "cdef" == (30, 40)
    && snd (twoStep memBody "ab" "cdef") == fresh2
  where
    fresh2 = case memBody of
      Channel x g -> snd (g (x (Const "cdef")))

-- | A named 'Body' at the @(Const, Either)@ corner: 'commit' writes the
-- channel from the input alone; 'emit' evolves ('Left', the updated
-- channel) while the input is small and completes ('Right') once it is
-- not — the exit constructor a bare 'Moore' emit cannot say.
doneBody :: Body Const Either Int Int (->) Int Int
doneBody = Channel (\(Const i) -> i) (\ch -> if ch < 4 then Left (ch + 1) else Right ch)

-- | The 'Either' run: commit, emit, repeat. 'Left' logs the evolved
-- channel — never carried forward, per the @Const@ corner's
-- memorylessness — and the run continues; 'Right' terminates it, and
-- the remaining inputs are never committed.
runDone :: Body Const Either ch ch (->) i o -> [i] -> [Either ch o]
runDone (Channel x g) = go
  where
    go [] = []
    go (i : is) =
      let p = g (x (Const i))
       in p : case p of
            Left _ -> go is
            Right _ -> []

-- | Completion at the @(Const, 'Either')@ corner: an 'emit' returning
-- 'Right' terminates the run — @[Left 4, Right 5]@, the third input
-- never committed. The falsifier is a run that continues past the exit,
-- or reads the evolved channel back; either would break the anchor.
completion :: Bool
completion = runDone doneBody [3, 5, 7] == [Left 4, Right 5]

fusion :: Bool
fusion = case fuse memBody of
  Step f -> f (Const "abcd") == (5, 40)

slideCommit, slideEmit :: Body (,) Const Int Int (->) Int Int
slideCommit = Channel (uncurry (+) .> (* 10)) (Const . (+ 1))
slideEmit = Channel (uncurry (+)) ((* 10) .> (Const . (+ 1)))

linkSliding :: Bool
linkSliding = case (fuse slideCommit, fuse slideEmit) of
  (Step f, Step g) -> unConst (f (3, 4)) == 71 && unConst (f (3, 4)) == unConst (g (3, 4))

emitFirst :: Channel Either Either Int Int Int Int (->) Int Int
emitFirst = Channel (either negate (+ 1)) (\i -> if even i then Left (i `div` 2) else Right (i * 10))

emitBeforeCommit :: Bool
emitBeforeCommit = case emitFirst of
  Channel c e -> (e .> c) 4 == -2 && (e .> c) 3 == 31

repeatedEmission :: IO Bool
repeatedEmission = do
  commits <- newIORef (0 :: Int)
  let channel =
        Channel
          (K (\(c, i) -> modifyIORef' commits (+ 1) >> pure (c + i)))
          (K (\c -> pure (Const (c * 10)))) ::
          Body (,) Const Int Int (K IO) Int Int
  case channel of
    Channel _ e -> do
      first <- runK e 3
      second <- runK e 4
      commitCount <- readIORef commits
      pure (first == Const 30 && second == Const 40 && commitCount == 0)

sumMachine :: Moore (,) Int (->) Int Int
sumMachine = Channel (uncurry (+)) ((),)

sumScanM :: Bool
sumScanM = scanM 0 sumMachine [1, 2, 3] == [0, 1, 3, 6]

countingMachine :: Moore (,) (Int, Int) (->) Int (Int, Int)
countingMachine =
  Channel
    (\((count, total), input) -> (count + 1, total + input))
    (\channel -> ((), channel))

seededCommitScan :: Bool
seededCommitScan =
  scanM (0, 0) countingMachine [1, 2, 3]
    == [(0, 0), (1, 1), (2, 3), (3, 6)]

carryMachine :: Moore (,) Int (->) Int Int
carryMachine = Channel (uncurry (+)) (\channel -> ((), channel * 10))

carryScanM :: Bool
carryScanM = scanM 0 carryMachine [1, 2, 3] == [0, 10, 30, 60]

carryFoldM :: Bool
carryFoldM = foldM 0 carryMachine [1, 2, 3] == 60

emptyMachine :: Moore (,) Int (->) Int Int
emptyMachine = Channel (error "scanM ran commit on empty input") ((),)

emptyScanM :: Bool
emptyScanM = scanM 0 emptyMachine [] == [0]

emptyFoldMachine :: Moore (,) Int (->) Int Int
emptyFoldMachine = Channel (error "foldM ran commit on empty input") ((),)

emptyFoldM :: Bool
emptyFoldM = foldM 0 emptyFoldMachine [] == 0

identityMachine :: Moore (,) s (->) s s
identityMachine = Channel snd ((),)

runIdentityMachine :: s -> [s] -> [s]
runIdentityMachine seed = scanM seed identityMachine
{-# NOINLINE runIdentityMachine #-}

identityScanM :: IO Bool
identityScanM = do
  result <- timeout 1000000 $ evaluate (take 5 (runIdentityMachine 0 ([1 ..] :: [Int])) == [0, 1, 2, 3, 4])
  pure (result == Just True)

delayMachine :: Moore (,) (s, s) (->) s s
delayMachine = Channel (\((_, previous), input) -> (previous, input)) (\channel -> ((), fst channel))

directDelayScan :: Bool
directDelayScan = scanM (1 :: Int, 1) delayMachine [0, 1, 2] == [1, 1, 0, 1]

composeMachine ::
  Moore (,) s2 (->) b c ->
  Moore (,) s1 (->) a b ->
  Moore (,) (s1, s2) (->) a c
composeMachine (Channel commit2 emit2) (Channel commit1 emit1) =
  Channel
    ( \((channel1, channel2), input) ->
        let channel1' = commit1 (channel1, input)
            middle = snd (emit1 channel1')
            channel2' = commit2 (channel2, middle)
         in (channel1', channel2')
    )
    (emit2 . snd)

composedDelayScan :: Bool
composedDelayScan =
  let outputs :: [Int]
      outputs = scanM ((2, 2), (1, 1)) (composeMachine delayMachine delayMachine) [0, 1, 2]
   in outputs == [1, 1, 2, 0]

lazyFoldRun :: Bool
lazyFoldRun = foldM (error "foldM forced the seed") lazyMachine [0, 1] == "done"
  where
    lazyMachine =
      Channel
        (\(_, _) -> ())
        (const ((), "done")) ::
        Moore (,) () (->) Int String

scanFoldAgreement :: Bool
scanFoldAgreement =
  all
    (\inputs -> foldM 0 sumMachine inputs == last (scanM 0 sumMachine inputs))
    [[], [7], [1, 2, 3, 4]]

machineTopic :: Verbosity -> IO [Bool]
machineTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Machine oracles"
  sequence
    [ checkV verbosity "body fusion composes commit then emit" fusion,
      checkV verbosity "scanM emits the initial zero and every subsequent sum" sumScanM,
      checkV verbosity "scanM observes the initial channel then performs one commit per input" seededCommitScan,
      checkV verbosity "scanM empty input emits the seed without commit" emptyScanM,
      checkIOV verbosity "scanM identity emits the seed and an infinite-input prefix" identityScanM,
      checkV verbosity "scanM carries commit-produced channels rather than observations" carryScanM,
      checkV verbosity "foldM observes the final commit-produced channel" carryFoldM,
      checkV verbosity "foldM empty input emits the seed without commit" emptyFoldM,
      checkV verbosity "foldM agrees with the final scanM observation" scanFoldAgreement,
      checkV verbosity "foldM does not force a seed its commits ignore" lazyFoldRun,
      checkV verbosity "scanM restores a direct delay channel" directDelayScan,
      checkV verbosity "scanM restores delay1 1 . delay1 2 as [1,1,2,0]" composedDelayScan,
      checkV verbosity "a link slides between commit and emit without changing fusion" linkSliding,
      checkIOV verbosity "emit repeats without running commit" repeatedEmission,
      checkV verbosity "a general channel permits emit before commit where its interfaces align" emitBeforeCommit,
      checkV verbosity "const-corner body at (,) is memoryless: step 2 is the fresh commit/emit; threading breaks the anchors" threading,
      checkV verbosity "const-corner body at Either: an emit returning Right terminates the run" completion
    ]
