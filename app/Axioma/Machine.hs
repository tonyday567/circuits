{-# LANGUAGE ScopedTypeVariables #-}

-- The law witnesses below deliberately spell the laws literally. The
-- alternative Body/optic/Q and cross-lane witnesses live in the
-- circuits-examples Body zoo; this module retains the core machine lifecycle,
-- MergeNat, and MooreT structure.

-- | Core machine oracles.
module Axioma.Machine
  ( machineTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Category (id, (.))
import Circuit.Machine (Body (Body), MergeNat (..), Moore, MooreT (..), fold, scan, scanT)
import Circuit.Tensor (Const (..), SemiTensor (..), Symmetric (..), Tensor, Unital (..), unConst)
import Circuit.Traced (Assoc (..), OuterSwap (..), Strength (..), Trace (..), Unfold (..))
import Control.Exception (evaluate)
import Control.Monad (when)
import Data.List.NonEmpty (toList)
import Data.Maybe (isNothing)
import Data.These (These (..), these)
import System.Timeout (timeout)
import Prelude hiding (id, (.))

-- | A named 'Body' at the @(Const, (,))@ corner: 'commit' writes the
-- channel from the input alone (its length) — the @Const@ tick source
-- has no channel slot — and 'emit' emits the channel update alongside
-- the output. The leg types are chosen so the threading falsifier — a
-- step-2 commit reading step 1's emitted package — is a type error at
-- 'commit', not a silent carry.
memBody :: Body Const (,) Int Int (->) String Int
memBody = Body length (\(Const s) -> length s) (\ch -> (ch + 1, ch * 10))

-- | The two-step run, spelt out: each step commits its channel from its
-- own input alone; step 1's emitted package is bound and deliberately
-- dead. That dead binding is the memorylessness claim — a threading
-- runner would route it into step 2's commit.
twoStep :: Body Const (,) ch ch' (->) i o -> i -> i -> (o, o)
twoStep (Body _ x g) i1 i2 =
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
      Body _ x g -> snd (g (x (Const "cdef")))

-- | A named 'Body' at the @(Const, Either)@ corner: 'commit' writes the
-- channel from the input alone; 'emit' evolves ('Left', the updated
-- channel) while the input is small and completes ('Right') once it is
-- not — the exit constructor a bare 'Moore' emit (@arr ch o@, no
-- constructors) cannot say.
doneBody :: Body Const Either Int Int (->) Int Int
doneBody = Body id (\(Const i) -> i) (\ch -> if ch < 4 then Left (ch + 1) else Right ch)

-- | The 'Either' run: commit, emit, repeat. 'Left' logs the evolved
-- channel — never carried forward, per the @Const@ corner's
-- memorylessness — and the run continues; 'Right' terminates it, and
-- the remaining inputs are never committed.
runDone :: Body Const Either ch ch (->) i o -> [i] -> [Either ch o]
runDone (Body _ x g) = go
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

-- Falsifiers (verify.md discipline): a stale-carrier composite feed breaks
-- the unit scans; a non-projection fold (e.g. a These-sum fold) breaks
-- naturality; naturality alone admits both projection folds, so the These
-- input-bias is pinned by the scanBoth unit witnesses — scanT's
-- That-injection never exercises the These clause.

sumG :: MooreT (,) (->) Int Int
sumG = MooreT (Body id (uncurry (+)) Const)

prodG :: MooreT (,) (->) Int Int
prodG = MooreT (Body (* 10) (uncurry (*)) Const)

countG :: MooreT (,) (->) Int Int
countG = MooreT (Body (const 100) (\(c, _) -> c + 1) Const)

eitherG :: MooreT Either (->) Int Int
eitherG = MooreT (Body id (either id (+ 1)) (Const . (* 2)))

theseG :: MooreT These (->) Int Int
theseG = MooreT (Body id (these id (+ 1) (\c i -> c + i)) Const)

xs :: [Int]
xs = [1, 2, 3, 4]

-- Ported-instance witnesses for MooreT (,) (->). Each witness is named
-- for the counterexample it catches:
--   * the functor runs catch an fmap wired to the commit leg — meanM's
--     channel (Int, Int) is not its output type Int, so a leg swap is
--     ill-typed, and an fmap that drops the observation fails the
--     [1,1,2,2] anchor;
--   * the applicative product runs catch crossed (ch1, ch2) wiring — the
--     counter and collector channels differ, so a crossed commit is a type
--     error and a crossed observation swaps the pair;
--   * the trace runs catch a strict knot tie (the strictBody divergence)
--     and a dropped feedback (powersBody would return a wrong stream);
--   * the unital, tensor, and braid runs catch swapped unitors and
--     swapped product wires;
--   * the assoc and outerSwap round trips catch a state-threading slip past
--     the reassociated or slid product;
--   * the strength run catches a swapped fst/snd wire in the strengthened
--     machine.

-- | Running mean: channel (count, sum), the view the integer mean. The
-- channel type differs from the output type, so a swapped-leg fmap cannot
-- type here — the functor witnesses run where a leg swap cannot.
meanM :: MooreT (,) (->) Int Int
meanM = MooreT (Body (\a -> (1, a)) (\((n, s), a) -> (n + 1, s + a)) (Const . (\(n, s) -> s `div` n)))

-- | Tick counter: channel Int, the view the tick count.
cntM :: MooreT (,) (->) Int Int
cntM = MooreT (Body (const 0) (\(s, _) -> s + 1) Const)

-- | Newest-first collector: channel [Int], distinct from cntM's channel, so
-- crossed (ch1, ch2) wiring in the applicative and tensor products is a
-- type error rather than a silent swap; a crossed observation still shows
-- in the run.
colM :: MooreT (,) (->) Int [Int]
colM = MooreT (Body (: []) (\(s, a) -> a : s) Const)

-- | View-bump machine for the strength witness: the channel is the last
-- input, the view adds 100.
bumpM :: MooreT (,) (->) Int Int
bumpM = MooreT (Body id snd (Const . (+ 100)))

-- | Left-nested product of the counter and collector for the associator
-- round trip.
nestedM :: MooreT (,) (->) ((Int, Int), Int) ((Int, [Int]), Int)
nestedM = tensor (tensor cntM colM) cntM

-- | Right-nested product for the outerSwap round trip and the associator RHS.
sideM :: MooreT (,) (->) (Int, (Int, Int)) (Int, ([Int], Int))
sideM = tensor cntM (tensor colM cntM)

sideXs :: [(Int, (Int, Int))]
sideXs = [(1, (10, 100)), (2, (20, 200)), (3, (30, 300)), (4, (40, 400))]

-- | Powers-of-two body for the lazy-knot productivity witness: the initial
-- channel is @1 : map (* 2) ns@ with the feedback @ns@ tied by the trace —
-- the machine counterpart of the cartesian @(->)@ 'trace' powers example.
-- Guards the Trace productivity clause: a strict knot tie diverges here.
powersBody :: MooreT (,) (->) ([Integer], ()) ([Integer], [Integer])
powersBody = MooreT (Body (\(ns, ()) -> 1 : map (* 2) ns) (\(s, (_, ())) -> s) (Const . (\s -> (s, take 5 s))))

-- | Strict accumulator body for the divergence witness: init and step are
-- strict in the feedback channel, so the lazy knot is circular and the run
-- never terminates. Guards the Trace non-strictness clause, modelled on the
-- Pullback trace-divergence oracle.
strictBody :: MooreT (,) (->) (Int, Int) (Int, Int)
strictBody = MooreT (Body (uncurry (+)) (\(s, (fb, x)) -> s + fb + x) (Const . (\s -> (s, s))))

-- Input-list elimination at the inclusive tensor, full injection: every
-- step feeds These c i, where scanT's That-injection is memoryless on the
-- carrier. Modelled on scanT, pattern-matching These directly.
scanBoth :: MooreT These (->) i o -> [i] -> [o]
scanBoth (MooreT (Body j k e)) = \case
  [] -> []
  (i : is) -> let c = j i in unConst (e c) : go c is
  where
    go _ [] = []
    go c (i : is) = let c' = k (These c i) in unConst (e c') : go c' is

scanTheseRun :: Moore (,) s (->) a b -> [a] -> [b]
scanTheseRun (Body c k o) = \case
  [] -> []
  (a : as) -> toList (unfold gen (Nothing, a, as))
  where
    gen (ms, a, rest) =
      let s' = case ms of
            Nothing -> c a
            Just s -> k (s, a)
       in case rest of
            [] -> That (unConst (o s'))
            (a' : rest') -> These (Just s', a', rest') (unConst (o s'))

sumRun :: Moore (,) Int (->) Int Int
sumRun = Body id (uncurry (+)) Const

meanRun :: Moore (,) (Int, Int) (->) Int Int
meanRun = Body (\a -> (1, a)) (\((n, s), a) -> (n + 1, s + a)) (Const . (\(n, s) -> s `div` n))

-- mergeNat naturality: mergeNat . tensor f f == f . mergeNat at f = (+ 1).
natPair :: Bool
natPair =
  all
    (\x -> mergeNat (tensor f f x) == f (mergeNat x))
    [(0, 5), (3, 7)]
  where
    f :: Int -> Int
    f = (+ 1)

natEither :: Bool
natEither =
  all
    (\x -> mergeNat (tensor f f x) == f (mergeNat x))
    [Left 0, Right 5]
  where
    f :: Int -> Int
    f = (+ 1)

natThese :: Bool
natThese =
  all
    (\x -> mergeNat (tensor f f x) == f (mergeNat x))
    [This 0, That 5, These 0 5]
  where
    f :: Int -> Int
    f = (+ 1)

machineTopic :: Verbosity -> IO [Bool]
machineTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Machine oracles"
  sequence
    [ checkV verbosity "const-corner body at (,) is memoryless: step 2 is the fresh commit/emit; threading breaks the anchors" threading,
      checkV verbosity "const-corner body at Either: an emit returning Right terminates the run" completion,
      checkV verbosity "mooreT (,) scan anchor" (scanT sumG xs == [1, 3, 6, 10]),
      checkV verbosity "mooreT Either scan anchor" (scanT eitherG xs == [2, 6, 8, 10]),
      checkV verbosity "mooreT These scan anchor (That-injection)" (scanT theseG xs == [1, 3, 4, 5]),
      checkV verbosity "mooreT These scanBoth anchor (full injection)" (scanBoth theseG xs == [1, 3, 6, 10]),
      checkV verbosity "the These unfold agrees with scan and fold (an early That truncates the run to its first output)" $
        let run = scanTheseRun sumRun xs
         in scanTheseRun sumRun [] == []
              && run == scan (MooreT sumRun) xs
              && scanTheseRun meanRun xs == scan (MooreT meanRun) xs
              && fold (MooreT sumRun) xs == Just (last run),
      checkIOV verbosity "scan is spine-lazy: a prefix delivers on an infinite tape" $ do
        result <- timeout 1000000 $ evaluate (take 3 (scan (MooreT sumRun) [1 ..]) == [1, 3, 6])
        pure (result == Just True),
      checkV verbosity "mergeNat naturality at (,)" natPair,
      checkV verbosity "mergeNat naturality at Either" natEither,
      checkV verbosity "mergeNat naturality at These" natThese,
      checkV verbosity "mooreT unit L at (,): scanT (id . m) == scanT m" (scanT (id . sumG) xs == scanT sumG xs),
      checkV verbosity "mooreT unit R at (,): scanT (m . id) == scanT m" (scanT (sumG . id) xs == scanT sumG xs),
      checkV verbosity "mooreT unit L at Either" (scanT (id . eitherG) xs == scanT eitherG xs),
      checkV verbosity "mooreT unit R at Either" (scanT (eitherG . id) xs == scanT eitherG xs),
      checkV verbosity "mooreT unit L at These" (scanT (id . theseG) xs == scanT theseG xs),
      checkV verbosity "mooreT unit R at These" (scanT (theseG . id) xs == scanT theseG xs),
      checkV verbosity "mooreT unit L at These, full injection" (scanBoth (id . theseG) xs == scanBoth theseG xs),
      checkV verbosity "mooreT unit R at These, full injection" (scanBoth (theseG . id) xs == scanBoth theseG xs),
      checkV verbosity "mooreT associativity on a three-machine chain" (scanT ((countG . prodG) . sumG) xs == scanT (countG . (prodG . sumG)) xs),
      checkV verbosity "mooreT (,) functor identity: fmap id runs as the machine" $
        scanT (fmap id meanM) xs == [1, 1, 2, 2],
      checkV verbosity "mooreT (,) functor composition: fmap (f . g) runs as fmap f . fmap g" $
        scanT (fmap ((+ 1) . (* 2)) meanM) xs == scanT (fmap (+ 1) (fmap (* 2) meanM)) xs,
      checkV verbosity "mooreT (,) applicative identity: pure id <*> m runs as m" $
        scanT (pure id <*> sumG) xs == [1, 3, 6, 10],
      checkV verbosity "mooreT (,) applicative product: distinct channels stay on their own legs" $
        scanT ((,) <$> cntM <*> colM) xs == [(0, [1]), (1, [2, 1]), (2, [3, 2, 1]), (3, [4, 3, 2, 1])],
      checkV verbosity "mooreT (,) trace: lazy knot productive on a non-strict body" $
        scanT (trace powersBody) [(), (), ()] == [[1, 2, 4, 8, 16], [1, 2, 4, 8, 16], [1, 2, 4, 8, 16]],
      checkIOV verbosity "mooreT (,) trace: strict accumulator diverges (use feedback)" $ do
        result <- timeout 1000000 $ case scanT (trace strictBody) [1 :: Int] of
          (o : _) -> evaluate o
          [] -> pure 0
        pure (isNothing result),
      checkV verbosity "mooreT (,) unital: tensor unit wires pass a machine through" $
        scanT (unitl @(,) . tensor (id :: MooreT (,) (->) () ()) sumG . unitl' @(,)) xs == [1, 3, 6, 10]
          && scanT (unitr @(,) . tensor sumG (id :: MooreT (,) (->) () ()) . unitr' @(,)) xs == [1, 3, 6, 10],
      checkV verbosity "mooreT (,) tensor: product machine keeps the wires disjoint" $
        scanT (tensor cntM colM) (zip [1 .. 4] [10, 20, 30, 40])
          == [(0, [10]), (1, [20, 10]), (2, [30, 20, 10]), (3, [40, 30, 20, 10])],
      checkV verbosity "mooreT (,) braid: braid swaps the two product wires" $
        scanT (braid . tensor cntM colM) (zip [1 .. 2] [10, 20]) == [([10], 0), ([20, 10], 1)],
      checkV verbosity "mooreT (,) assoc: reassociating wires commutes with tensor nesting" $
        scanT (assoc . nestedM . assoc') sideXs == scanT sideM sideXs,
      checkV verbosity "mooreT (,) outerSwap: sliding a wire past a product commutes with tensor nesting" $
        scanT (outerSwap . sideM . outerSwap) sideXs == scanT (tensor colM (tensor cntM cntM)) sideXs,
      checkV verbosity "mooreT (,) strength: strength lifts a machine to the second wire" $
        scanT (strength bumpM) ([(1, 5), (2, 7), (3, 9)] :: [(Int, Int)]) == [(1, 105), (2, 107), (3, 109)]
    ]
