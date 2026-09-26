{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- The law witnesses below deliberately spell the laws literally —
-- @fmap f (fmap g m)@ and @pure id <*> m@ — so hlint's functor-law and
-- <$> rewrites are ignored module-wide.
{-# HLINT ignore "Functor law" #-}
{-# HLINT ignore "Use <$>" #-}

-- | GMachine oracles.
module Axioma.GMachine
  ( gMachineTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Category (id, (.))
import Circuit.GMachine (Cell (..), GMoore (..), GMooreT (..), Moore, TensorSchedule (..), cellAsLens, scanT)
import Circuit.Poly (applyLens)
import Circuit.Tensor (Action (..), Tensor (..), Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Control.Exception (evaluate)
import Control.Monad (when)
import Data.Maybe (isNothing)
import Data.These (These (..), these)
import System.Timeout (timeout)
import Prelude hiding (id, (.))

-- Cell (,) as a lens, via the cellAsLens dictionary: a Cell (,) s (->) i o
-- is the data of Lens s s o i — get = observe, put = curry absorb. The laws,
-- in machine spelling:
--
--   GetPut: absorb (s, observe s) = s
--   PutGet: observe (absorb (s, i)) = i
--   PutPut: absorb (absorb (s, i), j) = absorb (s, j)

-- The fully lawful witness: the register. The channel holds nothing but
-- the last input, the observation is the identity.
regW :: Cell (,) Int (->) Int Int
regW = Cell snd id

-- GetPut counterexample: the accumulator remembers. Its channel carries
-- history the view never shows, so feeding the view back doubles.
accW :: Cell (,) Int (->) Int Int
accW = Cell (uncurry (+)) id

-- PutGet counterexample: the observation ignores the input entirely.
constW :: Cell (,) Int (->) Int Int
constW = Cell fst (const 0)

-- PutPut counterexample: the update depends on history. An absorb already
-- applied cannot be undone by the next input alone.
cntW :: Cell (,) Int (->) Int Int
cntW = Cell (\(s, _) -> s + 1) id

getPut :: (Eq ch) => Cell (,) ch (->) i i -> ch -> Bool
getPut (Cell w o) s = w (s, o s) == s

-- PutGet only typechecks at a homogeneous focus: observe (absorb (s, i))
-- has type o, and the law compares it against i.
putGet :: (Eq i) => Cell (,) ch (->) i i -> ch -> i -> Bool
putGet (Cell w o) s i = o (w (s, i)) == i

putPut :: (Eq ch) => Cell (,) ch (->) i o -> ch -> i -> i -> Bool
putPut (Cell w _) s i j = w (w (s, i), j) == w (s, j)

-- The dictionary round trip: applyLens (cellAsLens c) is (observe, curry
-- absorb) back again.
dictOk :: Bool
dictOk =
  all
    ( \(s, i) ->
        fst (applyLens (cellAsLens regW) s) == observe regW s
          && snd (applyLens (cellAsLens regW) s) i == absorb regW (s, i)
    )
    [(s, i) | s <- points, i <- points]
  where
    points = [-1, 0, 5] :: [Int]

-- Falsifiers (verify.md discipline): a stale-carrier composite feed breaks
-- the unit scans; a non-projection fold (e.g. a These-sum fold) breaks
-- naturality; naturality alone admits both projection folds, so the These
-- input-bias is pinned by the scanBoth unit witnesses — scanT's
-- That-injection never exercises the These clause.

sumG :: GMooreT (,) (->) Int Int
sumG = GMooreT (GMoore id (Cell (uncurry (+)) id))

prodG :: GMooreT (,) (->) Int Int
prodG = GMooreT (GMoore (* 10) (Cell (uncurry (*)) id))

countG :: GMooreT (,) (->) Int Int
countG = GMooreT (GMoore (const 100) (Cell (\(c, _) -> c + 1) id))

eitherG :: GMooreT Either (->) Int Int
eitherG = GMooreT (GMoore id (Cell (either id (+ 1)) (* 2)))

theseG :: GMooreT These (->) Int Int
theseG = GMooreT (GMoore id (Cell (these id (+ 1) (\c i -> c + i)) id))

xs :: [Int]
xs = [1, 2, 3, 4]

-- Ported-instance witnesses for GMooreT (,) (->). Each witness is named
-- for the counterexample it catches:
--   * the functor runs catch an fmap wired to the absorb leg — meanM's
--     channel (Int, Int) is not its output type Int, so a leg swap is
--     ill-typed, and an fmap that drops the observation fails the
--     [1,1,2,2] anchor;
--   * the applicative product runs catch crossed (ch1, ch2) wiring — the
--     counter and collector channels differ, so a crossed absorb is a type
--     error and a crossed observation swaps the pair;
--   * the yank runs catch a strict knot tie (the strictBody divergence)
--     and a dropped feedback (powersBody would return a wrong stream);
--   * the unital, tensor, and braid runs catch swapped unitors and
--     swapped product wires;
--   * the assoc and slide round trips catch a state-threading slip past
--     the reassociated or slid product;
--   * the strength run catches a swapped fst/snd wire in the strengthened
--     machine.

-- | Running mean: channel (count, sum), the view the integer mean. The
-- channel type differs from the output type, so a swapped-leg fmap cannot
-- type here — the functor witnesses run where a leg swap cannot.
meanM :: GMooreT (,) (->) Int Int
meanM = GMooreT (GMoore (\a -> (1, a)) (Cell (\((n, s), a) -> (n + 1, s + a)) (\(n, s) -> s `div` n)))

-- | Tick counter: channel Int, the view the tick count.
cntM :: GMooreT (,) (->) Int Int
cntM = GMooreT (GMoore (const 0) (Cell (\(s, _) -> s + 1) id))

-- | Newest-first collector: channel [Int], distinct from cntM's channel, so
-- crossed (ch1, ch2) wiring in the applicative and tensor products is a
-- type error rather than a silent swap; a crossed observation still shows
-- in the run.
colM :: GMooreT (,) (->) Int [Int]
colM = GMooreT (GMoore (: []) (Cell (\(s, a) -> a : s) id))

-- | View-bump machine for the strength witness: the channel is the last
-- input, the view adds 100.
bumpM :: GMooreT (,) (->) Int Int
bumpM = GMooreT (GMoore id (Cell snd (+ 100)))

-- | Left-nested product of the counter and collector for the associator
-- round trip.
nestedM :: GMooreT (,) (->) ((Int, Int), Int) ((Int, [Int]), Int)
nestedM = tensor (tensor cntM colM) cntM

-- | Right-nested product for the slide round trip and the associator RHS.
sideM :: GMooreT (,) (->) (Int, (Int, Int)) (Int, ([Int], Int))
sideM = tensor cntM (tensor colM cntM)

sideXs :: [(Int, (Int, Int))]
sideXs = [(1, (10, 100)), (2, (20, 200)), (3, (30, 300)), (4, (40, 400))]

-- | Powers-of-two body for the lazy-knot productivity witness: the initial
-- channel is @1 : map (* 2) ns@ with the feedback @ns@ tied by the yank —
-- the machine counterpart of the cartesian @(->)@ 'yank' powers example.
-- Guards the Yank productivity clause: a strict knot tie diverges here.
powersBody :: GMooreT (,) (->) ([Integer], ()) ([Integer], [Integer])
powersBody = GMooreT (GMoore (\(ns, ()) -> 1 : map (* 2) ns) (Cell (\(s, (_, ())) -> s) (\s -> (s, take 5 s))))

-- | Strict accumulator body for the divergence witness: init and step are
-- strict in the feedback channel, so the lazy knot is circular and the run
-- never terminates. Guards the Yank non-strictness clause, modelled on the
-- Pullback yank-divergence oracle.
strictBody :: GMooreT (,) (->) (Int, Int) (Int, Int)
strictBody = GMooreT (GMoore (uncurry (+)) (Cell (\(s, (fb, x)) -> s + fb + x) (\s -> (s, s))))

-- Input-list elimination at the inclusive tensor, full injection: every
-- step feeds These c i, where scanT's That-injection is memoryless on the
-- carrier. Modelled on scanT, pattern-matching These directly.
scanBoth :: GMooreT These (->) i o -> [i] -> [o]
scanBoth (GMooreT (GMoore j (Cell k e))) = \case
  [] -> []
  (i : is) -> let c = j i in e c : go c is
  where
    go _ [] = []
    go c (i : is) = let c' = k (These c i) in e c' : go c' is

-- echoFold naturality: echoFold . tensor f f == f . echoFold at f = (+ 1).
natPair :: Bool
natPair =
  all
    (\x -> echoFold (tensor f f x) == f (echoFold x))
    [(0, 5), (3, 7)]
  where
    f :: Int -> Int
    f = (+ 1)

natEither :: Bool
natEither =
  all
    (\x -> echoFold (tensor f f x) == f (echoFold x))
    [Left 0, Right 5]
  where
    f :: Int -> Int
    f = (+ 1)

natThese :: Bool
natThese =
  all
    (\x -> echoFold (tensor f f x) == f (echoFold x))
    [This 0, That 5, These 0 5]
  where
    f :: Int -> Int
    f = (+ 1)

gMachineTopic :: Verbosity -> IO [Bool]
gMachineTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "GMachine oracles"
  sequence
    [ checkV verbosity "cell lens dictionary: get = observe, put = curry absorb" dictOk,
      checkV verbosity "cell GetPut (register)" (all (getPut regW) points),
      checkV verbosity "cell GetPut catches the accumulator" (not (getPut accW 1)),
      checkV verbosity "cell PutGet (register)" (all (\s -> putGet regW s 3) points),
      checkV verbosity "cell PutGet catches the constant observation" (not (putGet constW 0 3)),
      checkV verbosity "cell PutPut (register)" (putPut regW 0 1 2),
      checkV verbosity "cell PutPut catches the counting machine" (not (putPut cntW 0 1 2)),
      checkV verbosity "gmoorT (,) scan anchor" (scanT sumG xs == [1, 3, 6, 10]),
      checkV verbosity "gmoorT Either scan anchor" (scanT eitherG xs == [2, 6, 8, 10]),
      checkV verbosity "gmoorT These scan anchor (That-injection)" (scanT theseG xs == [1, 3, 4, 5]),
      checkV verbosity "gmoorT These scanBoth anchor (full injection)" (scanBoth theseG xs == [1, 3, 6, 10]),
      checkV verbosity "echoFold naturality at (,)" natPair,
      checkV verbosity "echoFold naturality at Either" natEither,
      checkV verbosity "echoFold naturality at These" natThese,
      checkV verbosity "gmoorT unit L at (,): scanT (id . m) == scanT m" (scanT (id . sumG) xs == scanT sumG xs),
      checkV verbosity "gmoorT unit R at (,): scanT (m . id) == scanT m" (scanT (sumG . id) xs == scanT sumG xs),
      checkV verbosity "gmoorT unit L at Either" (scanT (id . eitherG) xs == scanT eitherG xs),
      checkV verbosity "gmoorT unit R at Either" (scanT (eitherG . id) xs == scanT eitherG xs),
      checkV verbosity "gmoorT unit L at These" (scanT (id . theseG) xs == scanT theseG xs),
      checkV verbosity "gmoorT unit R at These" (scanT (theseG . id) xs == scanT theseG xs),
      checkV verbosity "gmoorT unit L at These, full injection" (scanBoth (id . theseG) xs == scanBoth theseG xs),
      checkV verbosity "gmoorT unit R at These, full injection" (scanBoth (theseG . id) xs == scanBoth theseG xs),
      checkV verbosity "gmoorT associativity on a three-machine chain" (scanT ((countG . prodG) . sumG) xs == scanT (countG . (prodG . sumG)) xs),
      checkV verbosity "gmoorT (,) functor identity: fmap id runs as the machine" $
        scanT (fmap id meanM) xs == [1, 1, 2, 2],
      checkV verbosity "gmoorT (,) functor composition: fmap (f . g) runs as fmap f . fmap g" $
        scanT (fmap ((+ 1) . (* 2)) meanM) xs == scanT (fmap (+ 1) (fmap (* 2) meanM)) xs,
      checkV verbosity "gmoorT (,) applicative identity: pure id <*> m runs as m" $
        scanT (pure id <*> sumG) xs == [1, 3, 6, 10],
      checkV verbosity "gmoorT (,) applicative product: distinct channels stay on their own legs" $
        scanT ((,) <$> cntM <*> colM) xs == [(0, [1]), (1, [2, 1]), (2, [3, 2, 1]), (3, [4, 3, 2, 1])],
      checkV verbosity "gmoorT (,) yank: lazy knot productive on a non-strict body" $
        scanT (yank powersBody) [(), (), ()] == [[1, 2, 4, 8, 16], [1, 2, 4, 8, 16], [1, 2, 4, 8, 16]],
      checkIOV verbosity "gmoorT (,) yank: strict accumulator diverges (use register)" $ do
        result <- timeout 1000000 (evaluate (head (scanT (yank strictBody) [1 :: Int])))
        pure (isNothing result),
      checkV verbosity "gmoorT (,) unital: tensor unit wires pass a machine through" $
        scanT (unitl @(,) . tensor (id :: Moore () ()) sumG . unitl' @(,)) xs == [1, 3, 6, 10]
          && scanT (unitr @(,) . tensor sumG (id :: Moore () ()) . unitr' @(,)) xs == [1, 3, 6, 10],
      checkV verbosity "gmoorT (,) tensor: product machine keeps the wires disjoint" $
        scanT (tensor cntM colM) (zip [1 .. 4] [10, 20, 30, 40])
          == [(0, [10]), (1, [20, 10]), (2, [30, 20, 10]), (3, [40, 30, 20, 10])],
      checkV verbosity "gmoorT (,) braid: braid swaps the two product wires" $
        scanT (braid . tensor cntM colM) (zip [1 .. 2] [10, 20]) == [([10], 0), ([20, 10], 1)],
      checkV verbosity "gmoorT (,) assoc: reassociating wires commutes with tensor nesting" $
        scanT (assoc . nestedM . assoc') sideXs == scanT sideM sideXs,
      checkV verbosity "gmoorT (,) slide: sliding a wire past a product commutes with tensor nesting" $
        scanT (slide . sideM . slide) sideXs == scanT (tensor colM (tensor cntM cntM)) sideXs,
      checkV verbosity "gmoorT (,) strength: strength lifts a machine to the second wire" $
        scanT (strength bumpM) [(1, 5), (2, 7), (3, 9)] == [(1, 105), (2, 107), (3, 109)]
    ]
  where
    points = [-1, 0, 5] :: [Int]
