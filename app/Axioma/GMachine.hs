{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# HLINT ignore "Functor law" #-}
{-# HLINT ignore "Use <$>" #-}

module Axioma.GMachine
  ( gMachineTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Category (id, (.))
import Circuit.GMachine (Body (Body), Cell (..), CellD (..), GMoore (..), GMooreT (..), Moore, TensorSchedule (..), bodyAsBodyTT, bodyTTAsBody, bodyTTAsCell, bodyTTAsCellD, cellAsBodyTT, cellAsLens, cellDAsBodyTT, scanT)
import Circuit.Poly (applyLens)
import Circuit.Tensor (Action (..), SemiTensor (..), Tensor, Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Control.Exception (evaluate)
import Control.Monad (when)
import Data.Maybe (isNothing)
import Data.These (These (..), these)
import System.Timeout (timeout)
import Prelude hiding (id, (.))

regW :: Cell (,) Int (->) Int Int
regW = Cell snd id

accW :: Cell (,) Int (->) Int Int
accW = Cell (uncurry (+)) id

constW :: Cell (,) Int (->) Int Int
constW = Cell fst (const 0)

cntW :: Cell (,) Int (->) Int Int
cntW = Cell (\(s, _) -> s + 1) id

getPut :: (Eq ch) => Cell (,) ch (->) i i -> ch -> Bool
getPut (Cell w o) s = w (s, o s) == s

putGet :: (Eq i) => Cell (,) ch (->) i i -> ch -> i -> Bool
putGet (Cell w o) s i = o (w (s, i)) == i

putPut :: (Eq ch) => Cell (,) ch (->) i o -> ch -> i -> i -> Bool
putPut (Cell w _) s i j = w (w (s, i), j) == w (s, j)

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

memCellD :: CellD (,) Int (->) String Int
memCellD = CellD length (\ch -> (ch + 1, ch * 10))

twoStep :: CellD (,) ch (->) i o -> i -> i -> (o, o)
twoStep (CellD x g) i1 i2 =
  let (_c1', o1) = g (x i1)
      (_c2', o2) = g (x i2)
   in (o1, o2)

threading :: Bool
threading =
  twoStep memCellD "ab" "cdef" == (20, 40)
    && twoStep memCellD "xyz" "cdef" == (30, 40)
    && snd (twoStep memCellD "ab" "cdef") == fresh2
  where
    fresh2 = case memCellD of
      CellD x g -> snd (g (x "cdef"))

doneCellD :: CellD Either Int (->) Int Int
doneCellD = CellD id (\ch -> if ch < 4 then Left (ch + 1) else Right ch)

runDone :: CellD Either ch (->) i o -> [i] -> [Either ch o]
runDone (CellD x g) = go
  where
    go [] = []
    go (i : is) =
      let p = g (x i)
       in p : case p of
            Left _ -> go is
            Right _ -> []

completion :: Bool
completion = runDone doneCellD [3, 5, 7] == [Left 4, Right 5]

tenW :: Cell (,) Int (->) Int Int
tenW = Cell (uncurry (+)) (* 10)

cellLegsOk :: Bool
cellLegsOk =
  all
    ( \(s, i) ->
        absorb rt (s, i) == s + i
          && observe rt s == 10 * s
    )
    [(s, i) | s <- grid, i <- grid]
  where
    rt = bodyTTAsCell (cellAsBodyTT tenW)
    grid = [-1, 0, 5] :: [Int]

cellDLegsOk :: Bool
cellDLegsOk =
  all (\c -> imbue rt c == (c + 1, c * 10)) grid
    && all (\s -> expunge rt s == length s) ["", "ab", "cdef"]
  where
    rt = bodyTTAsCellD (cellDAsBodyTT memCellD)
    grid = [-1, 0, 5] :: [Int]

bodyW :: Body (,) Int (->) Int Int
bodyW = Body (uncurry (+)) (\c -> (c, c))

bodyLegsOk :: Bool
bodyLegsOk =
  let Body k p = bodyTTAsBody (bodyAsBodyTT bodyW)
   in all (\(s, i) -> k (s, i) == s + i) [(s, i) | s <- grid, i <- grid]
        && all (\c -> p c == (c, c)) grid
  where
    grid = [-1, 0, 5] :: [Int]

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

meanM :: GMooreT (,) (->) Int Int
meanM = GMooreT (GMoore (\a -> (1, a)) (Cell (\((n, s), a) -> (n + 1, s + a)) (\(n, s) -> s `div` n)))

cntM :: GMooreT (,) (->) Int Int
cntM = GMooreT (GMoore (const 0) (Cell (\(s, _) -> s + 1) id))

colM :: GMooreT (,) (->) Int [Int]
colM = GMooreT (GMoore (: []) (Cell (\(s, a) -> a : s) id))

bumpM :: GMooreT (,) (->) Int Int
bumpM = GMooreT (GMoore id (Cell snd (+ 100)))

nestedM :: GMooreT (,) (->) ((Int, Int), Int) ((Int, [Int]), Int)
nestedM = tensor (tensor cntM colM) cntM

sideM :: GMooreT (,) (->) (Int, (Int, Int)) (Int, ([Int], Int))
sideM = tensor cntM (tensor colM cntM)

sideXs :: [(Int, (Int, Int))]
sideXs = [(1, (10, 100)), (2, (20, 200)), (3, (30, 300)), (4, (40, 400))]

powersBody :: GMooreT (,) (->) ([Integer], ()) ([Integer], [Integer])
powersBody = GMooreT (GMoore (\(ns, ()) -> 1 : map (* 2) ns) (Cell (\(s, (_, ())) -> s) (\s -> (s, take 5 s))))

strictBody :: GMooreT (,) (->) (Int, Int) (Int, Int)
strictBody = GMooreT (GMoore (uncurry (+)) (Cell (\(s, (fb, x)) -> s + fb + x) (\s -> (s, s))))

scanBoth :: GMooreT These (->) i o -> [i] -> [o]
scanBoth (GMooreT (GMoore j (Cell k e))) = \case
  [] -> []
  (i : is) -> let c = j i in e c : go c is
  where
    go _ [] = []
    go c (i : is) = let c' = k (These c i) in e c' : go c' is

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
      checkV verbosity "cellD at (,) is memoryless: step 2 is the fresh expunge/imbue; threading breaks the anchors" threading,
      checkV verbosity "cellD at Either: an imbue returning Right terminates the run" completion,
      checkV verbosity "bodytt (t,Const) corner: cell round trip is the identity leg-for-leg (decode slip breaks observe)" cellLegsOk,
      checkV verbosity "bodytt (Const,t) corner: celld round trip is the identity leg-for-leg (phantom read breaks expunge)" cellDLegsOk,
      checkV verbosity "bodytt (t,t) diagonal: body round trip is the identity leg-for-leg" bodyLegsOk,
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
