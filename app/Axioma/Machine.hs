{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- The law witnesses below deliberately spell the laws literally —
-- @fmap f (fmap g m)@ and @pure id <*> m@ — hlint's functor-law and
-- <$> rewrites for this module are suppressed in .hlint.yaml.

-- | Machine oracles.
module Axioma.Machine
  ( machineTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Category (K (..), id, (.))
import Circuit.Machine (Body (Body), Cell (..), EitherBody (..), FoldBody (..), LensBody (..), MealyT (..), MergeNat (..), Moore, MooreT (..), OpticBody (..), ProfunctorBody (..), Step (..), TheseBody (..), bodyAsLens, fold, fuseEitherBody, fuseFoldBody, fuseLensBody, fuseOpticBody, fuseProfunctorBody, fuseTheseBody, lensAsLensBody, lensAsOptic, lensBodyAsLens, lensBodyToOptic, mealyToKnot, mooreToKnot, opticAsLens, opticToLensBody, scan, scanT, traceToMoore, unfuseEitherBody, unfuseTheseBody)
import Circuit.Poly (Lens, applyLens, lens)
import Circuit.Syntax qualified as S
import Circuit.Tensor (Const (..), SemiTensor (..), Symmetric (..), Tensor, Unital (..), unConst)
import Circuit.Trace (FreeTrace)
import Circuit.Traced (Assoc (..), OuterSwap (..), Strength (..), Trace (..), Unfold (..))
import Control.Exception (evaluate)
import Control.Monad (when)
import Data.Functor.Identity (Identity (..))
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List.NonEmpty (toList)
import Data.Maybe (isNothing)
import Data.These (These (..), these)
import System.Timeout (timeout)
import Prelude hiding (id, (.))

-- A Moore (,) body's commit/emit legs as a lens, via the bodyAsLens
-- dictionary: a Body (,) Const s s (->) i o is the data of Lens s s o i —
-- get = emit, put = curry commit. The laws, in machine spelling:
--
--   GetPut: commit (s, emit s) = s
--   PutGet: emit (commit (s, i)) = i
--   PutPut: commit (commit (s, i), j) = commit (s, j)

-- The fully lawful witness: the register. The channel holds nothing but
-- the last input, the observation is the identity.
regW :: Moore (,) Int (->) Int Int
regW = Body id snd Const

-- GetPut counterexample: the accumulator remembers. Its channel carries
-- history the view never shows, so feeding the view back doubles.
accW :: Moore (,) Int (->) Int Int
accW = Body id (uncurry (+)) Const

-- PutGet counterexample: the observation ignores the input entirely.
constW :: Moore (,) Int (->) Int Int
constW = Body id fst (const (Const 0))

-- PutPut counterexample: the update depends on history. A commit already
-- applied cannot be undone by the next input alone.
cntW :: Moore (,) Int (->) Int Int
cntW = Body id (\(s, _) -> s + 1) Const

getPut :: (Eq ch) => Moore (,) ch (->) i i -> ch -> Bool
getPut (Body _ w o) s = w (s, unConst (o s)) == s

-- PutGet only typechecks at a homogeneous focus: emit (commit (s, i))
-- has type o, and the law compares it against i.
putGet :: (Eq i) => Moore (,) ch (->) i i -> ch -> i -> Bool
putGet (Body _ w o) s i = unConst (o (w (s, i))) == i

putPut :: (Eq ch) => Moore (,) ch (->) i o -> ch -> i -> i -> Bool
putPut (Body _ w _) s i j = w (w (s, i), j) == w (s, j)

-- The dictionary round trip: applyLens (bodyAsLens c) is (emit, curry
-- commit) back again.
dictOk :: Bool
dictOk =
  case regW of
    Body _ k e ->
      all
        ( \(s, i) ->
            fst (applyLens (bodyAsLens regW) s) == unConst (e s)
              && snd (applyLens (bodyAsLens regW) s) i == k (s, i)
        )
        [(s, i) | s <- points, i <- points]
  where
    points = [-1, 0, 5] :: [Int]

-- | A sample parallel-legs body: add the input to the channel, view the
-- channel doubled. Its lens has source position Int and source direction
-- Int (the diagonal case).
sumLensBody :: LensBody (,) Int Int (->) Int Int
sumLensBody = LensBody (uncurry (+)) (* 2)

-- | The LensBody lens round trip: lensBodyAsLens extracts (view, set), and
-- lensAsLensBody rebuilds the same body.
lbodyDictOk :: Bool
lbodyDictOk =
  let lb = lensAsLensBody (lensBodyAsLens sumLensBody)
   in and [view lb s == view sumLensBody s && set lb (s, i) == set sumLensBody (s, i) | s <- points, i <- points]
  where
    points = [-1, 0, 5] :: [Int]

-- | Hand-built lens round trip through the body: the view and put agree
-- with the original lens.
lensAsLensBodyOk :: Bool
lensAsLensBodyOk =
  let l :: Lens Int Int String Int
      l = lens show (\n d -> n + d)
      lb = lensAsLensBody l
      check s i =
        view lb s == show s
          && set lb (s, i) == s + i
   in all (uncurry check) [(s, i) | s <- points, i <- points]
  where
    points = [-1, 0, 5] :: [Int]

-- | An off-diagonal LensBody: the new channel type differs from the old.
-- The corresponding lens has source position Int and source direction
-- String.
offDiagLensBody :: LensBody (,) Int String (->) Int Int
offDiagLensBody = LensBody (\(s, i) -> show (s + i)) (* 2)

-- | Off-diagonal round trip: the lens source direction is the new channel
-- type, not the old.
offDiagLensBodyOk :: Bool
offDiagLensBodyOk =
  let l :: Lens Int String Int Int
      l = lensBodyAsLens offDiagLensBody
      lb = lensAsLensBody l
   in and [view lb s == view offDiagLensBody s && set lb (s, i) == set offDiagLensBody (s, i) | s <- points, i <- points]
  where
    points = [-1, 0, 5] :: [Int]

-- The OpticBody round trips. The residual is existential, so every
-- round-trip witness compares fused ticks — never residuals. The spec
-- witnesses spell the fused semantics directly: after the 'fuseLensBody'
-- relaxation every round trip routes through 'fuseOpticBody' on at
-- least one side, so without them a shared bug in the fuse would pass
-- both sides unnoticed.

-- | The reference semantics of a fused optic body, spelt directly: the
-- tick pairs the rebuilt channel with the output, the residual threaded
-- from 'focus' into 'rebuild'.
opticSpecOk :: Bool
opticSpecOk =
  and [f (c, i) == let (r, o) = foc c in (reb (r, i), o) | c <- points, i <- points]
  where
    points = [-1, 0, 5] :: [Int]
    foc c = (c + 1, c * 2)
    reb = uncurry (+)
    Step f = fuseOpticBody (OpticBody foc reb :: OpticBody (,) Int Int (->) Int Int)

-- | The reference semantics of a fused lens body, spelt directly: the
-- tick pairs the new channel ('set') with the tick-start view.
lensBodySpecOk :: Bool
lensBodySpecOk =
  and [f (c, i) == (s (c, i), v c) | c <- points, i <- points]
  where
    points = [-1, 0, 5] :: [Int]
    LensBody s v = sumLensBody
    Step f = fuseLensBody sumLensBody

-- | Fuse after the bridge agrees with 'fuseLensBody', on the diagonal
-- and off-diagonal bodies: the residual route copies the channel alone,
-- but the fused tick is identical.
opticFuseLensOk :: Bool
opticFuseLensOk =
  and
    [ f1 (s, i) == f2 (s, i) && g1 (s, i) == g2 (s, i)
    | s <- points,
      i <- points
    ]
  where
    points = [-1, 0, 5] :: [Int]
    Step f1 = fuseOpticBody (lensBodyToOptic sumLensBody)
    Step f2 = fuseLensBody sumLensBody
    Step g1 = fuseOpticBody (lensBodyToOptic offDiagLensBody)
    Step g2 = fuseLensBody offDiagLensBody

-- | The bridge there and back — 'opticToLensBody' after 'lensBodyToOptic'.
-- 'LensBody' has no existential, nothing to quotient by: the legs come
-- back exactly, and the fused tick is the original's.
opticBodyBridgeOk :: Bool
opticBodyBridgeOk =
  and
    [ f1 (s, i) == f2 (s, i)
        && view lb s == view sumLensBody s
        && set lb (s, i) == set sumLensBody (s, i)
    | s <- points,
      i <- points
    ]
  where
    points = [-1, 0, 5] :: [Int]
    lb = opticToLensBody (lensBodyToOptic sumLensBody)
    Step f1 = fuseLensBody lb
    Step f2 = fuseLensBody sumLensBody

-- | The coend quotient: the residual body keeps the channel's successor
-- as residual, which the getter/putter spelling has to drop — the
-- residual changes across the bridge, the fused tick doesn't.
opticCoendOk :: Bool
opticCoendOk =
  and [f1 (s, i) == f2 (s, i) | s <- points, i <- points]
  where
    points = [-1, 0, 5] :: [Int]
    ob = OpticBody (\c -> (c + 1, c * 2)) (uncurry (+)) :: OpticBody (,) Int Int (->) Int Int
    Step f1 = fuseOpticBody (lensBodyToOptic (opticToLensBody ob))
    Step f2 = fuseOpticBody ob

-- | The coend quotient across a residual of a different type: the
-- residual body pairs the channel with a flag, which the getter/putter
-- spelling has to drop entirely — the residual's type changes across
-- the bridge, the fused tick doesn't.
opticCoendTypedOk :: Bool
opticCoendTypedOk =
  and [f1 (c, i) == f2 (c, i) | c <- points, i <- points]
  where
    points = [-1, 0, 5] :: [Int]
    ob = OpticBody (\c -> ((c, even c), c * 2)) (\((r, _), i) -> r + i) :: OpticBody (,) Int Int (->) Int Int
    Step f1 = fuseOpticBody (lensBodyToOptic (opticToLensBody ob))
    Step f2 = fuseOpticBody ob

-- | A fused tick whose channel, input and output are three different
-- types (Int, String, Bool): a swapped braid or crossed wire is a type
-- error here, not a value accident.
opticTypedOk :: Bool
opticTypedOk =
  and [f (c, i) == (show (c * 2) ++ i, even c) | c <- points, i <- strs]
  where
    points = [-1, 0, 5] :: [Int]
    strs = ["", "x"] :: [String]
    ob = OpticBody (\c -> (c * 2, even c)) (\(r, i) -> show r ++ i) :: OpticBody (,) Int String (->) String Bool
    Step f = fuseOpticBody ob

-- The prism reference: a fused prism body at 'Either', spelt case by
-- case. A hit emits the output; a miss passes the residual through to
-- the rebuild; an input alone rebuilds the channel.
prismTick :: (ch -> Either r o) -> (Either r i -> ch') -> Either ch i -> Either ch' o
prismTick f b = \case
  Left c -> case f c of
    Left r -> Left (b (Left r))
    Right o -> Right o
  Right i -> Left (b (Right i))

-- | Prism bodies at 'Either' against the reference, exhaustively. One
-- prism's residual is a different type from the channel (String vs
-- Int), so a crossed wire is a type error, not a value accident.
prismSpecOk :: Bool
prismSpecOk =
  and
    [ g x == prismTick foc1 reb1 x && h x == prismTick foc2 reb2 x
    | x <- [Left c | c <- points] ++ [Right i | i <- points]
    ]
  where
    points = [-1, 0, 5] :: [Int]
    foc1 c = if c > 0 then Right (c * 10) else Left c
    reb1 = either id negate
    foc2 c = if even c then Right (c > 0) else Left (show c)
    reb2 = either id show
    Step g = fuseOpticBody (OpticBody foc1 reb1 :: OpticBody Either Int Int (->) Int Int)
    Step h = fuseOpticBody (OpticBody foc2 reb2 :: OpticBody Either Int String (->) Int Bool)

-- The These reference, derived case by case from 'innerSwap' at
-- 'These': a 'This' residual rebuilds alone; a 'That' output emits; a
-- 'These' focus does both.
theseTick :: (ch -> These r o) -> (These r i -> ch') -> These ch i -> These ch' o
theseTick f b = \case
  This c -> case f c of
    This r -> This (b (This r))
    That o -> That o
    These r o -> These (b (This r)) o
  That i -> This (b (That i))
  These c i -> case f c of
    This r -> This (b (These r i))
    That o -> These (b (That i)) o
    These r o -> These (b (These r i)) o

-- | A These body against the reference, exhaustively over every
-- presence pattern. The focus splits by sign — zero rebuilds alone,
-- positive emits alone, negative does both — so all seven branches of
-- 'innerSwap' at These are exercised.
theseSpecOk :: Bool
theseSpecOk =
  and [g x == theseTick foc reb x | x <- inputs]
  where
    points = [-1, 0, 5] :: [Int]
    inputs = [This c | c <- points] ++ [That i | i <- points] ++ [These c i | c <- points, i <- points]
    foc c = case c of
      0 -> This "zero"
      _ | c > 0 -> That True
      _ -> These (show c) False
    reb = \case
      This r -> length r
      That i -> i
      These r i -> length r + i
    Step g = fuseOpticBody (OpticBody foc reb :: OpticBody These Int Int (->) Int Bool)

-- | The canonical residual fuses like the getter/putter spelling:
-- 'fuseOpticBody' after 'lensAsOptic' agrees with 'fuseLensBody' after
-- 'lensAsLensBody'.
lensAsOpticOk :: Bool
lensAsOpticOk =
  and [f1 (s, i) == f2 (s, i) | s <- points, i <- points]
  where
    points = [-1, 0, 5] :: [Int]
    l = lensBodyAsLens sumLensBody
    Step f1 = fuseOpticBody (lensAsOptic l)
    Step f2 = fuseLensBody (lensAsLensBody l)

-- | 'opticAsLens' after 'lensAsOptic' returns the lens. The put runs
-- 'focus' a second time, so the round trip is witnessed through
-- 'applyLens', extensionally.
opticAsLensOk :: Bool
opticAsLensOk =
  and
    [ let (a1, p1) = applyLens (opticAsLens (lensAsOptic l)) s
          (a2, p2) = applyLens l s
       in (a1, p1 i) == (a2, p2 i)
    | s <- points,
      i <- points
    ]
  where
    points = [-1, 0, 5] :: [Int]
    l = lensBodyAsLens sumLensBody

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

-- MealyT witnesses. A Mealy machine exposes both the new channel and the
-- output at each tick; the runner below is the cartesian @(->)@ spelling.
runMealyT :: MealyT (,) (->) i o -> [i] -> [o]
runMealyT (MealyT (Cell seed (Step f))) is =
  let c0 = seed ()
      go _ [] = []
      go c (x : rest) =
        let (c', y) = f (c, x)
         in y : go c' rest
   in go c0 is

-- | Running sum: channel and output are both the accumulated sum.
sumMealy :: MealyT (,) (->) Int Int
sumMealy = MealyT (Cell (const 0) (Step (\(s, i) -> (s + i, s + i))))

-- | Running product: channel and output are both the accumulated product.
prodMealy :: MealyT (,) (->) Int Int
prodMealy = MealyT (Cell (const 1) (Step (\(s, i) -> (s * i, s * i))))

-- | Recent-window Mealy: productive when tied as a knot because the body
-- is non-strict in the feedback channel.
recentMealy :: MealyT (,) (->) Int [Int]
recentMealy = MealyT (Cell (const []) (Step (\(ns, i) -> (i : ns, take 3 (i : ns)))))

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

-- The bundle round trips, exhaustive over small finite inputs: a tick
-- at the Either or These source is exactly its legs, so fuse after
-- unfuse must reproduce the arrow at every point, and unfuse after
-- fuse must hand the legs back unchanged.
sbodyRT :: Bool
sbodyRT =
  and
    [ f' x == g x
    | g <- [either Right Left, either (Left . not) (const (Right True))],
      let Step f' = fuseEitherBody (unfuseEitherBody (Step g)),
      x <- [Left False, Left True, Right False, Right True]
    ]

tbodyRT :: Bool
tbodyRT =
  and
    [ f' x == g x
    | g <- [these This That These, these (That . not) This (\c i -> These (not c) i)],
      let Step f' = fuseTheseBody (unfuseTheseBody (Step g)),
      x <- [This False, This True, That False, That True, These False False, These False True, These True False, These True True]
    ]

sbodyLegs :: Bool
sbodyLegs =
  let sb = EitherBody (Left . (* 2)) (Right . (+ 1)) id :: EitherBody Either Either Int Int (->) Int Int
      EitherBody ch' i' _ = unfuseEitherBody (fuseEitherBody sb)
   in and [ch' c == Left (2 * c) | c <- [0 .. 2]]
        && and [i' i == Right (i + 1) | i <- [0 .. 2]]

tbodyLegs :: Bool
tbodyLegs =
  let tb = TheseBody Left Right (\(c, i) -> Right (c + i)) :: TheseBody Either Int Int (->) Int Int
      TheseBody ch' i' b' = unfuseTheseBody (fuseTheseBody tb)
   in and [ch' c == Left c | c <- [0 .. 2]]
        && and [i' i == Right i | i <- [0 .. 2]]
        && and [b' (c, i) == Right (c + i) | c <- [0 .. 2], i <- [0 .. 2]]

-- | The bundle fuses are no longer @(->)@-only: they work over any
-- arrow that supplies the required structural dictionaries. Witnesses
-- on @K Identity@ exercise the new substrate instances without IO.
fuseFoldBodyK :: Bool
fuseFoldBodyK =
  let fb = FoldBody (K $ const (pure 0)) (K $ \(c, i) -> pure (c + i)) (K $ \c -> pure (c * 2)) :: FoldBody (,) Int (K Identity) Int Int
      Step (K f) = fuseFoldBody fb
   in runIdentity (f (3, 4)) == (7, 14)

fuseLensBodyK :: Bool
fuseLensBodyK =
  let lb = LensBody (K $ \(c, i) -> pure (c + i)) (K $ \c -> pure (c * 2)) :: LensBody (,) Int Int (K Identity) Int Int
      Step (K f) = fuseLensBody lb
   in runIdentity (f (3, 4)) == (7, 6)

-- | The relaxed fuse's effect order over 'K IO': the residual route runs
-- the view (inside 'focus') before the set (inside 'rebuild') — the
-- output is produced before the input is consumed. Each leg logs to a
-- shared IORef; the old formulation ran set-then-view, and 'K Identity'
-- cannot see either order.
fuseLensBodyOrderOk :: IO Bool
fuseLensBodyOrderOk = do
  ref <- newIORef []
  let lb =
        LensBody
          (K $ \(c, i) -> modifyIORef' ref ("set" :) >> pure (c + i))
          (K $ \c -> modifyIORef' ref ("view" :) >> pure (c * 2)) ::
          LensBody (,) Int Int (K IO) Int Int
      Step (K f) = fuseLensBody lb
  out <- f (3, 4)
  entries <- reverse <$> readIORef ref
  pure (out == (7, 6) && entries == ["view", "set"])

fuseEitherBodyK :: Bool
fuseEitherBodyK =
  let sb = EitherBody (K $ pure . Left . (* 2)) (K $ pure . Right . (+ 1)) (K pure) :: EitherBody Either Either Int Int (K Identity) Int Int
      Step (K f) = fuseEitherBody sb
   in runIdentity (f (Left 3)) == Left 6
        && runIdentity (f (Right 3)) == Right 4

fuseTheseBodyK :: Bool
fuseTheseBodyK =
  let tb = TheseBody (K $ pure . Left . (* 2)) (K $ pure . Right) (K $ \(c, i) -> pure (Right (c + i))) :: TheseBody Either Int Int (K Identity) Int Int
      Step (K f) = fuseTheseBody tb
   in runIdentity (f (This 3)) == Left 6
        && runIdentity (f (That 3)) == Right 3
        && runIdentity (f (These 3 4)) == Right 7

fuseProfunctorBodyK :: Bool
fuseProfunctorBodyK =
  let pb = ProfunctorBody (K $ \(c, i) -> pure (c + i)) (K $ \c -> pure (c * 10)) (K $ \c -> pure (c + 1)) :: ProfunctorBody (,) Int Int (K Identity) Int Int
      Step (K f) = fuseProfunctorBody pb
   in unConst (runIdentity (f (3, 4))) == 71

machineTopic :: Verbosity -> IO [Bool]
machineTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Machine oracles"
  sequence
    [ checkV verbosity "body lens dictionary: get = emit, put = curry commit" dictOk,
      checkV verbosity "LensBody lens dictionary round trip (diagonal)" lbodyDictOk,
      checkV verbosity "lensAsLensBody round trip" lensAsLensBodyOk,
      checkV verbosity "LensBody lens dictionary round trip (off-diagonal)" offDiagLensBodyOk,
      checkV verbosity "OpticBody spec: the fused tick pairs the rebuilt channel with the output (spelt directly)" opticSpecOk,
      checkV verbosity "LensBody spec: the fused tick pairs set with the tick-start view (spelt directly)" lensBodySpecOk,
      checkV verbosity "OpticBody fuse after lensBodyToOptic agrees with fuseLensBody (diagonal and off-diagonal)" opticFuseLensOk,
      checkV verbosity "opticToLensBody after lensBodyToOptic hands the legs back exactly" opticBodyBridgeOk,
      checkV verbosity "OpticBody coend quotient: the residual changes, the fused tick doesn't" opticCoendOk,
      checkV verbosity "OpticBody coend quotient across a residual of a different type (Int, Bool)" opticCoendTypedOk,
      checkV verbosity "OpticBody fused tick at three distinct carrier types (Int, String, Bool)" opticTypedOk,
      checkV verbosity "prism bodies at Either against the case-by-case reference (two prisms, exhaustive)" prismSpecOk,
      checkV verbosity "These body against the case-by-case reference (all seven branches)" theseSpecOk,
      checkV verbosity "fuseOpticBody . lensAsOptic agrees with fuseLensBody . lensAsLensBody" lensAsOpticOk,
      checkV verbosity "opticAsLens after lensAsOptic returns the lens (witnessed through applyLens)" opticAsLensOk,
      checkV verbosity "body GetPut (register)" (all (getPut regW) points),
      checkV verbosity "body GetPut catches the accumulator" (not (getPut accW 1)),
      checkV verbosity "body PutGet (register)" (all (\s -> putGet regW s 3) points),
      checkV verbosity "body PutGet catches the constant observation" (not (putGet constW 0 3)),
      checkV verbosity "body PutPut (register)" (putPut regW 0 1 2),
      checkV verbosity "body PutPut catches the counting machine" (not (putPut cntW 0 1 2)),
      checkV verbosity "const-corner body at (,) is memoryless: step 2 is the fresh commit/emit; threading breaks the anchors" threading,
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
      checkV verbosity "EitherBody fuse after unfuse reproduces the tick (Either Bool, exhaustive)" sbodyRT,
      checkV verbosity "TheseBody fuse after unfuse reproduces the tick (These Bool, exhaustive)" tbodyRT,
      checkV verbosity "EitherBody unfuse after fuse hands the legs back" sbodyLegs,
      checkV verbosity "TheseBody unfuse after fuse hands the legs back" tbodyLegs,
      checkV verbosity "FoldBody fuse over K Identity" fuseFoldBodyK,
      checkV verbosity "LensBody fuse over K Identity" fuseLensBodyK,
      checkIOV verbosity "fuseLensBody runs view before set over K IO (the residual route's effect order)" fuseLensBodyOrderOk,
      checkV verbosity "EitherBody fuse over K Identity" fuseEitherBodyK,
      checkV verbosity "TheseBody fuse over K Identity" fuseTheseBodyK,
      checkV verbosity "ProfunctorBody fuse over K Identity" fuseProfunctorBodyK,
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
        scanT (strength bumpM) ([(1, 5), (2, 7), (3, 9)] :: [(Int, Int)]) == [(1, 105), (2, 107), (3, 109)],
      checkV verbosity "mealyT (,) unit L" (runMealyT (id . sumMealy) xs == runMealyT sumMealy xs),
      checkV verbosity "mealyT (,) unit R" (runMealyT (sumMealy . id) xs == runMealyT sumMealy xs),
      checkV verbosity "mealyT (,) associativity on a three-machine chain" (runMealyT ((prodMealy . sumMealy) . sumMealy) xs == runMealyT (prodMealy . (sumMealy . sumMealy)) xs),
      checkV verbosity "traceToMoore on a base arrow runs as the arrow" $
        scan (traceToMoore (S.Lift (+ 1) :: FreeTrace (,) (->) Int Int)) xs == [2, 3, 4, 5],
      checkV verbosity "mooreToKnot on a memoryless Moore matches the one-tick output" $
        S.run (mooreToKnot (MooreT (Body (const 0) snd (Const . (* 2)) :: Moore (,) Int (->) Int Int))) 5 == 10,
      checkV verbosity "mealyToKnot on a productive body ties a constant-input knot" $
        S.run (mealyToKnot recentMealy) 7 == [7, 7, 7]
    ]
  where
    points = [-1, 0, 5] :: [Int]
