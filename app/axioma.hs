{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Circuit.Stamped (Stamped (..), stamp, stamped)
import Circuit.Category (K (..), id, (.), (.>))
import Circuit.Channel (assoc, assoc', slide, strength, trace)
import Circuit.Poly.Channel (Channel (..), commitChannel, constChannel, emitChannel, idChannel, mapChannel)
import Circuit.Body (Body (..), SomeBody (..), morphism, runSomeBody)
import Circuit.Bimonoid (Copy (..), CopyDiscard, Discard (..), Merge (..), MergeZero, Zero (..))
import Circuit.Dagger (Dagger (..), transpose)
import Circuit.Poles (Bias (..), HasDual (..), In (..), Out (..), Poles (..), box, close, copycat, poles, poles0, polesK, prefixIn, splay, splay0, suffixOut, (>:>))
import Circuit.Poles qualified as Poles
import Circuit.Body qualified as Body
import Circuit.Process qualified as Process
import Circuit.Poly qualified as Poly
import Circuit.FinRel
import Circuit.Fragment qualified as Frag
import Circuit.Hyper (Hyper, observe)
import Circuit.Hyper qualified as HyperLoop
import Circuit.Layer (run)
import Circuit.Syntax qualified as Syn
import Circuit.Trace (Trace, base, yank)
import Circuit.Net qualified as Net
import Circuit.Poly (Dir, Eval (..), Mono, System, fromEvalSystem, lens, monoDir, monoIn, mooreSystem, runSystem, system)
import Circuit.Process (Boundary (..), Process (..), delay, encode, fold, isMark, isPayload, markSystem, mealy, register, runMealy, scan, systemToProcess)
import Circuit.Par (Par (..), distL, distR, mix)
import Circuit.Shared (Pick (..), Schedule (..), Shared (..))
import Circuit.Tensor (Action (..), Tensor (..), superpose)
import Circuit.Tools.Test (check)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Kind (Type)
import Data.List (foldl', isInfixOf, permutations, sort, uncons)
import Data.Maybe (catMaybes, fromMaybe, isNothing)
import Data.Proxy (Proxy (..))
import Data.These (These (..), these)
import Data.Tuple qualified as Tuple
import Data.Void (Void, absurd)
import GHC.TypeNats (KnownNat, natVal)
import Prelude hiding (curry, id, uncurry, (.))
import Prelude qualified as Pre

type N1 = FinObj 1

type N2 = FinObj 2

-- ---------------------------------------------------------------------------
--
-- 'mergeE' is callable here because the source type @?A ⅋ ?A@ puts @a@ inside
-- the injective 'ChuOPar' constructor, letting GHC determine it. 'zeroE' is
-- not directly callable at a specific @a@ because 'WhyNot' is a non-injective
-- type family and @a@ only appears inside the result. Its value-level oracle
-- 'zeroWhyNotParChu' now lives in the circuits-chu package and is exercised
-- there.
--
-- This is one instance of a general pattern: type-family non-injectivity
-- blocks polymorphic instance methods whenever an object appears only inside
-- the result of a non-injective family. The same obstruction appears in the
-- ForwardChu target for Net.bind over OChu r (see circuits-chu/axioma.hs and
-- loom/traced-ochu.md).
-- ---------------------------------------------------------------------------

-- | Swap the second and third @n@-wire blocks of @((a,b),(c,d))@.
swapBlocks ::
  forall n.
  (KnownNat n) =>
  FinRel ((FinObj n, FinObj n), (FinObj n, FinObj n)) ((FinObj n, FinObj n), (FinObj n, FinObj n))
swapBlocks = wiring perm
  where
    n = fromIntegral (natVal (Proxy @n))
    perm i
      | i < n = i
      | i < 2 * n = i + n
      | i < 3 * n = i - n
      | otherwise = i

swapMiddle :: FinRel ((N1, N1), (N1, N1)) ((N1, N1), (N1, N1))
swapMiddle = swapBlocks @1

swapMiddle2 :: FinRel ((N2, N2), (N2, N2)) ((N2, N2), (N2, N2))
swapMiddle2 = swapBlocks @2

-- | Simple additive process for oracles.
sumP :: Process Int Int
sumP = Process id (+) id

-- | Pair swap for the (,) trace yanking oracle.
swapPairP :: Process (Int, Int) (Int, Int)
swapPairP = Process id (\_ x -> x) (\(a, b) -> (b, a))

-- | Either swap for the Either trace yanking oracle.
swapEitherP :: Process (Either Int Int) (Either Int Int)
swapEitherP = Process id (\_ x -> x) swapEither
  where
    swapEither (Left a) = Right a
    swapEither (Right b) = Left b

-- | EWMA body: stateless affine box with feedback.
ewmaBody :: Double -> Process (Double, Double) (Double, Double)
ewmaBody alpha =
  Process
    (\(x, prev) -> alpha * x + (1 - alpha) * prev)
    (\s (x, _) -> alpha * x + (1 - alpha) * s)
    (\s -> (s, s))

-- | Exponentially weighted moving average with initial feedback.
ewma :: Double -> Double -> Process Double Double
ewma alpha s0 = register s0 (ewmaBody alpha)

-- | Shared-medium body: adds the input to the shared state and echoes it.
sharedAddP :: Process (Int, Int) (Int, Int)
sharedAddP = Process (Pre.uncurry (+)) (\s (_, a) -> s + a) (\s -> (s, s))

-- | Shared-medium body: doubles the shared state and echoes the input.
sharedDoubleP :: Process (Int, Int) (Int, Int)
sharedDoubleP = Process (\(s, _) -> s * 2) (\s (_, _) -> s * 2) (\s -> (s, s))

-- | Function counterpart of 'sharedAddP' for premonoidal centrality tests.
sharedAddF :: (Int, Int) -> (Int, Int)
sharedAddF (s, a) = let s' = s + a in (s', s')

-- | Function counterpart of 'sharedDoubleP' for premonoidal centrality tests.
sharedDoubleF :: (Int, Int) -> (Int, Int)
sharedDoubleF (s, _c) = let s' = s * 2 in (s', s')

-- | State-agnostic body: passes payload through unchanged.
bodyIdF :: (Int, Int) -> (Int, Int)
bodyIdF (s, a) = (s, a)

-- | State-agnostic body: increments the right payload, leaves state alone.
bodyIncF :: (Int, Int) -> (Int, Int)
bodyIncF (s, c) = (s, c + 1)

-- | Annotated helpers to avoid ambiguous overloads.
id1 :: FinRel N1 N1
id1 = finId

id2 :: FinRel N2 N2
id2 = finId

copy1 :: FinRel N1 (N1, N1)
copy1 = copy

copy2 :: FinRel N2 (N2, N2)
copy2 = copy

discard1 :: FinRel N1 ()
discard1 = discard

discard2 :: FinRel N2 ()
discard2 = discard

plus1 :: FinRel (N1, N1) N1
plus1 = plus

plus2 :: FinRel (N2, N2) N2
plus2 = plus

zero1 :: FinRel () N1
zero1 = zero

zero2 :: FinRel () N2
zero2 = zero

unitl1' :: FinRel N1 ((), N1)
unitl1' = unitl'FinRel

unitr1' :: FinRel N1 (N1, ())
unitr1' = unitr'FinRel

unitl2' :: FinRel N2 ((), N2)
unitl2' = unitl'FinRel

unitr2' :: FinRel N2 (N2, ())
unitr2' = unitr'FinRel

unitr0 :: FinRel ((), ()) ()
unitr0 = unitrFinRel

discard0 :: FinRel () ()
discard0 = discard

zero0 :: FinRel () ()
zero0 = zero

-- | Dagger(FinRel) collapse witness: 'Copy' on the dagger requires
-- 'Merge' on the base, so the back of @copy@ is @plus@.  The
-- constructors are pinned by type signatures so the instance method
-- resolves unambiguously.
daggerCopy1 :: Dagger (FinRel) N1 (N1, N1)
daggerCopy1 = copy

daggerDiscard1 :: Dagger (FinRel) N1 ()
daggerDiscard1 = discard

-- | 'check' for assertions that live in 'IO'.
checkIO :: String -> IO Bool -> IO Bool
checkIO name act = do
  ok <- act
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok

-- ---------------------------------------------------------------------------
-- ⅋ probe helpers
-- ---------------------------------------------------------------------------

-- | Body that preppoles a marker to the shared feedback list and emits the
-- first three elements.  Used to make the shared-medium interleaving observable.
markerBody :: Int -> ([Int], ()) -> ([Int], [Int])
markerBody n (ns, ()) = (n : ns, take 3 ns)

-- | Schedule that always runs the left body first without modifying the shared
-- state.  A pure order swap is invisible to the trace — this is the sliding
-- axiom of the traced category observed at the shared channel.
pureLeft :: Schedule [Int]
pureLeft = Schedule (,Both LeftFirst)

-- | Schedule that always runs the right body first without modifying the shared
-- state.
pureRight :: Schedule [Int]
pureRight = Schedule (,Both RightFirst)

-- | Schedule that always runs the left body first, leaving a neutral schedule
-- token in the shared state so the interleaving is observable.
leftFirst :: Schedule [Int]
leftFirst = Schedule $ \s -> (0 : s, Both LeftFirst)

-- | Schedule that always runs the right body first, leaving the same neutral
-- schedule token so the two orderings remain comparable on body sets.
rightFirst :: Schedule [Int]
rightFirst = Schedule $ \s -> (0 : s, Both RightFirst)

-- | Residual state for the pair-sum mealy process.
data PS = Empty | Held Int
  deriving (Eq, Show)

-- | Mealy process that forwards every input.
linearP :: Process Int (Maybe Int)
linearP = mealy () (\() a -> ((), Just a))

-- | Mealy process that sums consecutive pairs.
pairSumP :: Process Int (Maybe Int)
pairSumP = mealy Empty $ \s x -> case s of
  Empty -> (Held x, Nothing)
  Held y -> (Empty, Just (x + y))

-- | Mealy process that emits the count of inputs seen so far.
countP :: Process () (Maybe Int)
countP = mealy 0 (\n _ -> let n' = n + 1 in (n', Just n'))

-- | Premonoidal left-first product of two knot bodies.
--
-- This is the composite @(f ⊗ id) ; (id ⊗ g)@ in the category of knot bodies
-- @Body (,) s (->)@.  It threads the shared state through @f@ first, then @g@.
bodyParL :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, These b d))
bodyParL f g (s, (a, c)) =
  let (s', b) = f (s, a)
      (s'', d) = g (s', c)
   in (s'', These b d)

-- | Premonoidal right-first product of two knot bodies.
--
-- This is the composite @(id ⊗ g) ; (f ⊗ id)@.  It threads the shared state
-- through @g@ first, then @f@.
bodyParR :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, These b d))
bodyParR f g (s, (a, c)) =
  let (s', d) = g (s, c)
      (s'', b) = f (s', a)
   in (s'', These b d)

-- | Centrality of two knot bodies at a chosen input.
--
-- Two bodies are central when the premonoidal left-first and right-first
-- products agree.  For the cartesian instance @Body (,) s (->)@ this is the
-- statement that order of state threading is invisible.
bodyCentral :: (Eq s, Eq b, Eq d) => ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> (s, (a, c)) -> Bool
bodyCentral f g input = bodyParL f g input == bodyParR f g input

-- | Premonoidal left-first whiskering built from assoc / slide / first.
--
-- This is the composite @(f ⊗ id) ; (id ⊗ g)@ expressed with the cartesian
-- structural maps.  It threads state through @f@ first, then @g@.
whiskerL :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, (b, d)))
whiskerL f g =
  assoc' @(,) @(->)
    .> par @(,) @(->) f id
    .> assoc @(,) @(->)
    .> slide @(,) @(->)
    .> par @(,) @(->) id g
    .> slide @(,) @(->)

-- | Premonoidal right-first whiskering built from assoc / slide / first.
--
-- This is the composite @(id ⊗ g) ; (f ⊗ id)@.
whiskerR :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, (b, d)))
whiskerR f g =
  slide @(,) @(->)
    .> par @(,) @(->) id g
    .> slide @(,) @(->)
    .> assoc' @(,) @(->)
    .> par @(,) @(->) f id
    .> assoc @(,) @(->)

-- | Lift a payload map to a body that leaves shared state alone.
--
-- Such bodies are exactly the structural maps of the underlying category
-- threaded through the ambient state wire.
liftBody :: (a -> b) -> (s, a) -> (s, b)
liftBody f (s, a) = (s, f a)

-- | State-touching body with a pair payload: adds both components to state.
sharedAddFPair :: (Int, (Int, Int)) -> (Int, (Int, Int))
sharedAddFPair (s, (a, b)) = let s' = s + a + b in (s', (s', s'))

-- ---------------------------------------------------------------------------
-- Residual-oracle helpers
-- ---------------------------------------------------------------------------

-- | A synchronous identity-like 'K IO' end: writes are stored in an
-- 'IORef' and reads retrieve the most recently stored value.  This is the
-- effectful counterpart of the unit/copycat end: closing the two poles
-- yanks to the identity morphism.
mkIdentityEnd :: IO (Poles (K IO) Int Int)
mkIdentityEnd = do
  ref <- newIORef (0 :: Int)
  pure $ polesK (writeIORef ref) (readIORef ref)

main :: IO ()
main = do
  results <-
    sequence
      [ -- copy/discard comonoid laws
        check "copy coassociative (n=1)" $
          parFinRel copy1 id1 `compFinRel` copy1 == assoc'FinRel `compFinRel` parFinRel id1 copy1 `compFinRel` copy1,
        check "copy coassociative (n=2)" $
          parFinRel copy2 id2 `compFinRel` copy2 == assoc'FinRel `compFinRel` parFinRel id2 copy2 `compFinRel` copy2,
        check "copy left counit (n=1)" $
          parFinRel discard1 id1 `compFinRel` copy1 == unitl1',
        check "copy left counit (n=2)" $
          parFinRel discard2 id2 `compFinRel` copy2 == unitl2',
        check "copy right counit (n=1)" $
          parFinRel id1 discard1 `compFinRel` copy1 == unitr1',
        check "copy right counit (n=2)" $
          parFinRel id2 discard2 `compFinRel` copy2 == unitr2',
        check "copy cocommutative (n=1)" $
          swapFinRel `compFinRel` copy1 == copy1,
        check "copy cocommutative (n=2)" $
          swapFinRel `compFinRel` copy2 == copy2,
        -- plus/zero monoid laws
        check "plus associative (n=1)" $
          plus1 `compFinRel` parFinRel plus1 id1 == plus1 `compFinRel` parFinRel id1 plus1 `compFinRel` assocFinRel,
        check "plus associative (n=2)" $
          plus2 `compFinRel` parFinRel plus2 id2 == plus2 `compFinRel` parFinRel id2 plus2 `compFinRel` assocFinRel,
        check "plus left unit (n=1)" $
          plus1 `compFinRel` parFinRel zero1 id1 `compFinRel` unitl1' == id1,
        check "plus left unit (n=2)" $
          plus2 `compFinRel` parFinRel zero2 id2 `compFinRel` unitl2' == id2,
        check "plus right unit (n=1)" $
          plus1 `compFinRel` parFinRel id1 zero1 `compFinRel` unitr1' == id1,
        check "plus right unit (n=2)" $
          plus2 `compFinRel` parFinRel id2 zero2 `compFinRel` unitr2' == id2,
        check "plus commutative (n=1)" $
          plus1 `compFinRel` swapFinRel == plus1,
        check "plus commutative (n=2)" $
          plus2 `compFinRel` swapFinRel == plus2,
        -- bialgebra laws
        check "bialgebra copy-plus (n=1)" $
          copy1 `compFinRel` plus1 == parFinRel plus1 plus1 `compFinRel` swapMiddle `compFinRel` parFinRel copy1 copy1,
        check "bialgebra copy-plus (n=2)" $
          copy2 `compFinRel` plus2 == parFinRel plus2 plus2 `compFinRel` swapMiddle2 `compFinRel` parFinRel copy2 copy2,
        check "bialgebra discard-plus (n=1)" $
          discard1 `compFinRel` plus1 == unitr0 `compFinRel` parFinRel discard1 discard1,
        check "bialgebra discard-plus (n=2)" $
          discard2 `compFinRel` plus2 == unitr0 `compFinRel` parFinRel discard2 discard2,
        check "bialgebra zero-copy (n=1)" $
          copy1 `compFinRel` zero1 == parFinRel zero1 zero1 `compFinRel` unitr'FinRel,
        check "bialgebra zero-copy (n=2)" $
          copy2 `compFinRel` zero2 == parFinRel zero2 zero2 `compFinRel` unitr'FinRel,
        check "bialgebra discard-zero" $
          compFinRel discard0 zero0 == (finId :: FinRel () ()),
        -- scalar arithmetic over GF(2)
        check "scalar True is identity" $
          finScalar True == id1,
        check "scalar False is idempotent" $
          compFinRel (finScalar False :: FinRel N1 N1) (finScalar False) == finScalar False,
        check "scalar False absorbs scalar True" $
          compFinRel (finScalar False :: FinRel N1 N1) (finScalar True) == finScalar False,
        check "scalar True after scalar False" $
          compFinRel (finScalar True :: FinRel N1 N1) (finScalar False) == finScalar False,
        -- Dagger(FinRel k) collapse: the dagger instances interlock the
        -- ⊗-comonoid and the ⅋-monoid in a single construction.
        check "Dagger(FinRel) copy front is FinRel copy" $
          front daggerCopy1 == copy1,
        check "Dagger(FinRel) copy back is FinRel plus" $
          back daggerCopy1 == plus1,
        check "Dagger(FinRel) discard front is FinRel discard" $
          front daggerDiscard1 == discard1,
        check "Dagger(FinRel) discard back is FinRel zero" $
          back daggerDiscard1 == zero1,
        check "Dagger(FinRel) transpose copy has plus in front" $
          front (transpose daggerCopy1) == plus1,
        -- traced structure
        check "trace yanking (n=1)" $
          traceFinRel (swapFinRel :: FinRel (N1, N1) (N1, N1)) == id1,
        check "trace of identity pair" $
          traceFinRel (parFinRel id1 id1 :: FinRel (N1, N1) (N1, N1)) == id1,
        -- Para laws promoted to circuits-learn-axioma (11 Aug 2026).
        -- The L1/L2 constant-state trace checks now live there alongside
        -- the full Category associativity and identity oracles for Para.
        -- Circuit.Process oracles
        check "Process seed emits first output" $
          scan sumP [5] == [5],
        check "Process scan semantics" $
          scan sumP [1, 2, 3] == [1, 3, 6],
        check "Process fold semantics" $
          fold sumP [1, 2, 3] == Just 6,
        check "Process fold empty" $
          isNothing (fold sumP []),
        check "Process scan == run . encode" $
          Syn.eval (encode sumP) [1, 2, 3] == scan sumP [1, 2, 3],
        check "Process Traced (,) yanking" $
          scan (trace swapPairP) [1, 2, 3] == [1, 2, 3],
        check "Process Traced Either yanking" $
          scan (trace swapEitherP) [1, 2, 3] == [1, 2, 3],
        check "Process register (EWMA)" $
          scan (ewma 0.5 0.0) [1.0, 1.0, 1.0] == [0.5, 0.75, 0.875],
        check "Process register == trace . strength . delay (EWMA)" $
          let body = ewmaBody 0.5
              s0 = 0.0
              xs = [1.0, 1.0, 1.0]
              swapP (Process i st ex) =
                Process (i . Tuple.swap) (\s -> st s . Tuple.swap) (Tuple.swap . ex)
           in scan (register s0 body) xs
                == scan (trace (swapP (body . strength (delay s0)))) xs,
        -- Process / Body equivalence
        check "processToSomeBody sumP agrees with scan" $
          Body.runSomeBody (Process.processToSomeBody sumP) [1, 2, 3 :: Int] == scan sumP [1, 2, 3],
        check "processToSomeBody swapPairP agrees with scan" $
          Body.runSomeBody (Process.processToSomeBody swapPairP) [(1, 2), (3, 4), (5, 6)] == scan swapPairP [(1, 2), (3, 4), (5, 6)],
        check "processToSomeBody ewma agrees with scan" $
          Body.runSomeBody (Process.processToSomeBody (ewma 0.5 0.0)) [1.0, 1.0, 1.0] == scan (ewma 0.5 0.0) [1.0, 1.0, 1.0],
        -- Process / Trace Either round-trip factors through Body Either ch (->)
        check "Process encode factors through Body Either ch (->)" $
          let viaBody p = case Process.processToBody p of Body.SomeBody _ (Body.Body f) -> yank (base f)
           in scan sumP [1, 2, 3] == Syn.eval (viaBody sumP) [1, 2, 3]
                && scan swapPairP [(1, 2), (3, 4), (5, 6)] == Syn.eval (viaBody swapPairP) [(1, 2), (3, 4), (5, 6)]
                && scan (ewma 0.5 0.0) [1.0, 1.0, 1.0] == Syn.eval (viaBody (ewma 0.5 0.0)) [1.0, 1.0, 1.0],
        -- Process as a base arrow for Trace / Net / Shared
        check "Process lifts into Trace (,) Process" $
          scan (Syn.eval (base sumP :: Trace (,) Process Int Int)) [1, 2, 3]
            == scan sumP [1, 2, 3],
        check "Net (,) Process copy uses Process.copy" $
          let p = run (Net.Copy :: Net.Net (,) Process Int (Int, Int)) :: Process Int (Int, Int)
           in scan p [5] == [(5, 5)],
        check "Net (,) Process plus uses Process.plus" $
          let p = run (Net.Plus :: Net.Net (,) Process (Int, Int) Int) :: Process (Int, Int) Int
           in scan p [(2, 3)] == [5],
        check "Shared (,) Process LR order differs from RL" $
          let lr = sharedBy (Schedule (,Both LeftFirst) :: Schedule Int) sharedAddP sharedDoubleP
              rl = sharedBy (Schedule (,Both RightFirst) :: Schedule Int) sharedAddP sharedDoubleP
           in scan lr [(1, (2, 3))] == [(6, These 3 6)]
                && scan rl [(1, (2, 3))] == [(4, These 4 2)],
        -- Poles oracles
        check "O9 poles . splay == id" $
          let e :: Poles (->) () Int
              e = poles0 (const ()) (const 42)
              (write', receive') = splay0 e
              e' = poles0 write' receive'
           in box @() e' () == 42 && box @() e () == 42,
        check "annihilation: close on non-copycat end violates yanking" $
          let e :: Poles (->) Int Int
              e = poles0 (const ()) (const 42)
           in close (conjoint e) (companion e) 0 == 42
                && close (conjoint e) (companion e) 7 == 42,
        checkIO "residual observed: sequential boxes agree but residual is exposed" $ do
          ref <- newIORef (0 :: Int)
          let e1 :: Poles (K IO) Int Int
              e1 = polesK (\x -> modifyIORef' ref (+ x)) (pure 0)
              e2 :: Poles (K IO) Int Int
              e2 = polesK (\_ -> pure ()) (pure 1)
          r1 <- runK (box @() (Poles.compose0 e1 e2)) 5
          residual1 <- readIORef ref
          writeIORef ref 0
          r2 <- runK (box @() e2 . box @() e1) 5
          residual2 <- readIORef ref
          pure (r1 == r2 && r1 == 1 && residual1 == 5 && residual2 == 5),
        check "Bool as a non-terminal 'Poles' pole composes write then read" $
          let e :: Poles (->) Int Int
              e = poles @(->) @Int @Int @Bool (const False) (\b -> if b then 1 :: Int else 0)
              (w, r) = splay @(->) @Int @Int @Bool e
           in not (w 42) && r False == 0 && close (conjoint e) (companion e) 42 == 0,
        check "Bool copycat is not identity (Bool is not terminal)" $
          let e :: Poles (->) Bool Bool
              e = copycat @(->) @Bool
           in not (close (conjoint e) (companion e) True)
                && not (close (conjoint e) (companion e) False),
        -- Additive Poles oracles
        check "Additive Poles.pair pairs outputs" $
          let e1 :: Poles (->) () Int
              e1 = poles0 (const ()) (const 1)
              e2 :: Poles (->) () Int
              e2 = poles0 (const ()) (const 2)
           in box @() (Poles.pair e1 e2) () == (1, 2),
        check "Poles.race LeftFirst picks left when both speak" $
          let eL :: Poles (->) () (Maybe Int)
              eL = poles0 (const ()) (const (Just 1))
              eR :: Poles (->) () (Maybe Int)
              eR = poles0 (const ()) (const (Just 2))
           in box @() (Poles.race isNothing LeftFirst eL eR) () == Just 1,
        check "Poles.race RightFirst picks right when both speak" $
          let eL :: Poles (->) () (Maybe Int)
              eL = poles0 (const ()) (const (Just 1))
              eR :: Poles (->) () (Maybe Int)
              eR = poles0 (const ()) (const (Just 2))
           in box @() (Poles.race isNothing RightFirst eL eR) () == Just 2,
        check "Poles.race falls back when left is silent" $
          let eL :: Poles (->) () (Maybe Int)
              eL = poles0 (const ()) (const Nothing)
              eR :: Poles (->) () (Maybe Int)
              eR = poles0 (const ()) (const (Just 2))
           in box @() (Poles.race isNothing LeftFirst eL eR) () == Just 2
                && box @() (Poles.race isNothing RightFirst eL eR) () == Just 2,
        -- Stamped oracles
        check "Stamped fmap preserves stamp (Int token)" $
          let s = Stamped 7 ("hello" :: String)
           in stamp (fmap reverse s) == (7 :: Int) && stamped (fmap reverse s) == "olleh",
        check "Stamped fmap preserves stamp (Bool token)" $
          let s = Stamped True (10 :: Int)
           in stamp (fmap (+ 1) s) && stamped (fmap (+ 1) s) == 11,
        -- Boundary oracles
        check "Boundary fmap preserves Mark tag" $
          isMark (fmap length (Mark "halt" :: Boundary String String)),
        check "Boundary fmap acts on Payload" $
          let p = fmap length (Payload "hi" :: Boundary String String)
           in isPayload p && p == Payload 2,
        -- Mark system (circuits-residual §7)
        check "markSystem steps payloads through the inner system" $
          let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
              sys = markSystem (== "HALT") id innerSys
              p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
           in scan p (map Payload [1, 2, 3]) == [Just 1, Just 3, Just 6],
        check "markSystem halts on a halt mark and emits Nothing thereafter" $
          let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
              sys = markSystem (== "HALT") id innerSys
              p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
           in scan p [Payload 1, Payload 2, Mark "HALT", Payload 3] == [Just 1, Just 3, Nothing, Nothing],
        check "markSystem treats non-halt marks as no-ops" $
          let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
              sys = markSystem (== "HALT") id innerSys
              p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
           in scan p [Payload 1, Mark "NOOP", Payload 2] == [Just 1, Just 1, Just 3],
        check "markSystem halts immediately when the first input is a halt mark" $
          let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
              sys = markSystem (== "HALT") id innerSys
              p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
           in scan p [Mark "HALT", Payload 1] == [Nothing, Nothing],
        check "markSystem round-trips through systemToProcess" $
          let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
              sys = markSystem (== "HALT") id innerSys
              p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
           in scan p [] == [] && fold p [Payload 1, Payload 2, Mark "HALT"] == Just Nothing,
        -- Par / linear distributivity
        check "Par distL is the one-way (,) / Either distributor" $
          distL ('x', Left True :: Either Bool Int) == Left ('x', True)
            && distR (Left True :: Either Bool Int, 'x') == Left True,
        check "Par unitlP collapses Void on Either" $
          unitlP (Right 42 :: Either Void Int) == (42 :: Int),
        check "Par unitrP collapses Void on Either" $
          unitrP (Left 42 :: Either Int Void) == (42 :: Int),
        -- Channel These presence-preserving slide
        check "Channel These slide preserves presence on all 7 cases" $
          let presenceInput :: These Char (These Char Char) -> (Bool, Bool, Bool)
              presenceInput = \case
                This _ -> (True, False, False)
                That (This _) -> (False, True, False)
                That (That _) -> (False, False, True)
                That (These _ _) -> (False, True, True)
                These _ (This _) -> (True, True, False)
                These _ (That _) -> (True, False, True)
                These _ (These _ _) -> (True, True, True)
              presenceOutput :: These Char (These Char Char) -> (Bool, Bool, Bool)
              presenceOutput = \case
                This _ -> (False, True, False)
                That (This _) -> (True, False, False)
                That (That _) -> (False, False, True)
                That (These _ _) -> (True, False, True)
                These _ (This _) -> (True, True, False)
                These _ (That _) -> (False, True, True)
                These _ (These _ _) -> (True, True, True)
              cases :: [These Char (These Char Char)]
              cases =
                [ This 'a',
                  That (This 'b'),
                  That (That 'c'),
                  That (These 'b' 'c'),
                  These 'a' (This 'b'),
                  These 'a' (That 'c'),
                  These 'a' (These 'b' 'c')
                ]
           in all (\x -> presenceInput x == presenceOutput (slide x)) cases,
        check "Channel These slide . slide == id where types permit" $
          let x = These 'a' (These 'b' 'c' :: These Char Char)
           in (slide . slide) x == (x :: These Char (These Char Char)),
        -- Traced These falsifier: the both-branch forces a discard.
        --
        -- A candidate trace for These must choose, in the These a c case,
        -- whether to emit c (discarding a) or loop on a (discarding c).
        -- Two equally natural biased traces disagree, so no canonical trace
        -- exists; any fixed bias breaks sliding/dinaturality under composition.
        check "Traced These is impossible: biased traces disagree in the both-branch" $
          let traceTheseEmit f b = go (f (That b))
                where
                  go (That c) = c
                  go (This a) = go (f (This a))
                  go (These _ c) = c
              traceTheseLoop f b = go (f (That b))
                where
                  go (That c) = c
                  go (This a) = go (f (This a))
                  go (These a _) = go (f (This a))
              step :: These Int Int -> These Int Int
              step (That n) = These 1 n
              step (This 0) = That 0
              step (This n) = This (n - 1)
              step (These m n) = These (m + 1) n
           in traceTheseEmit step 5 /= traceTheseLoop step 5,
        -- ⊗/⅋ probe: sharedBy vs superpose
        check "pure order swap is invisible at the shared channel (sliding axiom)" $
          let k1 = markerBody 1
              k2 = markerBody 2
           in Syn.eval (yank (base (sharedBy pureLeft k1 k2))) ((), ())
                == Syn.eval (yank (base (sharedBy pureRight k1 k2))) ((), ()),
        check "sharedBy differs from superpose (shared vs independent feedback)" $
          let k1 = markerBody 1
              k2 = markerBody 2
              theseToPair (This a) = (a, [])
              theseToPair (That b) = ([], b)
              theseToPair (These a b) = (a, b)
           in Syn.eval (superpose (yank (base k1)) (yank (base k2))) ((), ())
                /= theseToPair (Syn.eval (yank (base (sharedBy leftFirst k1 k2))) ((), ())),
        check "sharedBy schedule changes observable interleaving" $
          let k1 = markerBody 1
              k2 = markerBody 2
           in Syn.eval (yank (base (sharedBy rightFirst k1 k2))) ((), ())
                /= Syn.eval (yank (base (sharedBy leftFirst k1 k2))) ((), ()),
        check "sharedBy Both LeftFirst equals premonoidal left-first product" $
          let k1 = markerBody 1
              k2 = markerBody 2
              input = ([], ((), ())) :: ([Int], ((), ()))
           in sharedBy (Schedule (,Both LeftFirst) :: Schedule [Int]) k1 k2 input == bodyParL k1 k2 input,
        check "sharedBy Both RightFirst equals premonoidal right-first product" $
          let k1 = markerBody 1
              k2 = markerBody 2
              input = ([], ((), ())) :: ([Int], ((), ()))
           in sharedBy (Schedule (,Both RightFirst) :: Schedule [Int]) k1 k2 input == bodyParR k1 k2 input,
        -- Gate: Bias = f⋉g / f⋊g means the hand-written products agree with
        -- sharedBy under the constant schedules pureLeft / pureRight.
        check "bodyParL equals sharedBy under pureLeft" $
          let k1 = markerBody 1
              k2 = markerBody 2
              input = ([], ((), ())) :: ([Int], ((), ()))
           in bodyParL k1 k2 input == sharedBy pureLeft k1 k2 input,
        check "bodyParR equals sharedBy under pureRight" $
          let k1 = markerBody 1
              k2 = markerBody 2
              input = ([], ((), ())) :: ([Int], ((), ()))
           in bodyParR k1 k2 input == sharedBy pureRight k1 k2 input,
        -- Gate: Bias is the premonoidal ordering iff the whiskerings agree.
        check "left-first whiskering equals bodyParL" $
          let k1 = markerBody 1
              k2 = markerBody 2
              input = ([], ((), ())) :: ([Int], ((), ()))
              (s, (b, d)) = whiskerL k1 k2 input
           in (s, These b d) == bodyParL k1 k2 input,
        check "right-first whiskering equals bodyParR" $
          let k1 = markerBody 1
              k2 = markerBody 2
              input = ([], ((), ())) :: ([Int], ((), ()))
              (s, (b, d)) = whiskerR k1 k2 input
           in (s, These b d) == bodyParR k1 k2 input,
        -- Centrality oracles: the ⊗/⅋ distinction is exactly premonoidal centrality
        -- Centrality witnesses: bodyCentral is a predicate at one input against
        -- one partner. These are existence witnesses, not proofs of ∀g.
        check "state-agnostic bodies witness centrality at a point" $
          let input = (0, (1, 2)) :: (Int, (Int, Int))
           in bodyCentral bodyIdF bodyIncF input,
        check "state-touching bodies witness non-centrality at a point" $
          let input = (1, (2, 3)) :: (Int, (Int, Int))
           in not (bodyCentral sharedAddF sharedDoubleF input),
        -- markerBody writes to the shared state, so these bodies are NOT central.
        -- What this oracle observes: after feedback closure, the two threading
        -- orders produce the same observable output (here, the same rotation of
        -- markers). This is a coincidence of the example, not Benton–Hyland
        -- centrality and not Centre Preservation (Def 3.2 runs the other way).
        check "marker bodies have equal trace under left-first and right-first threading (not centrality)" $
          let k1 = markerBody 1
              k2 = markerBody 2
           in Syn.eval (yank (base (bodyParL k1 k2))) ((), ())
                == Syn.eval (yank (base (bodyParR k1 k2))) ((), ()),
        -- Structural maps are central: they do not touch the shared state,
        -- so order of threading is invisible (Benton–Hyland centrality).
        check "copy witnesses centrality wrt state-touching body at a point" $
          let input = (0, (1, 2)) :: (Int, (Int, Int))
           in bodyCentral (liftBody (\x -> (x, x))) sharedAddF input,
        check "discard witnesses centrality wrt state-touching body at a point" $
          let input = (0, (1, 2)) :: (Int, (Int, Int))
           in bodyCentral (liftBody (const ())) sharedAddF input,
        check "plus witnesses centrality wrt state-touching body at a point" $
          let input = (0, ((1, 2), 3)) :: (Int, ((Int, Int), Int))
           in bodyCentral (liftBody (Pre.uncurry (+))) sharedAddF input,
        check "zero witnesses centrality wrt state-touching body at a point" $
          let input = (0, ((), 3)) :: (Int, ((), Int))
           in bodyCentral (liftBody (const (0 :: Int))) sharedAddF input,
        check "swap witnesses centrality wrt state-touching body at a point" $
          let input = (0, ((1, 2), (3, 4))) :: (Int, ((Int, Int), (Int, Int)))
           in bodyCentral (liftBody (\(a, b) -> (b, a))) sharedAddFPair input,
        -- Benton–Hyland Def 3.2: unrestricted sliding fails for non-central
        -- effectful morphisms. The witness uses two IO actions on a shared ref.
        checkIO "unrestricted sliding fails for non-central K IO" $
          do
            ref <- newIORef (1 :: Int)
            let f = K $ \ ~((), ()) -> do
                  v <- readIORef ref
                  modifyIORef' ref (+ 1)
                  pure ((), v)
                g = K $ \ ~() -> do
                  modifyIORef' ref (* 2)
                  pure ()
                post = trace (par @(,) @(K IO) g id . f)
                pre = trace (f . par @(,) @(K IO) g id)
            (l, r) <- (,) <$> runK post () <*> runK pre ()
            pure (l /= r),
        -- Body (,) (K IO) must compose as a category. This is the untested
        -- edge of parameterising Body over arr; Z2's Trace-level witness stands
        -- on it. The bodies touch a shared IORef to confirm composition threads
        -- state through the K base, not just the function base.
        checkIO "Body (,) (K IO) composes as a category" $
          do
            ref <- newIORef (0 :: Int)
            let f = Body.Body $ K $ \((s, a) :: (Int, Int)) -> do
                  writeIORef ref (s + 1)
                  pure (s + 1, a + 1)
                g = Body.Body $ K $ \(s, b) -> do
                  v <- readIORef ref
                  pure (s + v, b * 2)
                gf = g . f
            (sOut, c) <- runK (Body.morphism gf) (0, 5)
            pure (sOut == 2 && c == 12),
        -- Benton-Hyland Def 3.2 at the Trace level: Trace's trace inherits the
        -- Central Sliding side-condition from its base. A non-central effectful
        -- morphism g slid past f gives a different result depending on order.
        -- Trace's 'trace' discharges into the base 'trace', so the same witness
        -- that fails for K IO directly also fails for Trace (,) (K IO).
        checkIO "Trace trace requires centrality over K IO (Central Sliding)" $
          do
            ref <- newIORef 1
            let f = K $ \ ~((), ()) -> do
                  v <- readIORef ref
                  modifyIORef' ref (+ 1)
                  pure ((), v) :: IO ((), Int)
                g = K $ \ ~() -> do
                  modifyIORef' ref (* 2)
                  pure ()
                post = trace (base f . base (par @(,) @(K IO) g id)) :: Trace (,) (K IO) () Int
                pre = trace (base (par @(,) @(K IO) g id) . base f) :: Trace (,) (K IO) () Int
            l <- runK (Syn.eval post) ()
            writeIORef ref 1
            r <- runK (Syn.eval pre) ()
            pure (l /= r),
        -- Trace (.) preserves the semantic order of composed yank bodies over
        -- an effectful base. This is not a centrality claim; it just checks
        -- that Trace's normal form agrees with a hand-built body that threads
        -- state in the same order.
        checkIO "Trace (.) preserves semantic order of composed yank bodies" $
          do
            ref <- newIORef 1
            let g = K $ \ ~(s, a) -> do
                  v <- readIORef ref
                  writeIORef ref (v + 1)
                  pure (s, v + a)
                f = K $ \ ~(s, b) -> do
                  v <- readIORef ref
                  writeIORef ref (v * 2)
                  pure (s, v * b)
                loopFG = yank (base f) . yank (base g) :: Trace (,) (K IO) Int Int
                -- Same threading as Trace's (.) normal form: g's state wire first.
                handBuiltFG =
                  yank (base
                    (K $
                      \ ~((s1, s2), a) -> do
                        (s1', b) <- runK g (s1, a)
                        (s2', c) <- runK f (s2, b)
                        pure ((s1', s2'), c)))
            r1 <- runK (Syn.eval loopFG) 5
            writeIORef ref 1
            r2 <- runK (Syn.eval handBuiltFG) 5
            pure (r1 == r2),
        check "sharedBy L gates right body (output is This only)" $
          let k1 = markerBody 1
              k2 = markerBody 2
              leftOnly = Schedule (,L) :: Schedule [Int]
           in Syn.eval (yank (base (sharedBy leftOnly k1 k2))) ((), ()) == This [1, 1, 1],
        check "sharedBy R gates left body (output is That only)" $
          let k1 = markerBody 1
              k2 = markerBody 2
              rightOnly = Schedule (,R) :: Schedule [Int]
           in Syn.eval (yank (base (sharedBy rightOnly k1 k2))) ((), ()) == That [2, 2, 2],
        check "sharedBy left-first and right-first both agree on body sets" $
          let k1 = markerBody 1
              k2 = markerBody 2
              leftResult = Syn.eval (yank (base (sharedBy leftFirst k1 k2))) ((), ())
              rightResult = Syn.eval (yank (base (sharedBy rightFirst k1 k2))) ((), ())
              bodySet = sort . these id id (++)
           in bodySet leftResult == [0, 0, 1, 1, 2, 2]
                && bodySet rightResult == [0, 0, 1, 1, 2, 2],
        -- Free-syntax bridge: SigShared is the algebraic ⅋ connective
        check "AlgShared Syn.eval agrees with sharedBy" $
          let k1 = markerBody 1
              k2 = markerBody 2
              term :: Frag.AlgShared (,) (->) ((), ()) (These [Int] [Int])
              term =
                Frag.Op
                  ( Frag.R
                      ( Frag.R
                          ( Frag.Yank
                              ( Frag.Op
                                  ( Frag.R
                                      (Frag.L (Frag.SigShared pureLeft (Frag.Lift k1) (Frag.Lift k2)))
                                  )
                              )
                          )
                      )
                  )
           in Frag.eval term ((), ()) == Syn.eval (yank (base (sharedBy pureLeft k1 k2))) ((), ()),
        check "AlgShared L schedule gates right body" $
          let k1 = markerBody 1
              k2 = markerBody 2
              leftOnly = Schedule (,L) :: Schedule [Int]
              term :: Frag.AlgShared (,) (->) ((), ()) (These [Int] [Int])
              term =
                Frag.Op
                  ( Frag.R
                      ( Frag.R
                          ( Frag.Yank
                              ( Frag.Op
                                  ( Frag.R
                                      (Frag.L (Frag.SigShared leftOnly (Frag.Lift k1) (Frag.Lift k2)))
                                  )
                              )
                          )
                      )
                  )
           in Frag.eval term ((), ()) == This [1, 1, 1],
        check "AlgShared R schedule gates left body" $
          let k1 = markerBody 1
              k2 = markerBody 2
              rightOnly = Schedule (,R) :: Schedule [Int]
              term :: Frag.AlgShared (,) (->) ((), ()) (These [Int] [Int])
              term =
                Frag.Op
                  ( Frag.R
                      ( Frag.R
                          ( Frag.Yank
                              ( Frag.Op
                                  ( Frag.R
                                      (Frag.L (Frag.SigShared rightOnly (Frag.Lift k1) (Frag.Lift k2)))
                                  )
                              )
                          )
                      )
                  )
           in Frag.eval term ((), ()) == That [2, 2, 2],
        -- Mealy process oracles
        check "mealy linear forwards every input" $
          runMealy linearP [1, 2, 3 :: Int] == [1, 2, 3],
        check "mealy pairSum buffers and sums pairs" $
          runMealy pairSumP [1, 2, 3, 4 :: Int] == [3, 7],
        check "mealy pairSum leaves one input unemitted" $
          runMealy pairSumP [1, 2, 3 :: Int] == [3],
        check "mealy count emits accumulating count" $
          runMealy countP [(), (), ()] == [1, 2, 3],
        check "mealy scan matches runMealy" $
          catMaybes (scan pairSumP [1, 2, 3, 4 :: Int]) == runMealy pairSumP [1, 2, 3, 4],
        check "mealy process encodes to Trace Either" $
          Syn.eval (encode pairSumP) [1, 2, 3, 4 :: Int]
            == scan pairSumP [1, 2, 3, 4],
        -- Poly.Channel oracles (B2)
        check "Poly Channel id emits committed input" $
          case emitChannel (commitChannel (idChannel 0) (monoIn (42 :: Int))) of
            EP (EK o, EE _) -> o == 42,
        check "Poly Channel const ignores state" $
          case emitChannel (commitChannel (constChannel (7 :: Int)) (monoIn (99 :: Int))) of
            EP (EK o, EE _) -> o == 7,
        check "Poly Channel mapChannel applies lens forward and backward" $
          let ch0 = mapChannel (lens (+ 1) (\_ d -> d - 1 :: Int)) (idChannel 0)
              ev0 = emitChannel ch0
              ch1 = commitChannel ch0 (monoIn 5)
              ev1 = emitChannel ch1
           in case (ev0, ev1) of
                (EP (EK o0, EE _), EP (EK o1, EE _)) -> o0 == 1 && o1 == 5
      ]
  if and results
    then putStrLn "\nAll tests passed."
    else error "Some tests failed."
