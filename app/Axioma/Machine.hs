{-# LANGUAGE DataKinds #-}

-- | Machine and polynomial channel oracles.
module Axioma.Machine
  ( machineTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Machine (Machine (..), duplicateMachine, fromEvalMachine, machine, machineToClosed, monoIn, toEvalMachine)
import Circuit.Par (Par (..), distL, distR)
import Circuit.Poly (Eval (..), Mono, Poly (..))
import Circuit.Syntax (eval)
import Control.Category (id)
import Control.Exception (SomeException, evaluate, try)
import Control.Monad (replicateM, when)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

mkMachine :: (s -> a -> s) -> (s -> b) -> Machine (,) s (->) (Mono a b)
mkMachine st ex = fromEvalMachine $ \s -> EP (EK (ex s), EE (st s))

peekM :: Machine (,) s (->) (Mono i o) -> s -> o
peekM sys s = case toEvalMachine sys s of EP (EK o, EE _) -> o

stepM :: Machine (,) s (->) (Mono i o) -> s -> i -> s
stepM sys s i = case toEvalMachine sys s of EP (EK _, EE f) -> f i

runMono :: Machine (,) s (->) (Mono i o) -> s -> (o, i -> s)
runMono sys s = case toEvalMachine sys s of EP (EK o, EE f) -> (o, f)

-- * duplicateMachine law probes

-- | Output stream of an observable machine over an input stream: the
-- position after each step.
positionsOf :: Machine (,) s (->) (Mono o s) -> s -> [o] -> [s]
positionsOf sys = go
  where
    go _ [] = []
    go s (o : os) = let s' = stepM sys s o in peekM sys s' : go s' os

-- | Observe an expanded machine at a state: the current state and the
-- one-step transition it presents.
peek2 :: Machine (,) s (->) ('Comp (Mono o s) (Mono o s)) -> s -> (s, o -> s)
peek2 sys s = case toEvalMachine sys s of
  EC ((cur, ()), f) _ -> (cur, \o -> fst (f (monoIn o)))

-- | Step an expanded machine by one direction pair.
step2 :: Machine (,) s (->) ('Comp (Mono o s) (Mono o s)) -> s -> (o, o) -> s
step2 sys s (o1, o2) = case toEvalMachine sys s of
  EC _ g -> g (monoIn o1, monoIn o2)

-- | Position stream of an expanded machine over a stream of direction pairs.
positions2 :: Machine (,) s (->) ('Comp (Mono o s) (Mono o s)) -> s -> [(o, o)] -> [(s, o -> s)]
positions2 sys = go
  where
    go _ [] = []
    go s (p : ps) = let s' = step2 sys s p in peek2 sys s' : go s' ps

-- | All sixteen two-state two-direction transitions.
allTransitions :: [Bool -> Bool -> Bool]
allTransitions =
  [ \s o -> tb !! (2 * fromEnum s + fromEnum o)
  | tb <- replicateM 4 [False, True]
  ]

-- | All direction-pair streams up to length three.
allPairStreams :: [[(Bool, Bool)]]
allPairStreams =
  concat
    [ replicateM n [(False, False), (False, True), (True, False), (True, True)]
    | n <- [0 .. 3]
    ]

-- | The two-step machine: the expansion projected back to a monomial
-- (observable) interface.  'duplicateMachine' requires 'Mono' input and
-- produces 'Comp' output, so iteration goes through this projection — which
-- forgets the presented transition.
twoStep :: Machine (,) s (->) (Mono o s) -> Machine (,) s (->) (Mono (o, o) s)
twoStep sys = mkMachine (\s (o1, o2) -> stepM sys (stepM sys s o1) o2) id

machineTopic :: Verbosity -> IO [Bool]
machineTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Machine and Par oracles"
  sequence
    [ -- Par / linear distributivity
      checkV verbosity "Par distL is the one-way (,) / Either distributor" $
        distL ('x', Left True :: Either Bool Int) == Left ('x', True)
          && distR (Left True :: Either Bool Int, 'x') == Left True,
      checkV verbosity "Par unitlP collapses Void on Either" $
        unitlP (Right 42 :: Either Void Int) == (42 :: Int),
      checkV verbosity "Par unitrP collapses Void on Either" $
        unitrP (Left 42 :: Either Int Void) == (42 :: Int),
      -- Machine peek/step oracles
      checkV verbosity "peekM reads current output without consuming input" $
        let sys = mkMachine (\s i -> s + i) (\s -> s * 2) :: Machine (,) Int (->) (Mono Int Int)
         in peekM sys 5 == 10,
      checkV verbosity "stepM advances state by one input" $
        let sys = mkMachine (\s i -> s + i) (\s -> s * 2) :: Machine (,) Int (->) (Mono Int Int)
         in stepM sys 5 3 == 8,
      checkV verbosity "runMono exposes output and transition" $
        let sys = mkMachine (\s i -> s + i) (\s -> s * 2) :: Machine (,) Int (->) (Mono Int Int)
            (o, next) = runMono sys 5
         in o == 10 && next 3 == 8,
      checkV verbosity "Machine id lens emits committed input" $
        let sys = mkMachine (\_s d -> d) id :: Machine (,) Int (->) (Mono Int Int)
         in peekM sys (stepM sys 0 (42 :: Int)) == 42,
      checkV verbosity "Machine const lens ignores state" $
        let sys = mkMachine (\s _d -> s) (const (7 :: Int)) :: Machine (,) Int (->) (Mono Int Int)
         in peekM sys (stepM sys 0 (99 :: Int)) == 7,
      checkV verbosity "machineToClosed hides state as a feedback trace" $
        let sys = mkMachine (\_s d -> d) id :: Machine (,) Int (->) (Mono Int Int)
            tr = machineToClosed sys
         in eval tr (Right 42 :: Either Void Int) == (42 :: Int, ()),
      -- toEvalMachine Moore-ness side condition (Circuit.Machine:211-221).
      -- The conversion reads the position by probing with 'probeDir', which
      -- is an error thunk for the shapes where it is defined. A Moore body
      -- never forces the direction value, so a bounded run of probes must
      -- complete; a strict body forces the probe and the conversion becomes
      -- a runtime error rather than a wrong answer. Mutation room: if the
      -- conversion ever forces the probe (or probeDir is made strict), the
      -- bounded run below crashes the whole topic.
      checkV verbosity "toEvalMachine never forces the probe direction on a Moore body (bounded run)" $
        let sys = mkMachine (\s i -> s + i) (\s -> s * 2) :: Machine (,) Int (->) (Mono Int Int)
            states = iterate (\s -> stepM sys s 1) 0
            steps = [peekM sys s | s <- take 64 states]
         in head steps == 0 && last steps == 126,
      checkIOV verbosity "toEvalMachine on a strict body is a runtime error, not a wrong answer" $ do
        let strictSys :: Machine (,) Int (->) (Mono Int Int)
            strictSys =
              machine $ \case
                (s, Right i) -> i `seq` (s + i, (s, ()))
                (_, Left v) -> absurd v
        result <- try (evaluate (peekM strictSys 5)) :: IO (Either SomeException Int)
        pure (case result of Left _ -> True; Right _ -> False),
      -- duplicateMachine laws.  Two notes on what is NOT here:
      -- \* right identity collapses into left identity: the counit is
      --   observation, and at an observable machine observation is the
      --   identity function — both identity laws are the same equation, so
      --   the second would be defined-to-pass.
      -- \* associativity is inexpressible: duplicateMachine requires a Mono
      --   input and produces a Comp output, so it cannot be applied twice.
      --   Iteration goes through the 'twoStep' projection, which forgets
      --   the presented transition.
      --
      -- The law's shape is pinned by what the expansion IS: one pair-step
      -- is two original steps, so observation of the expansion samples the
      -- original's run at every second step.
      checkV verbosity "expansion presents state and transition (static counit)" $
        and
          [ fst (peek2 (duplicateMachine sys) s0) == s0
              && and [snd (peek2 (duplicateMachine sys) s0) o == stepM sys s0 o | o <- [False, True]]
          | t <- allTransitions,
            let sys = mkMachine t id :: Machine (,) Bool (->) (Mono Bool Bool),
            s0 <- [False, True]
          ],
      checkV verbosity "left identity: observing the expansion samples the original at every second step" $
        and
          [ let flat = concatMap (\(a, b) -> [a, b]) ps
                full = positionsOf sys s0 flat
             in map fst (positions2 (duplicateMachine sys) s0 ps)
                  == [full !! (2 * i + 1) | i <- [0 .. length ps - 1]]
          | t <- allTransitions,
            let sys = mkMachine t id :: Machine (,) Bool (->) (Mono Bool Bool),
            s0 <- [False, True],
            ps <- allPairStreams,
            not (null ps)
          ],
      checkV verbosity "machine maps: h commutes iff behaviors agree (xor/not vs xor/xnor)" $
        let xorT s o = s /= o
            xnorT s o = s == o
            sysXor = mkMachine xorT id :: Machine (,) Bool (->) (Mono Bool Bool)
            sysXnor = mkMachine xnorT id :: Machine (,) Bool (->) (Mono Bool Bool)
            streams = replicateM 3 [False, True]
            seeds = [False, True]
         in -- 'not' is a machine map xor -> xor ...
            and [positionsOf sysXor (not s0) os == map not (positionsOf sysXor s0 os) | s0 <- seeds, os <- streams]
              -- ... but not xor -> xnor, and the behaviors witness it
              && or [positionsOf sysXnor (not s0) os /= map not (positionsOf sysXor s0 os) | s0 <- seeds, os <- streams],
      checkV verbosity "duplicate preserves machine maps: expanded transitions commute iff h does" $
        let xorT s o = s /= o
            xnorT s o = s == o
            sysXor = mkMachine xorT id :: Machine (,) Bool (->) (Mono Bool Bool)
            sysXnor = mkMachine xnorT id :: Machine (,) Bool (->) (Mono Bool Bool)
            seeds = [False, True]
         in and
              [ snd (peek2 (duplicateMachine sysXor) (not s0)) o == not (snd (peek2 (duplicateMachine sysXor) s0) o)
              | s0 <- seeds,
                o <- seeds
              ]
              && or
                [ snd (peek2 (duplicateMachine sysXnor) (not s0)) o /= not (snd (peek2 (duplicateMachine sysXor) s0) o)
                | s0 <- seeds,
                  o <- seeds
                ],
      checkV verbosity "projected expansion = two-step machine (the tower iterates only through projection)" $
        and
          [ positionsOf (twoStep sys) s0 ps == map fst (positions2 (duplicateMachine sys) s0 ps)
          | t <- allTransitions,
            let sys = mkMachine t id :: Machine (,) Bool (->) (Mono Bool Bool),
            s0 <- [False, True],
            ps <- allPairStreams
          ],
      -- The comonoid reading: comonoids in (Poly, ◁, y) are small
      -- categories — counit is identities, comultiplication is composition.
      -- The lift of 'duplicateMachine' to a machine exists exactly when the
      -- transition is an action of the direction monoid.
      checkV verbosity "comonoid lift: a monoid-action transition passes the action laws" $
        let t s n = s + n :: Int
            states = [-2 .. 2]
            dirs = [0 .. 3]
         in and [t s 0 == s | s <- states]
              && and [t s (n + m) == t (t s n) m | s <- states, n <- dirs, m <- dirs],
      checkV verbosity "comonoid lift: a non-action transition has no identity direction (falsifier)" $
        let xorT s o = s /= o
            constF _s _o = False
            constT _s _o = True
            bools = [False, True]
            hasIdentity f = or [and [f s o0 == s | s <- bools] | o0 <- bools]
         in hasIdentity xorT && not (hasIdentity constF) && not (hasIdentity constT)
    ]
