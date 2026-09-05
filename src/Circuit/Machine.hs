{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | A machine fibered over a polynomial interface @p@.
--
-- @
--   newtype Machine t s arr p = Machine (Body t s arr (Dir p) (Pos p))
-- @
--
-- * The base is the state @s@.
-- * The fiber/interface is the polynomial @p@, with positions 'Pos' p and
--   directions 'Dir' p.
-- * The span shape is @s <- (s, Dir p) -> Pos p@.
-- * "Machine" because the observable output 'Pos' p depends on the state @s@,
--   not directly on the current input direction. The direction is consumed to
--   compute the next state; then the position is read from that state.
--
-- For a monomial @Mono i o@:
--
-- @
--   Dir (Mono i o) = i
--   Pos (Mono i o) = o
-- @
--
-- so @Machine (,) s (->) (Mono i o)@ collapses to the ordinary machine body
-- @(s, i) -> (s, o)@. The 'machine' constructor together with 'monoIn' /
-- 'monoDir' makes this explicit.
--
-- For a general polynomial @p@, 'Pos' p and 'Dir' p can be branching: the
-- polynomial layer handles sums and products of interfaces, so 'Machine' is a
-- machine that can branch, offer choices, or run parallel interfaces,
-- all while 'Circuit.Body.Body' handles the state transition.
--
-- In the BLLL picture (Katis–Sabadini–Walters), an F-machine is an
-- F-algebra @F E -> E@ plus an output @E -> O@. 'Machine' fits this with
-- state object @E = s@, endofunctor @F = (-) ⊗ Dir p@, transition
-- @d : s ⊗ Dir p -> s@, and output @obs : s -> Pos p@ bundled with the
-- transition in the 'Circuit.Body.Body'.
--
-- 'Circuit.Process.Mealy' is the pointed monomial special case: where
-- @Mealy@ is the existential form @∃s. (s, s -> a -> s, s -> b)@, 'Machine'
-- is the polynomial-lens form of the same idea, with @p@ describing the
-- interactive interface.
--
-- This module defines the 'Machine' type, conversions between eval and arrow
-- forms, wiring combinators, and higher-level execution combinators.
--
-- == Conversion ladder
--
-- The canonical conversion set: 'machine' in and 'machineMorphism' out;
-- 'Circuit.Process.asProcess' / 'Circuit.Process.machineAsMealy' to
-- processes and 'Circuit.Process.processAsMachine' back;
-- 'machineToPoles' / 'machineToPolesAt' to the equipment;
-- 'coalgebraToMachine' / 'machineToCoalgebraMono' to coalgebras.  The
-- pointed-process side of the ladder lives in "Circuit.Process".
module Circuit.Machine
  ( -- * machines
    Machine (..),
    Closed,
    machine,
    machineMorphism,
    machineToClosed,

    -- * Eval / arrow conversion
    MachineEval (..),
    fromEvalMachine,
    toEvalMachine,
    step,

    -- * Monomial helpers
    monoDir,
    monoIn,

    -- * Tensor wiring
    parWiringMachine,

    -- * Channel-pole view of machines
    machineToPoles,
    machineToPolesWithProbe,
    machineToPolesAt,

    -- * Comultiplication / duplication
    duplicateMachine,

    -- * Branches
    branchMachine,
    runMachineSum,
    branchMachineHet,
    runMachineSumHet,
    SumStep (..),

    -- * Coalgebras
    Coalgebra (..),
    coalgebraToMachine,
    composeCoalgebra,
    machineToCoalgebraMono,
  )
where

import Circuit.Body (Body (..))
import Circuit.Container (Located (..), SomePos (..), posAt, posOf)
import Circuit.Equip (Poles (..))
import Circuit.Poly
  ( Dir,
    Eval (..),
    Mono,
    Morphism (..),
    Netlist,
    Poly (..),
    Pos,
    nestedToComp,
    runMorphism,
  )
import Circuit.Trace (Trace, base)
import Circuit.Traced (Yank, yank)
import Control.Category ((.))
import Data.Kind (Type)
import Data.Void (absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Category (Op (..))
-- >>> import Circuit.Equip (Poles (..))
-- >>> import Circuit.Poly (Dir, Eval (..), Mono, Morphism, Poly (..), Pos, lens, applyLens)
-- >>> import Circuit.Container (SomePos (..), posOf)
-- >>> import Circuit.Machine (Machine, machine, machineMorphism, machineToPolesAt, branchMachine, MachineEval (..), toEvalMachine, fromEvalMachine, monoDir, monoIn, parWiringMachine)
-- >>> import Circuit.Process (runBody)
-- >>> import Data.Void (absurd)

-- | A machine with interface @p@, carrier @s@, over base arrow @arr@,
-- parameterised by the state-pairing tensor @t@.
--
-- Uncurried netlist form: the state and the current input direction are fed
-- together under @t@, and the result is the next state together with the current
-- output position.  For the monomial @Mono i o@ and @t = (,)@ this is exactly
-- the Machine body @arr (s, i) (s, o)@ after collapsing the unit positions.
--
-- In the equipment-optics vocabulary this is the span
--
-- @
--   s <- (t s (Dir p)) -Pos p->
-- @
--
-- expressed inside 'Circuit.Body.Body': the residual is the state @s@, the left
-- leg returns the next state, and the right leg is the observable position.
-- The input direction is part of the apex together with the residual.
--
-- The opposite arrow @Circuit.Category.Op arr@ is also supported, so
-- @Machine t s (Op (->)) p@ is a first-class codata body.  Together with the
-- forward @(->)@ case this reproduces the @Fam(Set^op)@ rung of polynomial
-- equipment.
--
-- In the equipment-optic reading, the companion/conjoint poles of a
-- 'Machine' over carrier @s@ are the 'Circuit.Optic.opticPolesP' action of
-- a pointed optic whose residual is the machine's state; the coherence is
-- oracled in @Axioma.Optic@.
--
-- >>> let sys = machine (\case (_, Left v) -> absurd v; (s, Right i) -> (s + i, (s * 2, ()))) :: Machine (,) Int (->) (Mono Int Int)
-- >>> machineMorphism sys (3, Right 5)
-- (8,(6,()))
newtype Machine (t :: Type -> Type -> Type) s (arr :: Type -> Type -> Type) (p :: Poly)
  = Machine (Body t s arr (Dir p) (Pos p))

-- | A machine with hidden carrier, represented as a trace over the
-- polynomial interface.
--
-- This is the unpointed counterpart of 'Machine': the state carrier is not a
-- type parameter; instead it is folded into the feedback wire of the trace.
-- 'machineToClosed' embeds a pointed 'Machine' into this form by closing the
-- state channel with 'yank'.
--
-- This is the closure discharge of pointing: the run takes no seed, and that
-- is visible in the type. See 'Circuit.Equip.UnitCell' for the taxonomy.
type Closed t arr p = Trace t arr (Dir p) (Pos p)

-- | Convert a pointed 'Machine' into a hidden-state 'Closed' by closing the
-- state feedback wire.
machineToClosed ::
  (Circuit.Traced.Yank t arr) =>
  Machine t s arr p ->
  Closed t arr p
machineToClosed (Machine (Body f)) = yank (base f)

-- | Construct a cartesian 'Machine' from its underlying arrow.
machine :: arr (s, Dir p) (s, Pos p) -> Machine (,) s arr p
machine = Machine . Body

-- | Inspect a cartesian 'Machine' as its underlying arrow.
machineMorphism :: Machine (,) s arr p -> arr (s, Dir p) (s, Pos p)
machineMorphism (Machine (Body f)) = f

-- | Extract the monomial direction from its 'Either Void' encoding.
monoDir :: Dir (Mono i o) -> i
monoDir (Right i) = i
monoDir (Left v) = absurd v

-- | Inject a monomial direction into its 'Either Void' encoding.
monoIn :: i -> Dir (Mono i o)
monoIn = Right

-- | Convert an eval-form @(->)@ machine into the arrow form.
fromEvalMachine :: (MachineEval p) => (s -> Eval p s) -> Machine (,) s (->) p
fromEvalMachine f = machine $ \(s, d) ->
  let (pos, next) = evalToMachine (f s)
   in (next d, pos)

-- | Convert an arrow-form @(->)@ machine back into eval form.
--
-- This is a Machine observation: the position is read from the state alone, with
-- the direction supplied only to compute the next state.  Correctness therefore
-- requires that the machine be Machine at the call site — the position must not
-- depend on the direction.  Internally the direction is 'probeDir', which is
-- lazily unused for the polynomial shapes where it is defined; any strict
-- forcing of the direction (a bang pattern, 'seq', or a strict tuple in a
-- user-written body) will turn 'toEvalMachine' into a runtime error rather than
-- a wrong answer.
toEvalMachine :: forall p s. (MachineEval p) => Machine (,) s (->) p -> s -> Eval p s
toEvalMachine sys s = evalFromMachine pos (\d -> fst (machineMorphism sys (s, d)))
  where
    pos = snd (machineMorphism sys (s, probeDir @p))

-- | Run one step: observe the current @p@-output from state @s@.
step :: (MachineEval p) => Machine (,) s (->) p -> s -> Eval p s
step = toEvalMachine

-- | Helpers for translating between the 'Eval' presentation and the arrow
-- presentation of a @(->)@ machine.  These extend the netlist view to 'Sum'.
class MachineEval (p :: Poly) where
  evalToMachine :: Eval p x -> (Pos p, Dir p -> x)
  evalFromMachine :: Pos p -> (Dir p -> x) -> Eval p x
  probeDir :: Dir p

instance MachineEval 'Y where
  evalToMachine (EY x) = ((), \() -> x)
  evalFromMachine () k = EY (k ())
  probeDir = ()

instance MachineEval ('Const a) where
  evalToMachine (EK c) = (c, absurd)
  evalFromMachine c _ = EK c
  probeDir = error "probeDir Const"

instance MachineEval ('Exp a) where
  evalToMachine (EE f) = ((), f)
  evalFromMachine () = EE
  probeDir = error "probeDir Exp"

instance (MachineEval p, MachineEval q) => MachineEval ('Sum p q) where
  evalToMachine (ES (Left v)) =
    let (i, f) = evalToMachine v
     in (Left i, either f (const offFibre))
  evalToMachine (ES (Right w)) =
    let (j, g) = evalToMachine w
     in (Right j, either (const offFibre) g)
  evalFromMachine (Left i) k = ES (Left (evalFromMachine i (k . Left)))
  evalFromMachine (Right j) k = ES (Right (evalFromMachine j (k . Right)))
  probeDir :: Dir ('Sum p q)
  probeDir = Left (probeDir @p)

instance (MachineEval p, MachineEval q) => MachineEval ('Prod p q) where
  evalToMachine (EP (u, v)) =
    let (i, f) = evalToMachine u
        (j, g) = evalToMachine v
     in ((i, j), either f g)
  evalFromMachine (i, j) k =
    EP (evalFromMachine i (k . Left), evalFromMachine j (k . Right))
  probeDir :: Dir ('Prod p q)
  probeDir = Left (probeDir @p)

instance (MachineEval p, MachineEval q) => MachineEval ('PTensor p q) where
  evalToMachine (ET pos f) = (pos, f)
  evalFromMachine = ET
  probeDir :: Dir ('PTensor p q)
  probeDir = (probeDir @p, probeDir @q)

instance (MachineEval p, MachineEval q) => MachineEval ('Comp p q) where
  evalToMachine (EC pos f) = (pos, f)
  evalFromMachine = EC
  probeDir :: Dir ('Comp p q)
  probeDir = (probeDir @p, probeDir @q)

-- | Monomial evaluation.  The position is the current-state observation, so
-- the probe direction is only needed to build the transition function and is
-- never forced when reading the position.
instance {-# OVERLAPPING #-} MachineEval (Mono i o) where
  evalToMachine (EP (EK o, EE f)) = ((o, ()), f . monoDir)
  evalFromMachine (o, ()) k = EP (EK o, EE (k . monoIn))
  probeDir :: Dir (Mono i o)
  probeDir = Right (error "probeDir Mono")

offFibre :: a
offFibre = error "off-fibre direction"

-- | Place two machines side by side: interface @p ⊗ q@, state @(s, t)@.
--
-- This is the entry point for acyclic wiring over the Dirichlet tensor —
-- boxes in parallel, pins assigned jointly.  The wired interface can be
-- mapped with 'parT' (wire-then-map).
parWiringMachine :: Machine (,) s (->) p -> Machine (,) t (->) q -> Machine (,) (s, t) (->) (PTensor p q)
parWiringMachine sp sq =
  machine $ \((s, t), (dp, dq)) ->
    let (s', posP) = machineMorphism sp (s, dp)
        (t', posQ) = machineMorphism sq (t, dq)
     in ((s', t'), (posP, posQ))

-- * Channel-pole view of machines

-- | Shared write pole for a @(->)@ machine over @(,)@: run the step and
-- post the new state into the carrier.
machineWriteStateBody :: Machine (,) s (->) p -> Body (,) s (->) (Dir p) s
machineWriteStateBody sys = Body $ \(s, d) ->
  let (s', _) = machineMorphism sys (s, d)
   in (s', s')

-- | Convert a @(->)@ 'Machine' into companion/conjoint channel poles over @Body@.
--
-- The write pole runs the step and posts the new state into the carrier; the
-- read pole fabricates an observation by re-stepping the machine with the
-- supplied probe direction. This works only when the read can be reasonably
-- approximated by a single probe direction; for an honest Machine observation
-- prefer 'machineToPoles'.
machineToPolesWithProbe :: Dir p -> Machine (,) s (->) p -> Poles s s (Body (,) s (->)) (Body (,) s (->)) (Dir p) (Pos p)
machineToPolesWithProbe probe sys =
  Poles
    (machineWriteStateBody sys)
    (Body $ \(_, ch) -> machineMorphism sys (ch, probe))

-- | Convert a pointed 'Machine' into companion/conjoint channel poles over @Body@.
--
-- The state carrier is the machine's state @s@.  The write pole steps with the
-- supplied direction and posts the new state; the read pole observes the
-- carrier without stepping, using the supplied observation function.
machineToPoles :: (s -> Pos p) -> Machine (,) s (->) p -> Poles s s (Body (,) s (->)) (Body (,) s (->)) (Dir p) (Pos p)
machineToPoles ex sys =
  Poles
    (machineWriteStateBody sys)
    (Body $ \(s, ch) -> (s, ex ch))

-- | Convert a 'Machine' into companion/conjoint poles over the /position
-- carrier/ 'SomePos' p — the honest grade of the polynomial pole.
--
-- The flat grade ('machineToPoles', 'machineToPolesWithProbe') needed an
-- observation argument because its carrier carried no position: the read
-- leg either consulted a supplied function or fabricated an observation by
-- re-stepping.  The 'SomePos' carrier /is/ a position, so no observation
-- argument is needed — the signature shrinks, which is the stamp of the
-- honest grade.
-- The write leg steps and posts 'posAt' of the new position; the read leg
-- recovers the position from the carrier it is handed, without stepping.
--
-- The write leg on a branched machine: the carrier records the branch and
-- payload of the position the step landed in:
--
-- >>> let inc = machine (\case (s, Left v) -> absurd v; (s, Right i) -> (s + i, (s, ()))) :: Machine (,) Int (->) (Mono Int Int)
-- >>> let dbl = machine (\case (s, Left v) -> absurd v; (s, Right i) -> (s + i, (s * 2, ()))) :: Machine (,) Int (->) (Mono Int Int)
-- >>> let br = branchMachine odd inc dbl :: Machine (,) Int (->) ('Sum (Mono Int Int) (Mono Int Int))
-- >>> let p = machineToPolesAt br
-- >>> map (\(SomePos i) -> posOf i) (runBody (conjoint p) 1 [Left (Right 1), Right (Right 1), Left (Right 1)])
-- [Left (1,()),Right (4,()),Left (3,())]
machineToPolesAt ::
  forall p s.
  (Located p) =>
  Machine (,) s (->) p ->
  Poles (SomePos p) (SomePos p) (Body (,) s (->)) (Body (,) s (->)) (Dir p) (Pos p)
machineToPolesAt sys =
  Poles
    (Body $ \(s, d) -> let (s', pos) = machineMorphism sys (s, d) in (s', posAt @p pos))
    (Body $ \(s, ch) -> (s, case ch of SomePos i -> posOf i))

-- | Comultiplication for an /observable/ machine: the output position is the
-- state. The result is a machine over the two-step interface
-- @Mono o s ◁ Mono o s@, so that feeding a pair of inputs @(o1, o2)@ runs the
-- original machine for two steps.
duplicateMachine :: Machine (,) s (->) (Mono o s) -> Machine (,) s (->) ('Comp (Mono o s) (Mono o s))
duplicateMachine sys =
  fromEvalMachine $ \s ->
    let runMono s' = case toEvalMachine sys s' of EP (EK o, EE f) -> (o, f)
        (s0, nextStep) = runMono s
        nextEval o =
          let (s1, step1) = runMono (nextStep o)
           in EP (EK s1, EE step1)
     in nestedToComp (EP (EK s0, EE nextEval))

-- | Build a machine whose interface is the coproduct of two monomial interfaces.
--
-- The carrier state selects the active branch at each step.  This is the
-- level-2 grammar operator on the span fragment: choice lives in the
-- polynomial interface ('Sum') rather than in the carrier-level 'if'.
branchMachine ::
  (s -> Bool) ->
  Machine (,) s (->) (Mono i o) ->
  Machine (,) s (->) (Mono i o) ->
  Machine (,) s (->) ('Sum (Mono i o) (Mono i o))
branchMachine cond sysL sysR =
  fromEvalMachine $ \s ->
    if cond s
      then ES (Left (toEvalMachine sysL s))
      else ES (Right (toEvalMachine sysR s))

-- | Run a machine with a homogeneous sum-of-monomials interface.
runMachineSum ::
  Machine (,) s (->) ('Sum (Mono i o) (Mono i o)) ->
  s ->
  (Either o o, i -> s)
runMachineSum sys s = case toEvalMachine sys s of
  ES (Left (EP (EK o, EE f))) -> (Left o, f)
  ES (Right (EP (EK o, EE f))) -> (Right o, f)

-- | A single step of a heterogeneous sum-interface machine.  The GADT encodes
-- the position-dependent input type: the left branch consumes an @i1@, the
-- right branch consumes an @i2@.
data SumStep s o1 i1 o2 i2 where
  SumStepL :: o1 -> (i1 -> s) -> SumStep s o1 i1 o2 i2
  SumStepR :: o2 -> (i2 -> s) -> SumStep s o1 i1 o2 i2

-- | Build a machine whose interface is the coproduct of two /different/
-- monomial interfaces.  The carrier state selects the active branch at each
-- step.
branchMachineHet ::
  (s -> Bool) ->
  Machine (,) s (->) (Mono i1 o1) ->
  Machine (,) s (->) (Mono i2 o2) ->
  Machine (,) s (->) ('Sum (Mono i1 o1) (Mono i2 o2))
branchMachineHet cond sysL sysR =
  fromEvalMachine $ \s ->
    if cond s
      then ES (Left (toEvalMachine sysL s))
      else ES (Right (toEvalMachine sysR s))

-- | Run a heterogeneous sum-interface machine.
runMachineSumHet ::
  Machine (,) s (->) ('Sum (Mono i1 o1) (Mono i2 o2)) ->
  s ->
  SumStep s o1 i1 o2 i2
runMachineSumHet sys s = case toEvalMachine sys s of
  ES (Left (EP (EK o, EE f))) -> SumStepL o f
  ES (Right (EP (EK o, EE f))) -> SumStepR o f

-- | Spivak's @[p,q]@-coalgebra. State @s@ is runtime, not a type index.
--
-- * 'act' gives the wiring pattern as a polynomial morphism.
-- * 'upd' takes a state and an input observation in @p@ and returns an output
--   observation in @q@, i.e. an 'Eval' pairing the presented position with its
--   own direction consumer.
data Coalgebra s p q = Coalgebra
  { act :: s -> Morphism p q,
    upd :: s -> Eval p s -> Eval q s
  }

-- | Run a @Coalgebra s 'Y q@ as a 'Machine' over @q@.
coalgebraToMachine :: (MachineEval q) => Coalgebra s 'Y q -> Machine (,) s (->) q
coalgebraToMachine coal = fromEvalMachine $ \s -> upd coal s (EY s)

-- | Convert a monomial 'Machine' into a @Coalgebra s 'Y (Mono i o)@.
machineToCoalgebraMono :: Machine (,) s (->) (Mono i o) -> Coalgebra s 'Y (Mono i o)
machineToCoalgebraMono sys =
  Coalgebra
    { act = \s ->
        let runMono s' = case toEvalMachine sys s' of EP (EK o, EE _) -> o
         in Point (EP (EK (runMono s), EE (const ()))),
      upd = \s _ -> toEvalMachine sys s
    }

-- | Sequential composition of two closed coalgebras via the composition product.
composeCoalgebra ::
  (Netlist p, Netlist q) =>
  Coalgebra s 'Y p ->
  Coalgebra t 'Y q ->
  Coalgebra (s, t) 'Y (Comp p q)
composeCoalgebra coalP coalQ =
  Coalgebra
    { act = \(s, t) ->
        let pPoint = runMorphism (act coalP s) (EY ())
            qPoint = runMorphism (act coalQ t) (EY ())
         in Point (nestedToComp (fmap (const qPoint) pPoint)),
      upd = \(s, t) _ ->
        let pVal = upd coalP s (EY s)
            qVal = upd coalQ t (EY t)
         in nestedToComp (fmap (\s' -> fmap (s',) qVal) pVal)
    }
