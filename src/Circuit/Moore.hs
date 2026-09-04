{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | A MachineP machine fibered over a polynomial interface @p@.
--
-- @
--   newtype MachineP t s arr p = MachineP (Body t s arr (Dir p) (Pos p))
-- @
--
-- * The base is the state @s@.
-- * The fiber/interface is the polynomial @p@, with positions 'Pos' p and
--   directions 'Dir' p.
-- * The span shape is @s <- (s, Dir p) -> Pos p@.
-- * "MachineP" because the observable output 'Pos' p depends on the state @s@,
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
-- so @MachineP (,) s (->) (Mono i o)@ collapses to the ordinary MachineP body
-- @(s, i) -> (s, o)@. The 'machineP' constructor together with 'monoIn' /
-- 'monoDir' makes this explicit.
--
-- For a general polynomial @p@, 'Pos' p and 'Dir' p can be branching: the
-- polynomial layer handles sums and products of interfaces, so 'MachineP' is a
-- MachineP machine that can branch, offer choices, or run parallel interfaces,
-- all while 'Circuit.Body.Body' handles the state transition.
--
-- In the BLLL picture (Katis–Sabadini–Walters), an F-MachineP machine is an
-- F-algebra @F E -> E@ plus an output @E -> O@. 'MachineP' fits this with
-- state object @E = s@, endofunctor @F = (-) ⊗ Dir p@, transition
-- @d : s ⊗ Dir p -> s@, and output @obs : s -> Pos p@ bundled with the
-- transition in the 'Circuit.Body.Body'.
--
-- 'Circuit.Process.Process' is the pointed monomial special case: where
-- @Process@ is the existential form @∃s. (s, s -> a -> s, s -> b)@, 'MachineP'
-- is the polynomial-lens form of the same idea, with @p@ describing the
-- interactive interface.
--
-- This module defines the 'MachineP' type, conversions between eval and arrow
-- forms, wiring combinators, and higher-level execution combinators.
module Circuit.Moore
  ( -- * MachineP machines
    MachineP (..),
    Machine (..),
    machineP,
    machineMorphismP,
    machinePToMachine,

    -- * Eval / arrow conversion
    MooreEval (..),
    fromEvalMachineP,
    toEvalMachineP,
    step,

    -- * Monomial helpers
    monoDir,
    monoIn,

    -- * Tensor wiring
    parWiringMachineP,

    -- * Channel-pole view of MachineP machines
    machinePToPoles,
    machinePToPolesWithProbe,

    -- * Comultiplication / duplication
    duplicateMachineP,

    -- * Branches
    branchMachineP,
    runMachinePSum,
    branchMachinePHet,
    runMachinePSumHet,
    SumStep (..),

    -- * Coalgebras
    Coalgebra (..),
    coalgebraToMoore,
    composeCoalgebra,
    machinePToCoalgebraMono,
  )
where

import Circuit.Body (Body (..))
import Circuit.Equip (Poles (..))
import Circuit.Equip qualified as Poles
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
import Control.Category (Category, id, (.))
import Data.Bifunctor
import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Category (Op (..))
-- >>> import Circuit.Poly (Eval (..), Mono, Morphism, lens, applyLens)
-- >>> import Circuit.Moore (MachineP, machineP, machineMorphismP, MooreEval (..), toEvalMachineP, fromEvalMachineP, monoDir, monoIn, parWiringMachineP)
-- >>> import Data.Void (absurd)

-- | A MachineP machine with interface @p@, carrier @s@, over base arrow @arr@,
-- parameterised by the state-pairing tensor @t@.
--
-- Uncurried netlist form: the state and the current input direction are fed
-- together under @t@, and the result is the next state together with the current
-- output position.  For the monomial @Mono i o@ and @t = (,)@ this is exactly
-- the MachineP body @arr (s, i) (s, o)@ after collapsing the unit positions.
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
-- @MachineP t s (Op (->)) p@ is a first-class codata body.  Together with the
-- forward @(->)@ case this reproduces the @Fam(Set^op)@ rung of polynomial
-- equipment.
--
-- >>> let sys = machineP (\case (_, Left v) -> absurd v; (s, Right i) -> (s + i, (s * 2, ()))) :: MachineP (,) Int (->) (Mono Int Int)
-- >>> machineMorphismP sys (3, Right 5)
-- (8,(6,()))
newtype MachineP (t :: Type -> Type -> Type) s (arr :: Type -> Type -> Type) (p :: Poly)
  = MachineP (Body t s arr (Dir p) (Pos p))

-- | A MachineP machine with hidden carrier, represented as a trace over the
-- polynomial interface.
--
-- This is the unpointed counterpart of 'MachineP': the state carrier is not a
-- type parameter; instead it is folded into the feedback wire of the trace.
-- 'machinePToMachine' embeds a pointed 'MachineP' into this form by closing the state
-- channel with 'yank'.
--
-- This is the closure discharge of pointing: the run takes no seed, and that
-- is visible in the type. See 'Circuit.Equip.UnitCell' for the taxonomy.
newtype Machine (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) (p :: Poly)
  = Machine (Trace t arr (Dir p) (Pos p))

-- | Convert a pointed 'MachineP' into a hidden-state 'Machine' by closing the state
-- feedback wire.
machinePToMachine ::
  (Circuit.Traced.Yank t arr) =>
  MachineP t s arr p ->
  Machine t arr p
machinePToMachine (MachineP (Body f)) = Machine (yank (base f))

-- | Construct a cartesian 'MachineP' from its underlying arrow.
machineP :: arr (s, Dir p) (s, Pos p) -> MachineP (,) s arr p
machineP = MachineP . Body

-- | Inspect a cartesian 'MachineP' as its underlying arrow.
machineMorphismP :: MachineP (,) s arr p -> arr (s, Dir p) (s, Pos p)
machineMorphismP (MachineP (Body f)) = f

-- | Extract the monomial direction from its 'Either Void' encoding.
monoDir :: Dir (Mono i o) -> i
monoDir (Right i) = i
monoDir (Left v) = absurd v

-- | Inject a monomial direction into its 'Either Void' encoding.
monoIn :: i -> Dir (Mono i o)
monoIn = Right

-- | Convert an eval-form @(->)@ MachineP machine into the arrow form.
fromEvalMachineP :: (MooreEval p) => (s -> Eval p s) -> MachineP (,) s (->) p
fromEvalMachineP f = machineP $ \(s, d) ->
  let (pos, next) = evalToMoore (f s)
   in (next d, pos)

-- | Convert an arrow-form @(->)@ MachineP machine back into eval form.
--
-- This is a MachineP observation: the position is read from the state alone, with
-- the direction supplied only to compute the next state.  Correctness therefore
-- requires that the machine be MachineP at the call site — the position must not
-- depend on the direction.  Internally the direction is 'probeDir', which is
-- lazily unused for the polynomial shapes where it is defined; any strict
-- forcing of the direction (a bang pattern, 'seq', or a strict tuple in a
-- user-written body) will turn 'toEvalMachineP' into a runtime error rather than
-- a wrong answer.
toEvalMachineP :: forall p s. (MooreEval p) => MachineP (,) s (->) p -> s -> Eval p s
toEvalMachineP sys s = evalFromMoore pos (\d -> fst (machineMorphismP sys (s, d)))
  where
    pos = snd (machineMorphismP sys (s, probeDir @p))

-- | Run one step: observe the current @p@-output from state @s@.
step :: (MooreEval p) => MachineP (,) s (->) p -> s -> Eval p s
step = toEvalMachineP

-- | Helpers for translating between the 'Eval' presentation and the arrow
-- presentation of a @(->)@ MachineP machine.  These extend the netlist view to 'Sum'.
class MooreEval (p :: Poly) where
  evalToMoore :: Eval p x -> (Pos p, Dir p -> x)
  evalFromMoore :: Pos p -> (Dir p -> x) -> Eval p x
  probeDir :: Dir p

instance MooreEval 'Y where
  evalToMoore (EY x) = ((), \() -> x)
  evalFromMoore () k = EY (k ())
  probeDir = ()

instance MooreEval ('Const a) where
  evalToMoore (EK c) = (c, absurd)
  evalFromMoore c _ = EK c
  probeDir = error "probeDir Const"

instance MooreEval ('Exp a) where
  evalToMoore (EE f) = ((), f)
  evalFromMoore () = EE
  probeDir = error "probeDir Exp"

instance (MooreEval p, MooreEval q) => MooreEval ('Sum p q) where
  evalToMoore (ES (Left v)) =
    let (i, f) = evalToMoore v
     in (Left i, either f (const offFibre))
  evalToMoore (ES (Right w)) =
    let (j, g) = evalToMoore w
     in (Right j, either (const offFibre) g)
  evalFromMoore (Left i) k = ES (Left (evalFromMoore i (k . Left)))
  evalFromMoore (Right j) k = ES (Right (evalFromMoore j (k . Right)))
  probeDir :: Dir ('Sum p q)
  probeDir = Left (probeDir @p)

instance (MooreEval p, MooreEval q) => MooreEval ('Prod p q) where
  evalToMoore (EP (u, v)) =
    let (i, f) = evalToMoore u
        (j, g) = evalToMoore v
     in ((i, j), either f g)
  evalFromMoore (i, j) k =
    EP (evalFromMoore i (k . Left), evalFromMoore j (k . Right))
  probeDir :: Dir ('Prod p q)
  probeDir = Left (probeDir @p)

instance (MooreEval p, MooreEval q) => MooreEval ('PTensor p q) where
  evalToMoore (ET pos f) = (pos, f)
  evalFromMoore = ET
  probeDir :: Dir ('PTensor p q)
  probeDir = (probeDir @p, probeDir @q)

instance (MooreEval p, MooreEval q) => MooreEval ('Comp p q) where
  evalToMoore (EC pos f) = (pos, f)
  evalFromMoore = EC
  probeDir :: Dir ('Comp p q)
  probeDir = (probeDir @p, probeDir @q)

-- | Monomial evaluation.  The position is the current-state observation, so
-- the probe direction is only needed to build the transition function and is
-- never forced when reading the position.
instance {-# OVERLAPPING #-} MooreEval (Mono i o) where
  evalToMoore (EP (EK o, EE f)) = ((o, ()), f . monoDir)
  evalFromMoore (o, ()) k = EP (EK o, EE (k . monoIn))
  probeDir :: Dir (Mono i o)
  probeDir = Right (error "probeDir Mono")

offFibre :: a
offFibre = error "off-fibre direction"

-- | Place two MachineP machines side by side: interface @p ⊗ q@, state @(s, t)@.
--
-- This is the entry point for acyclic wiring over the Dirichlet tensor —
-- boxes in parallel, pins assigned jointly.  The wired interface can be
-- mapped with 'parT' (wire-then-map).
parWiringMachineP :: MachineP (,) s (->) p -> MachineP (,) t (->) q -> MachineP (,) (s, t) (->) (PTensor p q)
parWiringMachineP sp sq =
  machineP $ \((s, t), (dp, dq)) ->
    let (s', posP) = machineMorphismP sp (s, dp)
        (t', posQ) = machineMorphismP sq (t, dq)
     in ((s', t'), (posP, posQ))

-- * Channel-pole view of MachineP machines

-- | Shared write pole for a @(->)@ MachineP machine over @(,)@: run the step and
-- post the new state into the carrier.
mooreWriteStateBody :: MachineP (,) s (->) p -> Body (,) s (->) (Dir p) s
mooreWriteStateBody sys = Body $ \(s, d) ->
  let (s', _) = machineMorphismP sys (s, d)
   in (s', s')

-- | Convert a @(->)@ 'MachineP' into companion/conjoint channel poles over @Body@.
--
-- The write pole runs the step and posts the new state into the carrier; the
-- read pole fabricates an observation by re-stepping the machine with the
-- supplied probe direction. This works only when the read can be reasonably
-- approximated by a single probe direction; for an honest MachineP observation
-- prefer 'machinePToPoles'.
machinePToPolesWithProbe :: Dir p -> MachineP (,) s (->) p -> Poles s s (Body (,) s (->)) (Body (,) s (->)) (Dir p) (Pos p)
machinePToPolesWithProbe probe sys =
  Poles
    (mooreWriteStateBody sys)
    (Body $ \(_, ch) -> machineMorphismP sys (ch, probe))

-- | Convert a pointed 'MachineP' into companion/conjoint channel poles over @Body@.
--
-- The state carrier is the machine's state @s@.  The write pole steps with the
-- supplied direction and posts the new state; the read pole observes the
-- carrier without stepping, using the supplied observation function.
machinePToPoles :: (s -> Pos p) -> MachineP (,) s (->) p -> Poles s s (Body (,) s (->)) (Body (,) s (->)) (Dir p) (Pos p)
machinePToPoles ex sys =
  Poles
    (mooreWriteStateBody sys)
    (Body $ \(s, ch) -> (s, ex ch))

-- | Comultiplication for an /observable/ MachineP machine: the output position is the
-- state. The result is a MachineP machine over the two-step interface
-- @Mono o s ◁ Mono o s@, so that feeding a pair of inputs @(o1, o2)@ runs the
-- original machine for two steps.
duplicateMachineP :: MachineP (,) s (->) (Mono o s) -> MachineP (,) s (->) ('Comp (Mono o s) (Mono o s))
duplicateMachineP sys =
  fromEvalMachineP $ \s ->
    let runMono s' = case toEvalMachineP sys s' of EP (EK o, EE f) -> (o, f)
        (s0, nextStep) = runMono s
        nextEval o =
          let (s1, step1) = runMono (nextStep o)
           in EP (EK s1, EE step1)
     in nestedToComp (EP (EK s0, EE nextEval))

-- | Build a MachineP machine whose interface is the coproduct of two monomial interfaces.
--
-- The carrier state selects the active branch at each step.  This is the
-- level-2 grammar operator on the span fragment: choice lives in the
-- polynomial interface ('Sum') rather than in the carrier-level 'if'.
branchMachineP ::
  (s -> Bool) ->
  MachineP (,) s (->) (Mono i o) ->
  MachineP (,) s (->) (Mono i o) ->
  MachineP (,) s (->) ('Sum (Mono i o) (Mono i o))
branchMachineP cond sysL sysR =
  fromEvalMachineP $ \s ->
    if cond s
      then ES (Left (toEvalMachineP sysL s))
      else ES (Right (toEvalMachineP sysR s))

-- | Run a MachineP machine with a homogeneous sum-of-monomials interface.
runMachinePSum ::
  MachineP (,) s (->) ('Sum (Mono i o) (Mono i o)) ->
  s ->
  (Either o o, i -> s)
runMachinePSum sys s = case toEvalMachineP sys s of
  ES (Left (EP (EK o, EE f))) -> (Left o, f)
  ES (Right (EP (EK o, EE f))) -> (Right o, f)

-- | A single step of a heterogeneous sum-interface MachineP machine.  The GADT encodes
-- the position-dependent input type: the left branch consumes an @i1@, the
-- right branch consumes an @i2@.
data SumStep s o1 i1 o2 i2 where
  SumStepL :: o1 -> (i1 -> s) -> SumStep s o1 i1 o2 i2
  SumStepR :: o2 -> (i2 -> s) -> SumStep s o1 i1 o2 i2

-- | Build a MachineP machine whose interface is the coproduct of two /different/
-- monomial interfaces.  The carrier state selects the active branch at each
-- step.
branchMachinePHet ::
  (s -> Bool) ->
  MachineP (,) s (->) (Mono i1 o1) ->
  MachineP (,) s (->) (Mono i2 o2) ->
  MachineP (,) s (->) ('Sum (Mono i1 o1) (Mono i2 o2))
branchMachinePHet cond sysL sysR =
  fromEvalMachineP $ \s ->
    if cond s
      then ES (Left (toEvalMachineP sysL s))
      else ES (Right (toEvalMachineP sysR s))

-- | Run a heterogeneous sum-interface MachineP machine.
runMachinePSumHet ::
  MachineP (,) s (->) ('Sum (Mono i1 o1) (Mono i2 o2)) ->
  s ->
  SumStep s o1 i1 o2 i2
runMachinePSumHet sys s = case toEvalMachineP sys s of
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

-- | Run a @Coalgebra s 'Y q@ as a 'MachineP' over @q@.
coalgebraToMoore :: (MooreEval q) => Coalgebra s 'Y q -> MachineP (,) s (->) q
coalgebraToMoore coal = fromEvalMachineP $ \s -> upd coal s (EY s)

-- | Convert a monomial 'MachineP' into a @Coalgebra s 'Y (Mono i o)@.
machinePToCoalgebraMono :: MachineP (,) s (->) (Mono i o) -> Coalgebra s 'Y (Mono i o)
machinePToCoalgebraMono sys =
  Coalgebra
    { act = \s ->
        let runMono s' = case toEvalMachineP sys s' of EP (EK o, EE _) -> o
         in Point (EP (EK (runMono s), EE (const ()))),
      upd = \s _ -> toEvalMachineP sys s
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
