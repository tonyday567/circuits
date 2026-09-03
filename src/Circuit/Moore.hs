{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | A Moore machine fibered over a polynomial interface @p@.
--
-- @
--   newtype Moore t s arr p = Moore (Body t s arr (Dir p) (Pos p))
-- @
--
-- * The base is the state @s@.
-- * The fiber/interface is the polynomial @p@, with positions 'Pos' p and
--   directions 'Dir' p.
-- * The span shape is @s <- (s, Dir p) -> Pos p@.
-- * "Moore" because the observable output 'Pos' p depends on the state @s@,
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
-- so @Moore (,) s (->) (Mono i o)@ collapses to the ordinary Moore body
-- @(s, i) -> (s, o)@. The 'moore' constructor together with 'monoIn' /
-- 'monoDir' makes this explicit.
--
-- For a general polynomial @p@, 'Pos' p and 'Dir' p can be branching: the
-- polynomial layer handles sums and products of interfaces, so 'Moore' is a
-- Moore machine that can branch, offer choices, or run parallel interfaces,
-- all while 'Circuit.Body.Body' handles the state transition.
--
-- In the BLLL picture (Katis–Sabadini–Walters), an F-Moore machine is an
-- F-algebra @F E -> E@ plus an output @E -> O@. 'Moore' fits this with
-- state object @E = s@, endofunctor @F = (-) ⊗ Dir p@, transition
-- @d : s ⊗ Dir p -> s@, and output @obs : s -> Pos p@ bundled with the
-- transition in the 'Circuit.Body.Body'.
--
-- 'Circuit.Process.Process' is the pointed monomial special case: where
-- @Process@ is the existential form @∃s. (s, s -> a -> s, s -> b)@, 'Moore'
-- is the polynomial-lens form of the same idea, with @p@ describing the
-- interactive interface.
--
-- This module defines the 'Moore' type, conversions between eval and arrow
-- forms, wiring combinators, and higher-level execution combinators.
module Circuit.Moore
  ( -- * Moore machines
    Moore (..),
    TMoore (..),
    moore,
    mooreMorphism,
    mooreToTMoore,

    -- * Eval / arrow conversion
    MooreEval (..),
    fromEvalMoore,
    toEvalMoore,
    step,

    -- * Monomial helpers
    monoDir,
    monoIn,

    -- * Tensor wiring
    parWiring,

    -- * Channel-pole view of Moore machines
    mooreToPoles,
    mooreToPolesWithProbe,

    -- * Comultiplication / duplication
    duplicateMoore,

    -- * Branches
    branchMoore,
    runMooreSum,
    branchMooreHet,
    runMooreSumHet,
    SumStep (..),

    -- * Coalgebras
    Coalgebra (..),
    coalgebraToMoore,
    composeCoalgebra,
    mooreToCoalgebraMono,
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
-- >>> import Circuit.Moore (Moore, moore, mooreMorphism, MooreEval (..), toEvalMoore, fromEvalMoore, monoDir, monoIn, parWiring)
-- >>> import Data.Void (absurd)

-- | A Moore machine with interface @p@, carrier @s@, over base arrow @arr@,
-- parameterised by the state-pairing tensor @t@.
--
-- Uncurried netlist form: the state and the current input direction are fed
-- together under @t@, and the result is the next state together with the current
-- output position.  For the monomial @Mono i o@ and @t = (,)@ this is exactly
-- the Moore body @arr (s, i) (s, o)@ after collapsing the unit positions.
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
-- @Moore t s (Op (->)) p@ is a first-class codata body.  Together with the
-- forward @(->)@ case this reproduces the @Fam(Set^op)@ rung of polynomial
-- equipment.
--
-- >>> let sys = moore (\case (_, Left v) -> absurd v; (s, Right i) -> (s + i, (s * 2, ()))) :: Moore (,) Int (->) (Mono Int Int)
-- >>> mooreMorphism sys (3, Right 5)
-- (8,(6,()))
newtype Moore (t :: Type -> Type -> Type) s (arr :: Type -> Type -> Type) (p :: Poly)
  = Moore (Body t s arr (Dir p) (Pos p))

-- | A Moore machine with hidden carrier, represented as a trace over the
-- polynomial interface.
--
-- This is the unpointed counterpart of 'Moore': the state carrier is not a
-- type parameter; instead it is folded into the feedback wire of the trace.
-- 'mooreToTMoore' embeds a pointed 'Moore' into this form by closing the state
-- channel with 'yank'.
newtype TMoore (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) (p :: Poly)
  = TMoore (Trace t arr (Dir p) (Pos p))

-- | Convert a pointed 'Moore' into a hidden-state 'TMoore' by closing the state
-- feedback wire.
mooreToTMoore ::
  (Circuit.Traced.Yank t arr) =>
  Moore t s arr p ->
  TMoore t arr p
mooreToTMoore (Moore (Body f)) = TMoore (yank (base f))

-- | Construct a cartesian 'Moore' from its underlying arrow.
moore :: arr (s, Dir p) (s, Pos p) -> Moore (,) s arr p
moore = Moore . Body

-- | Inspect a cartesian 'Moore' as its underlying arrow.
mooreMorphism :: Moore (,) s arr p -> arr (s, Dir p) (s, Pos p)
mooreMorphism (Moore (Body f)) = f

-- | Extract the monomial direction from its 'Either Void' encoding.
monoDir :: Dir (Mono i o) -> i
monoDir (Right i) = i
monoDir (Left v) = absurd v

-- | Inject a monomial direction into its 'Either Void' encoding.
monoIn :: i -> Dir (Mono i o)
monoIn = Right

-- | Convert an eval-form @(->)@ Moore machine into the arrow form.
fromEvalMoore :: (MooreEval p) => (s -> Eval p s) -> Moore (,) s (->) p
fromEvalMoore f = moore $ \(s, d) ->
  let (pos, next) = evalToMoore (f s)
   in (next d, pos)

-- | Convert an arrow-form @(->)@ Moore machine back into eval form.
--
-- This is a Moore observation: the position is read from the state alone, with
-- the direction supplied only to compute the next state.  Correctness therefore
-- requires that the machine be Moore at the call site — the position must not
-- depend on the direction.  Internally the direction is 'probeDir', which is
-- lazily unused for the polynomial shapes where it is defined; any strict
-- forcing of the direction (a bang pattern, 'seq', or a strict tuple in a
-- user-written body) will turn 'toEvalMoore' into a runtime error rather than
-- a wrong answer.
toEvalMoore :: forall p s. (MooreEval p) => Moore (,) s (->) p -> s -> Eval p s
toEvalMoore sys s = evalFromMoore pos (\d -> fst (mooreMorphism sys (s, d)))
  where
    pos = snd (mooreMorphism sys (s, probeDir @p))

-- | Run one step: observe the current @p@-output from state @s@.
step :: (MooreEval p) => Moore (,) s (->) p -> s -> Eval p s
step = toEvalMoore

-- | Helpers for translating between the 'Eval' presentation and the arrow
-- presentation of a @(->)@ Moore machine.  These extend the netlist view to 'Sum'.
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

-- | Place two Moore machines side by side: interface @p ⊗ q@, state @(s, t)@.
--
-- This is the entry point for acyclic wiring over the Dirichlet tensor —
-- boxes in parallel, pins assigned jointly.  The wired interface can be
-- mapped with 'parT' (wire-then-map).
parWiring :: Moore (,) s (->) p -> Moore (,) t (->) q -> Moore (,) (s, t) (->) (PTensor p q)
parWiring sp sq =
  moore $ \((s, t), (dp, dq)) ->
    let (s', posP) = mooreMorphism sp (s, dp)
        (t', posQ) = mooreMorphism sq (t, dq)
     in ((s', t'), (posP, posQ))

-- * Channel-pole view of Moore machines

-- | Shared write pole for a @(->)@ Moore machine over @(,)@: run the step and
-- post the new state into the carrier.
mooreWriteStateBody :: Moore (,) s (->) p -> Body (,) s (->) (Dir p) s
mooreWriteStateBody sys = Body $ \(s, d) ->
  let (s', _) = mooreMorphism sys (s, d)
   in (s', s')

-- | Convert a @(->)@ 'Moore' into companion/conjoint channel poles over @Body@.
--
-- The write pole runs the step and posts the new state into the carrier; the
-- read pole fabricates an observation by re-stepping the machine with the
-- supplied probe direction. This works only when the read can be reasonably
-- approximated by a single probe direction; for an honest Moore observation
-- prefer 'mooreToPoles'.
mooreToPolesWithProbe :: Dir p -> Moore (,) s (->) p -> Poles s s (Body (,) s (->)) (Dir p) (Pos p)
mooreToPolesWithProbe probe sys =
  Poles
    (mooreWriteStateBody sys)
    (Body $ \(_, ch) -> mooreMorphism sys (ch, probe))

-- | Convert a pointed 'Moore' into companion/conjoint channel poles over @Body@.
--
-- The state carrier is the machine's state @s@.  The write pole steps with the
-- supplied direction and posts the new state; the read pole observes the
-- carrier without stepping, using the supplied observation function.
mooreToPoles :: (s -> Pos p) -> Moore (,) s (->) p -> Poles s s (Body (,) s (->)) (Dir p) (Pos p)
mooreToPoles ex sys =
  Poles
    (mooreWriteStateBody sys)
    (Body $ \(s, ch) -> (s, ex ch))

-- | Comultiplication for an /observable/ Moore machine: the output position is the
-- state. The result is a Moore machine over the two-step interface
-- @Mono o s ◁ Mono o s@, so that feeding a pair of inputs @(o1, o2)@ runs the
-- original machine for two steps.
duplicateMoore :: Moore (,) s (->) (Mono o s) -> Moore (,) s (->) ('Comp (Mono o s) (Mono o s))
duplicateMoore sys =
  fromEvalMoore $ \s ->
    let runMono s' = case toEvalMoore sys s' of EP (EK o, EE f) -> (o, f)
        (s0, nextStep) = runMono s
        nextEval o =
          let (s1, step1) = runMono (nextStep o)
           in EP (EK s1, EE step1)
     in nestedToComp (EP (EK s0, EE nextEval))

-- | Build a Moore machine whose interface is the coproduct of two monomial interfaces.
--
-- The carrier state selects the active branch at each step.  This is the
-- level-2 grammar operator on the span fragment: choice lives in the
-- polynomial interface ('Sum') rather than in the carrier-level 'if'.
branchMoore ::
  (s -> Bool) ->
  Moore (,) s (->) (Mono i o) ->
  Moore (,) s (->) (Mono i o) ->
  Moore (,) s (->) ('Sum (Mono i o) (Mono i o))
branchMoore cond sysL sysR =
  fromEvalMoore $ \s ->
    if cond s
      then ES (Left (toEvalMoore sysL s))
      else ES (Right (toEvalMoore sysR s))

-- | Run a Moore machine with a homogeneous sum-of-monomials interface.
runMooreSum ::
  Moore (,) s (->) ('Sum (Mono i o) (Mono i o)) ->
  s ->
  (Either o o, i -> s)
runMooreSum sys s = case toEvalMoore sys s of
  ES (Left (EP (EK o, EE f))) -> (Left o, f)
  ES (Right (EP (EK o, EE f))) -> (Right o, f)

-- | A single step of a heterogeneous sum-interface Moore machine.  The GADT encodes
-- the position-dependent input type: the left branch consumes an @i1@, the
-- right branch consumes an @i2@.
data SumStep s o1 i1 o2 i2 where
  SumStepL :: o1 -> (i1 -> s) -> SumStep s o1 i1 o2 i2
  SumStepR :: o2 -> (i2 -> s) -> SumStep s o1 i1 o2 i2

-- | Build a Moore machine whose interface is the coproduct of two /different/
-- monomial interfaces.  The carrier state selects the active branch at each
-- step.
branchMooreHet ::
  (s -> Bool) ->
  Moore (,) s (->) (Mono i1 o1) ->
  Moore (,) s (->) (Mono i2 o2) ->
  Moore (,) s (->) ('Sum (Mono i1 o1) (Mono i2 o2))
branchMooreHet cond sysL sysR =
  fromEvalMoore $ \s ->
    if cond s
      then ES (Left (toEvalMoore sysL s))
      else ES (Right (toEvalMoore sysR s))

-- | Run a heterogeneous sum-interface Moore machine.
runMooreSumHet ::
  Moore (,) s (->) ('Sum (Mono i1 o1) (Mono i2 o2)) ->
  s ->
  SumStep s o1 i1 o2 i2
runMooreSumHet sys s = case toEvalMoore sys s of
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

-- | Run a @Coalgebra s 'Y q@ as a 'Moore' over @q@.
coalgebraToMoore :: (MooreEval q) => Coalgebra s 'Y q -> Moore (,) s (->) q
coalgebraToMoore coal = fromEvalMoore $ \s -> upd coal s (EY s)

-- | Convert a monomial 'Moore' into a @Coalgebra s 'Y (Mono i o)@.
mooreToCoalgebraMono :: Moore (,) s (->) (Mono i o) -> Coalgebra s 'Y (Mono i o)
mooreToCoalgebraMono sys =
  Coalgebra
    { act = \s ->
        let runMono s' = case toEvalMoore sys s' of EP (EK o, EE _) -> o
         in Point (EP (EK (runMono s), EE (const ()))),
      upd = \s _ -> toEvalMoore sys s
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
