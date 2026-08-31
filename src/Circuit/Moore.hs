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
-- @(s, i) -> (s, o)@. The 'mooreMachine' constructor makes this explicit:
-- it takes a transition @s -> a -> s@ and an observation @s -> b@, then
-- packages them as a 'Circuit.Body.Body'.
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
    mooreMachine,
    mooreToTMoore,

    -- * Eval / arrow conversion
    MooreEval (..),
    fromEvalMoore,
    toEvalMoore,
    step,
    peekMoore,
    stepMoore,

    -- * Monomial helpers
    monoDir,
    monoIn,

    -- * Boundary tokens
    Boundary (..),
    isMark,
    isPayload,
    markMoore,

    -- * Process conversions
    mooreAsProcess,
    asPProcess,
    pprocessAsMoore,

    -- * Tensor wiring
    parWiring,

    -- * Channel-pole view of Moore machines
    mooreToPoles,
    mooreToPolesWithProbe,
    polesToMoore,
    runPoles,

    -- * Monomial evaluation
    runMooreMono,

    -- * Lenses
    mooreAsLens,
    lensAsMoore,
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
import Circuit.Poles (HasDual (..), Poles (..))
import Circuit.Poles qualified as Poles
import Circuit.Poly
  ( Dir,
    Eval (..),
    Mono,
    Morphism (..),
    Netlist,
    Poly (..),
    Pos,
    applyLens,
    lens,
    nestedToComp,
    runMorphism,
  )
import Circuit.Process (PProcess (..), Process, asProcess, scanPProcess)
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
-- >>> import Circuit.Moore (Moore, moore, mooreMorphism, mooreMachine, MooreEval (..), toEvalMoore, fromEvalMoore, monoDir, monoIn, parWiring)

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
-- >>> let sys = mooreMachine (+) (*2) :: Moore (,) Int (->) (Mono Int Int)
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

-- | Build a monomial 'Moore' from a step and an observation.
--
-- This is the pointed-Moore view of a stateful morphism, expressed directly
-- in 'Moore' terminology.  The state transition @s -> a -> s@ and the
-- observation @s -> b@ are explicit; the seed is supplied later (for example
-- by 'mooreAsProcess').
mooreMachine :: (s -> a -> s) -> (s -> b) -> Moore (,) s (->) (Mono a b)
mooreMachine st ex =
  moore $ \case
    (_, Left v) -> absurd v
    (s, Right a) ->
      let s' = st s a
       in (s', (ex s, ()))

-- | Extract the monomial direction from its 'Either Void' encoding.
monoDir :: Dir (Mono i o) -> i
monoDir (Right i) = i
monoDir (Left v) = absurd v

-- | Inject a monomial direction into its 'Either Void' encoding.
monoIn :: i -> Dir (Mono i o)
monoIn = Right

-- * Boundary tokens

-- | The free boundary @K + payload@.
--
-- A token on the boundary is either a mark from a finite alphabet @k@ or a
-- payload value @a@.  This is the level-0 grammar of process boundaries:
-- marks are the control tokens, payloads are the data.
--
-- 'fmap' acts only on the payload side; marks are carried through unchanged.
--
-- >>> fmap length (Payload "hi")
-- Payload 2
-- >>> fmap length (Mark "halt")
-- Mark "halt"
data Boundary k a
  = -- | Control token from the finite mark alphabet.
    Mark k
  | -- | Data-carrying payload.
    Payload a
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Bifunctor Boundary where
  bimap f _ (Mark k) = Mark (f k)
  bimap _ g (Payload a) = Payload (g a)

-- | True iff the token is a 'Mark'.
isMark :: Boundary k a -> Bool
isMark (Mark _) = True
isMark (Payload _) = False

-- | True iff the token is a 'Payload'.
isPayload :: Boundary k a -> Bool
isPayload (Mark _) = False
isPayload (Payload _) = True

-- * Process conversions

-- | Convert a monomial 'Moore' into a 'PProcess' with a given seed.
asPProcess :: Moore (,) s (->) (Mono i o) -> s -> PProcess s i o
asPProcess sys s0 =
  PProcess
    s0
    (\s i -> stepMoore sys s i)
    (\s -> peekMoore sys s)
{-# INLINEABLE asPProcess #-}

-- | Convert a monomial 'Moore' into a 'Process' machine with a given initial
-- state.
mooreAsProcess :: Moore (,) s (->) (Mono i o) -> s -> Process i o
mooreAsProcess sys s0 = asProcess (asPProcess sys s0)
{-# INLINEABLE mooreAsProcess #-}

-- | Convert a 'PProcess' into a monomial 'Moore'.
pprocessAsMoore :: PProcess s i o -> Moore (,) s (->) (Mono i o)
pprocessAsMoore (PProcess _ st ex) =
  mooreMachine st ex
{-# INLINEABLE pprocessAsMoore #-}

-- | Lift a monomial 'Moore' and a state observation into a boundary machine
-- over 'Boundary' tokens.
--
-- Payloads are stepped through the inner machine.  Marks satisfying the halt
-- predicate freeze the machine and produce 'Nothing' thereafter; non-halt
-- marks leave the state unchanged and emit the current output.  The halted
-- state remembers the final inner state.
--
-- The returned machine carries state @Either s s@: 'Left' is running, 'Right'
-- is halted.  This is the core combinator behind mark-driven halt: the finite
-- mark alphabet @k@ carries control tokens, while payloads carry data.
markMoore ::
  (k -> Bool) ->
  (s -> b) ->
  Moore (,) s (->) (Mono a b) ->
  Moore (,) (Either s s) (->) (Mono (Boundary k a) (Maybe b))
markMoore isHalt ex sys =
  mooreMachine
    ( \s tok -> case (s, tok) of
        (Left s', Payload a) -> Left (fst (mooreMorphism sys (s', Right a)))
        (Left s', Mark k) -> if isHalt k then Right s' else Left s'
        (Right s', _) -> Right s'
    )
    ( \case
        Left s -> Just (ex s)
        Right _ -> Nothing
    )
{-# INLINEABLE markMoore #-}

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

-- | Peek at the current output of a monomial Moore machine.
--
-- >>> let sys = mooreMachine (\s i -> s + i) (\s -> s * 2) :: Moore (,) Int (->) (Mono Int Int)
-- >>> peekMoore sys 5
-- 10
peekMoore :: Moore (,) s (->) (Mono i o) -> s -> o
peekMoore sys s = fst (runMooreMono sys s)

-- | Advance a monomial Moore machine by one input, returning the next state.
--
-- >>> let sys = mooreMachine (\s i -> s + i) (\s -> s * 2) :: Moore (,) Int (->) (Mono Int Int)
-- >>> stepMoore sys 5 3
-- 8
stepMoore :: Moore (,) s (->) (Mono i o) -> s -> i -> s
stepMoore sys s i = snd (runMooreMono sys s) i

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

-- | Convert a pole-split body into a monomial @(->)@ 'Moore' machine.
--
-- The write pole supplies the state transition and the read pole supplies the
-- observation.  The result is a pointed Moore machine whose seed is supplied
-- separately (for example by 'runPoles').
polesToMoore :: Poles (Body (,) s (->)) a b -> Moore (,) s (->) (Mono a b)
polesToMoore p =
  let (Body write, Body receive) = Poles.splay0 p
   in mooreMachine (\s a -> fst (write (s, a))) (\s -> snd (receive (s, ())))

-- | Run a pair of channel poles over a list of inputs.
--
-- The poles are converted to a 'PProcess' and scanned; the final state is
-- discarded.
runPoles :: Poles (Body (,) s (->)) a b -> s -> [a] -> [b]
runPoles p s0 xs = scanPProcess (asPProcess (polesToMoore p) s0) xs

-- | Shared write pole for a @(->)@ Moore machine over @(,)@: run the step and discard
-- the output position.
mooreWriteBody :: Moore (,) s (->) p -> Body (,) s (->) (Dir p) ()
mooreWriteBody sys = Body $ \(s, d) -> (fst (mooreMorphism sys (s, d)), ())

-- | Convert a @(->)@ 'Moore' into companion/conjoint channel poles over @Body@.
--
-- The write pole runs the step and discards the output position; the read pole
-- fabricates an observation by re-stepping the machine with the supplied probe
-- direction. This works only when the read can be reasonably approximated by a
-- single probe direction; for an honest Moore observation prefer
-- 'mooreToPoles'.
mooreToPolesWithProbe :: Dir p -> Moore (,) s (->) p -> Poles (Body (,) s (->)) (Dir p) (Pos p)
mooreToPolesWithProbe probe sys =
  Poles.poles0
    (mooreWriteBody sys)
    (Body $ \(s, ()) -> mooreMorphism sys (s, probe))

-- | Convert a pointed 'Moore' into companion/conjoint channel poles over @Body@.
--
-- The state carrier is the machine's state @s@.  The write pole steps with the
-- supplied direction; the read pole observes the current state without stepping,
-- using the supplied observation function.
mooreToPoles :: (s -> Pos p) -> Moore (,) s (->) p -> Poles (Body (,) s (->)) (Dir p) (Pos p)
mooreToPoles ex sys =
  Poles.poles0
    (mooreWriteBody sys)
    (Body $ \(s, ()) -> (s, ex s))

-- | Run a monomial @(->)@ Moore machine at a state, exposing the output position and
-- the state-transition function.
runMooreMono :: Moore (,) s (->) (Mono i o) -> s -> (o, i -> s)
runMooreMono sys s = case toEvalMoore sys s of EP (EK o, EE f) -> (o, f)

-- | The coalgebra-as-lens isomorphism.
--
-- A monomial Moore machine @Moore (,) s (->) (Mono i o)@ is exactly a lens
-- @S y^S -> Mono i o@: the current state @s@ determines the output position
-- @o@, and each input direction @i@ determines the next state @s@.
--
-- This is the bridge to Spivak's presentation:
-- @Moore (,) s (->) p ≅ Poly(S y^S, p)@.
mooreAsLens :: Moore (,) s (->) (Mono i o) -> Morphism (Mono s s) (Mono i o)
mooreAsLens sys = lens get put
  where
    get s = fst (runMooreMono sys s)
    put s = snd (runMooreMono sys s)

-- | Inverse of 'mooreAsLens': build a Moore machine from a lens @S y^S -> Mono i o@.
lensAsMoore :: Morphism (Mono s s) (Mono i o) -> Moore (,) s (->) (Mono i o)
lensAsMoore m = fromEvalMoore $ \s ->
  case applyLens m s of
    (o, put) -> EP (EK o, EE put)

-- | Comultiplication for an /observable/ Moore machine: the output position is the
-- state. The result is a Moore machine over the two-step interface
-- @Mono o s ◁ Mono o s@, so that feeding a pair of inputs @(o1, o2)@ runs the
-- original machine for two steps.
duplicateMoore :: Moore (,) s (->) (Mono o s) -> Moore (,) s (->) ('Comp (Mono o s) (Mono o s))
duplicateMoore sys =
  fromEvalMoore $ \s ->
    let (s0, nextStep) = runMooreMono sys s
        nextEval o =
          let (s1, step1) = runMooreMono sys (nextStep o)
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
    { act = \s -> let (o, _) = runMooreMono sys s in Point (EP (EK o, EE (const ()))),
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
