{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | A Moore machine fibered over a polynomial interface @p@.
--
-- @
--   newtype Moore t arr s p = Moore (Body t s arr (Dir p) (Pos p))
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
-- so @Moore (,) (->) s (Mono i o)@ collapses to the ordinary Moore body
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
    moore,
    mooreMorphism,
    mooreMachine,

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
    SomePoles (..),
    runSomePoles,
    mooreToPolesWithProbe,
    mooreWithSeedToPoles,

    -- * Running monomial Moore machines
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
import Circuit.Category ((.>))
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
import Control.Category (id, (.))
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
-- @Moore t (Op (->)) s p@ is a first-class codata body.  Together with the
-- forward @(->)@ case this reproduces the @Fam(Set^op)@ rung of polynomial
-- equipment.
--
-- >>> let sys = mooreMachine (+) (*2) :: Moore (,) (->) Int (Mono Int Int)
-- >>> mooreMorphism sys (3, Right 5)
-- (8,(16,()))
newtype Moore (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) s (p :: Poly)
  = Moore (Body t s arr (Dir p) (Pos p))

-- | Construct a cartesian 'Moore' from its underlying arrow.
moore :: arr (s, Dir p) (s, Pos p) -> Moore (,) arr s p
moore = Moore . Body

-- | Inspect a cartesian 'Moore' as its underlying arrow.
mooreMorphism :: Moore (,) arr s p -> arr (s, Dir p) (s, Pos p)
mooreMorphism (Moore (Body f)) = f

-- | Build a monomial 'Moore' from a step and an observation.
--
-- This is the pointed-Moore view of a stateful morphism, expressed directly
-- in 'Moore' terminology.  The state transition @s -> a -> s@ and the
-- observation @s -> b@ are explicit; the seed is supplied later (for example
-- by 'Circuit.Process.mooreToProcess').
mooreMachine :: (s -> a -> s) -> (s -> b) -> Moore (,) (->) s (Mono a b)
mooreMachine st ex =
  moore $ \case
    (_, Left v) -> absurd v
    (s, Right a) ->
      let s' = st s a
       in (s', (ex s', ()))

-- | Extract the monomial direction from its 'Either Void' encoding.
monoDir :: Dir (Mono i o) -> i
monoDir (Right i) = i
monoDir (Left v) = absurd v

-- | Inject a monomial direction into its 'Either Void' encoding.
monoIn :: i -> Dir (Mono i o)
monoIn = Right

-- | Convert an eval-form @(->)@ Moore machine into the arrow form.
fromEvalMoore :: (MooreEval p) => (s -> Eval p s) -> Moore (,) (->) s p
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
toEvalMoore :: forall p s. (MooreEval p) => Moore (,) (->) s p -> s -> Eval p s
toEvalMoore sys s = evalFromMoore pos (\d -> fst (mooreMorphism sys (s, d)))
  where
    pos = snd (mooreMorphism sys (s, probeDir @p))

-- | Run one step: observe the current @p@-output from state @s@.
step :: (MooreEval p) => Moore (,) (->) s p -> s -> Eval p s
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

instance (MooreEval p, MooreEval q) => MooreEval ('Tensor p q) where
  evalToMoore (ET pos f) = (pos, f)
  evalFromMoore = ET
  probeDir :: Dir ('Tensor p q)
  probeDir = (probeDir @p, probeDir @q)

instance (MooreEval p, MooreEval q) => MooreEval ('Comp p q) where
  evalToMoore (EC pos f) = (pos, f)
  evalFromMoore = EC
  probeDir :: Dir ('Comp p q)
  probeDir = (probeDir @p, probeDir @q)

offFibre :: a
offFibre = error "off-fibre direction"

-- | Place two Moore machines side by side: interface @p ⊗ q@, state @(s, t)@.
--
-- This is the entry point for acyclic wiring over the Dirichlet tensor —
-- boxes in parallel, pins assigned jointly.  The wired interface can be
-- mapped with 'parT' (wire-then-map).
parWiring :: Moore (,) (->) s p -> Moore (,) (->) t q -> Moore (,) (->) (s, t) (Tensor p q)
parWiring sp sq =
  moore $ \((s, t), (dp, dq)) ->
    let (s', posP) = mooreMorphism sp (s, dp)
        (t', posQ) = mooreMorphism sq (t, dq)
     in ((s', t'), (posP, posQ))

-- * Channel-pole view of Moore machines

-- | An existentially-quantified pair of channel poles over a body, carrying
-- its seed. The shape mirrors 'Circuit.Body.SomeBody'.
data SomePoles t arr a b where
  SomePoles :: s -> Poles (Body t s arr) a b -> SomePoles t arr a b

-- | Run an existentially-packed pair of poles over a list of inputs.
--
-- This is the @(,)@ / @(->)@ specialisation; 'SomePoles' is parametric in the
-- tensor and arrow so that other shapes can reuse the existential packaging.
runSomePoles :: SomePoles (,) (->) a b -> [a] -> [b]
runSomePoles (SomePoles s0 p) xs =
  let (write, receive) = Poles.splay0 p
      Body f = write .> receive
      (_, bs) = foldl (\(s, acc) a -> let (s', b) = f (s, a) in (s', b : acc)) (s0, []) xs
   in reverse bs

-- | Shared write pole for a @(->)@ Moore machine over @(,)@: run the step and discard
-- the output position.
mooreWriteBody :: Moore (,) (->) s p -> Body (,) s (->) (Dir p) ()
mooreWriteBody sys = Body $ \(s, d) -> (fst (mooreMorphism sys (s, d)), ())

-- | Convert a @(->)@ 'Moore' into companion/conjoint channel poles over @Body@.
--
-- The write pole runs the step and discards the output position; the read pole
-- fabricates an observation by re-stepping the machine with the supplied probe
-- direction. This works only when the read can be reasonably approximated by a
-- single probe direction; for an honest Moore observation prefer
-- 'mooreWithSeedToPoles'.
mooreToPolesWithProbe :: Dir p -> Moore (,) (->) s p -> Poles (Body (,) s (->)) (Dir p) (Pos p)
mooreToPolesWithProbe probe sys =
  Poles.poles0
    (mooreWriteBody sys)
    (Body $ \(s, ()) -> mooreMorphism sys (s, probe))

-- | Convert a pointed 'Moore' into companion/conjoint channel poles over @Body@.
--
-- The state carrier is the machine's state @s@ and the seed @s0@ is carried by
-- 'SomePoles'.  The write pole steps with the supplied direction; the read pole
-- observes the current state without stepping, using the supplied observation
-- function.
mooreWithSeedToPoles :: s -> (s -> Pos p) -> Moore (,) (->) s p -> SomePoles (,) (->) (Dir p) (Pos p)
mooreWithSeedToPoles s0 ex sys =
  SomePoles s0 $
    Poles.poles0
      (mooreWriteBody sys)
      (Body $ \(s, ()) -> (s, ex s))

-- | Run a monomial @(->)@ Moore machine at a state, exposing the output position and
-- the state-transition function.
runMooreMono :: Moore (,) (->) s (Mono i o) -> s -> (o, i -> s)
runMooreMono sys s = case toEvalMoore sys s of EP (EK o, EE f) -> (o, f)

-- | The coalgebra-as-lens isomorphism.
--
-- A monomial Moore machine @Moore (,) (->) s (Mono i o)@ is exactly a lens
-- @S y^S -> Mono i o@: the current state @s@ determines the output position
-- @o@, and each input direction @i@ determines the next state @s@.
--
-- This is the bridge to Spivak's presentation:
-- @Moore (,) (->) s p ≅ Poly(S y^S, p)@.
mooreAsLens :: Moore (,) (->) s (Mono i o) -> Morphism (Mono s s) (Mono i o)
mooreAsLens sys = lens get put
  where
    get s = fst (runMooreMono sys s)
    put s = snd (runMooreMono sys s)

-- | Inverse of 'mooreAsLens': build a Moore machine from a lens @S y^S -> Mono i o@.
lensAsMoore :: Morphism (Mono s s) (Mono i o) -> Moore (,) (->) s (Mono i o)
lensAsMoore m = fromEvalMoore $ \s ->
  case applyLens m s of
    (o, put) -> EP (EK o, EE put)

-- | Comultiplication for an /observable/ Moore machine: the output position is the
-- state. The result is a Moore machine over the two-step interface
-- @Mono o s ◁ Mono o s@, so that feeding a pair of inputs @(o1, o2)@ runs the
-- original machine for two steps.
duplicateMoore :: Moore (,) (->) s (Mono o s) -> Moore (,) (->) s ('Comp (Mono o s) (Mono o s))
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
  Moore (,) (->) s (Mono i o) ->
  Moore (,) (->) s (Mono i o) ->
  Moore (,) (->) s ('Sum (Mono i o) (Mono i o))
branchMoore cond sysL sysR =
  fromEvalMoore $ \s ->
    if cond s
      then ES (Left (toEvalMoore sysL s))
      else ES (Right (toEvalMoore sysR s))

-- | Run a Moore machine with a homogeneous sum-of-monomials interface.
runMooreSum ::
  Moore (,) (->) s ('Sum (Mono i o) (Mono i o)) ->
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
  Moore (,) (->) s (Mono i1 o1) ->
  Moore (,) (->) s (Mono i2 o2) ->
  Moore (,) (->) s ('Sum (Mono i1 o1) (Mono i2 o2))
branchMooreHet cond sysL sysR =
  fromEvalMoore $ \s ->
    if cond s
      then ES (Left (toEvalMoore sysL s))
      else ES (Right (toEvalMoore sysR s))

-- | Run a heterogeneous sum-interface Moore machine.
runMooreSumHet ::
  Moore (,) (->) s ('Sum (Mono i1 o1) (Mono i2 o2)) ->
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
coalgebraToMoore :: (MooreEval q) => Coalgebra s 'Y q -> Moore (,) (->) s q
coalgebraToMoore coal = fromEvalMoore $ \s -> upd coal s (EY s)

-- | Convert a monomial 'Moore' into a @Coalgebra s 'Y (Mono i o)@.
mooreToCoalgebraMono :: Moore (,) (->) s (Mono i o) -> Coalgebra s 'Y (Mono i o)
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
