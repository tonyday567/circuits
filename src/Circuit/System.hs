{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | A Moore machine fibered over a polynomial interface @p@.
--
-- @
--   newtype SystemT t arr s p = SystemT (Body t s arr (Dir p) (Pos p))
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
-- so @System (->) s (Mono i o)@ collapses to the ordinary Moore body
-- @(s, i) -> (s, o)@. The 'mooreSystem' constructor makes this explicit:
-- it takes a transition @s -> a -> s@ and an observation @s -> b@, then
-- packages them as a 'Circuit.Body.Body'.
--
-- For a general polynomial @p@, 'Pos' p and 'Dir' p can be branching: the
-- polynomial layer handles sums and products of interfaces, so 'System' is a
-- Moore machine that can branch, offer choices, or run parallel interfaces,
-- all while 'Circuit.Body.Body' handles the state transition.
--
-- In the BLLL picture (Katis–Sabadini–Walters), an F-Moore machine is an
-- F-algebra @F E -> E@ plus an output @E -> O@. 'System' fits this with
-- state object @E = s@, endofunctor @F = (-) ⊗ Dir p@, transition
-- @d : s ⊗ Dir p -> s@, and output @obs : s -> Pos p@ bundled with the
-- transition in the 'Circuit.Body.Body'.
--
-- 'Circuit.Process.Process' is the pointed monomial special case: where
-- @Process@ is the existential form @∃s. (s, s -> a -> s, s -> b)@, 'System'
-- is the polynomial-lens form of the same idea, with @p@ describing the
-- interactive interface.
--
-- This module defines the system type, conversions between eval and arrow
-- forms, wiring combinators, and higher-level execution combinators.
module Circuit.System
  ( -- * Systems
    SystemT (..),
    System,
    system,
    runSystem,
    mooreSystem,

    -- * Eval / arrow conversion
    SystemEval (..),
    fromEvalSystem,
    toEvalSystem,
    step,

    -- * Monomial helpers
    monoDir,
    monoIn,

    -- * Tensor wiring
    parWiring,

    -- * Channel-pole view of systems
    SomePoles (..),
    runSomePoles,
    systemToPolesWithProbe,
    systemWithSeedToPoles,

    -- * Running monomial systems
    runSystemMono,

    -- * Lenses
    systemAsLens,
    lensAsSystem,
    duplicateSystem,

    -- * Branches
    branchSystem,
    runSystemSum,
    branchSystemHet,
    runSystemSumHet,
    SumStep (..),

    -- * Coalgebras
    Coalgebra (..),
    Step,
    coalgebraToSystem,
    composeCoalgebra,
    systemToCoalgebraMono,
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
-- >>> import Circuit.Poly (Eval (..), Mono, Morphism, lens, applyLens)
-- >>> import Circuit.System (System, system, runSystem, mooreSystem, SystemEval (..), toEvalSystem, fromEvalSystem, monoDir, monoIn, parWiring)

-- | A dynamical system with interface @p@, carrier @s@, over base arrow @arr@,
-- parameterised by the state-pairing tensor @t@.
--
-- Uncurried netlist form: the state and the current input direction are fed
-- together under @t@, and the result is the next state together with the current
-- output position.  For the monomial @Mono i o@ and @t = (,)@ this is exactly
-- the Moore body @arr (s, i) (s, o)@ after collapsing the unit positions.
--
-- The cartesian specialisation @SystemT (,)@ is kept as the type synonym
-- 'System'; use 'system' and 'runSystem' to construct and inspect it.
newtype SystemT (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) s (p :: Poly)
  = SystemT (Body t s arr (Dir p) (Pos p))

-- | Cartesian systems: the state-pairing tensor is @(,)@.
type System = SystemT (,)

-- | Construct a cartesian 'System' from its underlying arrow.
system :: arr (s, Dir p) (s, Pos p) -> System arr s p
system = SystemT . Body

-- | Inspect a cartesian 'System' as its underlying arrow.
runSystem :: System arr s p -> arr (s, Dir p) (s, Pos p)
runSystem (SystemT (Body f)) = f

-- | Build a monomial 'System' from a step and an observation.
--
-- This is the pointed-Moore view of a stateful morphism, expressed directly
-- in 'System' terminology.  The state transition @s -> a -> s@ and the
-- observation @s -> b@ are explicit; the seed is supplied later (for example
-- by 'Circuit.Process.systemToProcess').
mooreSystem :: (s -> a -> s) -> (s -> b) -> System (->) s (Mono a b)
mooreSystem st ex =
  system $ \case
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

-- | Convert an eval-form @(->)@ system into the arrow form.
fromEvalSystem :: (SystemEval p) => (s -> Eval p s) -> System (->) s p
fromEvalSystem f = system $ \(s, d) ->
  let (pos, next) = evalToSystem (f s)
   in (next d, pos)

-- | Convert an arrow-form @(->)@ system back into eval form.
toEvalSystem :: forall p s. (SystemEval p) => System (->) s p -> s -> Eval p s
toEvalSystem sys s = evalFromSystem pos (\d -> fst (runSystem sys (s, d)))
  where
    pos = snd (runSystem sys (s, probeDir @p))

-- | Run one step: observe the current @p@-output from state @s@.
step :: (SystemEval p) => System (->) s p -> s -> Eval p s
step = toEvalSystem

-- | Helpers for translating between the 'Eval' presentation and the arrow
-- presentation of a @(->)@ system.  These extend the netlist view to 'Sum'.
class SystemEval (p :: Poly) where
  evalToSystem :: Eval p x -> (Pos p, Dir p -> x)
  evalFromSystem :: Pos p -> (Dir p -> x) -> Eval p x
  probeDir :: Dir p

instance SystemEval 'Y where
  evalToSystem (EY x) = ((), \() -> x)
  evalFromSystem () k = EY (k ())
  probeDir = ()

instance SystemEval ('Const a) where
  evalToSystem (EK c) = (c, absurd)
  evalFromSystem c _ = EK c
  probeDir = error "probeDir Const"

instance SystemEval ('Exp a) where
  evalToSystem (EE f) = ((), f)
  evalFromSystem () = EE
  probeDir = error "probeDir Exp"

instance (SystemEval p, SystemEval q) => SystemEval ('Sum p q) where
  evalToSystem (ES (Left v)) =
    let (i, f) = evalToSystem v
     in (Left i, either f (const offFibre))
  evalToSystem (ES (Right w)) =
    let (j, g) = evalToSystem w
     in (Right j, either (const offFibre) g)
  evalFromSystem (Left i) k = ES (Left (evalFromSystem i (k . Left)))
  evalFromSystem (Right j) k = ES (Right (evalFromSystem j (k . Right)))
  probeDir :: Dir ('Sum p q)
  probeDir = Left (probeDir @p)

instance (SystemEval p, SystemEval q) => SystemEval ('Prod p q) where
  evalToSystem (EP (u, v)) =
    let (i, f) = evalToSystem u
        (j, g) = evalToSystem v
     in ((i, j), either f g)
  evalFromSystem (i, j) k =
    EP (evalFromSystem i (k . Left), evalFromSystem j (k . Right))
  probeDir :: Dir ('Prod p q)
  probeDir = Left (probeDir @p)

instance (SystemEval p, SystemEval q) => SystemEval ('Tensor p q) where
  evalToSystem (ET pos f) = (pos, f)
  evalFromSystem = ET
  probeDir :: Dir ('Tensor p q)
  probeDir = (probeDir @p, probeDir @q)

instance (SystemEval p, SystemEval q) => SystemEval ('Comp p q) where
  evalToSystem (EC pos f) = (pos, f)
  evalFromSystem = EC
  probeDir :: Dir ('Comp p q)
  probeDir = (probeDir @p, probeDir @q)

offFibre :: a
offFibre = error "off-fibre direction"

-- | Place two Moore systems side by side: interface @p ⊗ q@, state @(s, t)@.
--
-- This is the entry point for acyclic wiring over the Dirichlet tensor —
-- boxes in parallel, pins assigned jointly.  The wired interface can be
-- mapped with 'parT' (wire-then-map).
parWiring :: System (->) s p -> System (->) t q -> System (->) (s, t) (Tensor p q)
parWiring sp sq =
  system $ \((s, t), (dp, dq)) ->
    let (s', posP) = runSystem sp (s, dp)
        (t', posQ) = runSystem sq (t, dq)
     in ((s', t'), (posP, posQ))

-- * Channel-pole view of systems

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

-- | Shared write pole for a @(->)@ system over @(,)@: run the step and discard
-- the output position.
systemWriteBody :: System (->) s p -> Body (,) s (->) (Dir p) ()
systemWriteBody sys = Body $ \(s, d) -> (fst (runSystem sys (s, d)), ())

-- | Convert a @(->)@ 'System' into companion/conjoint channel poles over @Body@.
--
-- The write pole runs the step and discards the output position; the read pole
-- fabricates an observation by re-stepping the system with the supplied probe
-- direction. This works only when the read can be reasonably approximated by a
-- single probe direction; for an honest Moore observation prefer
-- 'systemWithSeedToPoles'.
systemToPolesWithProbe :: Dir p -> System (->) s p -> Poles (Body (,) s (->)) (Dir p) (Pos p)
systemToPolesWithProbe probe sys =
  Poles.poles0
    (systemWriteBody sys)
    (Body $ \(s, ()) -> runSystem sys (s, probe))

-- | Convert a pointed 'System' into companion/conjoint channel poles over @Body@.
--
-- The state carrier is the system's state @s@ and the seed @s0@ is carried by
-- 'SomePoles'.  The write pole steps with the supplied direction; the read pole
-- observes the current state without stepping, using the supplied observation
-- function.
systemWithSeedToPoles :: s -> (s -> Pos p) -> System (->) s p -> SomePoles (,) (->) (Dir p) (Pos p)
systemWithSeedToPoles s0 ex sys =
  SomePoles s0 $
    Poles.poles0
      (systemWriteBody sys)
      (Body $ \(s, ()) -> (s, ex s))

-- | Run a monomial @(->)@ system at a state, exposing the output position and
-- the state-transition function.
runSystemMono :: System (->) s (Mono i o) -> s -> (o, i -> s)
runSystemMono sys s = case toEvalSystem sys s of EP (EK o, EE f) -> (o, f)

-- | The coalgebra-as-lens isomorphism.
--
-- A monomial system @System (->) s (Mono i o)@ is exactly a lens
-- @S y^S -> Mono i o@: the current state @s@ determines the output position
-- @o@, and each input direction @i@ determines the next state @s@.
--
-- This is the bridge to Spivak's presentation: @System s p ≅ Poly(S y^S, p)@.
systemAsLens :: System (->) s (Mono i o) -> Morphism (Mono s s) (Mono i o)
systemAsLens sys = lens get put
  where
    get s = fst (runSystemMono sys s)
    put s = snd (runSystemMono sys s)

-- | Inverse of 'systemAsLens': build a system from a lens @S y^S -> Mono i o@.
lensAsSystem :: Morphism (Mono s s) (Mono i o) -> System (->) s (Mono i o)
lensAsSystem m = fromEvalSystem $ \s ->
  case applyLens m s of
    (o, put) -> EP (EK o, EE put)

-- | Comultiplication for an /observable/ system: the output position is the
-- state. The result is a system over the two-step interface
-- @Mono o s ◁ Mono o s@, so that feeding a pair of inputs @(o1, o2)@ runs the
-- original system for two steps.
duplicateSystem :: System (->) s (Mono o s) -> System (->) s ('Comp (Mono o s) (Mono o s))
duplicateSystem sys =
  fromEvalSystem $ \s ->
    let (s0, nextStep) = runSystemMono sys s
        nextEval o =
          let (s1, step1) = runSystemMono sys (nextStep o)
           in EP (EK s1, EE step1)
     in nestedToComp (EP (EK s0, EE nextEval))

-- | Build a system whose interface is the coproduct of two monomial interfaces.
--
-- The carrier state selects the active branch at each step.  This is the
-- level-2 grammar operator on the span fragment: choice lives in the
-- polynomial interface ('Sum') rather than in the carrier-level 'if'.
branchSystem ::
  (s -> Bool) ->
  System (->) s (Mono i o) ->
  System (->) s (Mono i o) ->
  System (->) s ('Sum (Mono i o) (Mono i o))
branchSystem cond sysL sysR =
  fromEvalSystem $ \s ->
    if cond s
      then ES (Left (toEvalSystem sysL s))
      else ES (Right (toEvalSystem sysR s))

-- | Run a system with a homogeneous sum-of-monomials interface.
runSystemSum ::
  System (->) s ('Sum (Mono i o) (Mono i o)) ->
  s ->
  (Either o o, i -> s)
runSystemSum sys s = case toEvalSystem sys s of
  ES (Left (EP (EK o, EE f))) -> (Left o, f)
  ES (Right (EP (EK o, EE f))) -> (Right o, f)

-- | A single step of a heterogeneous sum-interface system.  The GADT encodes
-- the position-dependent input type: the left branch consumes an @i1@, the
-- right branch consumes an @i2@.
data SumStep s o1 i1 o2 i2 where
  SumStepL :: o1 -> (i1 -> s) -> SumStep s o1 i1 o2 i2
  SumStepR :: o2 -> (i2 -> s) -> SumStep s o1 i1 o2 i2

-- | Build a system whose interface is the coproduct of two /different/
-- monomial interfaces.  The carrier state selects the active branch at each
-- step.
branchSystemHet ::
  (s -> Bool) ->
  System (->) s (Mono i1 o1) ->
  System (->) s (Mono i2 o2) ->
  System (->) s ('Sum (Mono i1 o1) (Mono i2 o2))
branchSystemHet cond sysL sysR =
  fromEvalSystem $ \s ->
    if cond s
      then ES (Left (toEvalSystem sysL s))
      else ES (Right (toEvalSystem sysR s))

-- | Run a heterogeneous sum-interface system.
runSystemSumHet ::
  System (->) s ('Sum (Mono i1 o1) (Mono i2 o2)) ->
  s ->
  SumStep s o1 i1 o2 i2
runSystemSumHet sys s = case toEvalSystem sys s of
  ES (Left (EP (EK o, EE f))) -> SumStepL o f
  ES (Right (EP (EK o, EE f))) -> SumStepR o f

-- | A step observation in @q@, parameterized by state. 'Eval' is already the
-- GADT that pairs each position with its branch-appropriate direction consumer,
-- so it avoids the flat 'Dir q' family that makes sums impossible.
type Step s q = Eval q s

-- | Spivak's @[p,q]@-coalgebra. State @s@ is runtime, not a type index.
--
-- * 'act' gives the wiring pattern as a polynomial morphism.
-- * 'upd' takes a state and an input observation in @p@ and returns an output
--   observation in @q@, i.e. a 'Step' pairing the presented position with its
--   own direction consumer.
data Coalgebra s p q = Coalgebra
  { act :: s -> Morphism p q,
    upd :: s -> Eval p s -> Step s q
  }

-- | Run a @Coalgebra s 'Y q@ as a 'System' over @q@.
coalgebraToSystem :: (SystemEval q) => Coalgebra s 'Y q -> System (->) s q
coalgebraToSystem coal = fromEvalSystem $ \s -> upd coal s (EY s)

-- | Convert a monomial 'System' into a @Coalgebra s 'Y (Mono i o)@.
systemToCoalgebraMono :: System (->) s (Mono i o) -> Coalgebra s 'Y (Mono i o)
systemToCoalgebraMono sys =
  Coalgebra
    { act = \s -> let (o, _) = runSystemMono sys s in Point (EP (EK o, EE (const ()))),
      upd = \s _ -> toEvalSystem sys s
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
