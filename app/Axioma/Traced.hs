-- | Traced oracles: the 'Circuit.Traced' structural ladder at the base
-- arrows @(,)@, 'Either', @K m@, and @Op arr@, plus the composite spends of
-- that ladder in the free 'Circuit.Trace' strength and 'Circuit.Tensor'
-- superposition.
--
-- The wave-4a slimming deleted the pointwise witnesses for the living
-- base-instance laws; this topic rehomes them. Every check is named for its
-- counterexample — see the per-block notes above each witness.
module Axioma.Traced
  ( tracedTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Category (Op (..), id, runK, runOp, (.), (.>))
import Circuit.Syntax (Syntax (..), eval)
import Circuit.Tensor (Action (..), SemiTensor (..), Tensor, superpose)
import Circuit.Trace (Trace)
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Control.Monad (when)
import Data.Bifunctor (first)
import Data.Functor.Identity (Identity (..))
import Data.These (These (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- * Channel slide witnesses

-- | Channel These slide, presence-preserving on all seven shapes.
--
-- Mutation question: a slide that re-routes /presence/ while staying an
-- involution — e.g. @These a (These b c) -> These a (These c b)@, which
-- keeps the involution law but swaps the b and c slots — flips a presence
-- bit here even though every involution round trip still passes.  Would
-- not survive deletion of the routing: caught.
theseSlidePresenceOk :: Bool
theseSlidePresenceOk =
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
   in all (\x -> presenceInput x == presenceOutput (slide x)) cases

-- | Channel (,) slide involution with distinct scalars per position, so a
-- one-scalar mutation of an implementation is caught.  Involution is an
-- instance obligation — the type does not guarantee it.
pairSlideInvolutionOk :: Bool
pairSlideInvolutionOk =
  let x = (1, (2, 3)) :: (Int, (Int, Int))
   in (slide . slide) x == x

-- | Channel Either slide involution on all three injections.  All three
-- are needed: a slide that routes @Right (Left b)@ back to @Right (Left
-- b)@ instead of @Left b@ survives the outer injections but fails on
-- @Left a@.
eitherSlideInvolutionOk :: Bool
eitherSlideInvolutionOk =
  let l = Left 1 :: Either Int (Either Bool Char)
      m = Right (Left True)
      r = Right (Right 'c')
   in all (\x -> (slide . slide) x == x) [l, m, r]

-- | Channel K Identity slide involution — the sole falsifier for the
-- @K m@ slide instance.  Mutation question: a slide that is not its own
-- inverse — a dropped swap, or effect-layer state carried between calls —
-- breaks the round trip; an identity replacement for the body is not the
-- instance's obligation (involution is the law the type cannot check).
kIdentitySlideInvolutionOk :: Bool
kIdentitySlideInvolutionOk =
  let x = (1, (2, 3)) :: (Int, (Int, Int))
   in runK (slide . slide) x == Identity x

-- | Channel Op slide involution, pointwise — the sole falsifier for the
-- Op-instance spend: @slide = Op slide@ is correct only because the base
-- slide is its own inverse (Op composition reverses, so @slide . slide@
-- at @Op@ is the base slide composed with itself backwards).
opSlideInvolutionOk :: Bool
opSlideInvolutionOk =
  let swapTwice :: Op (->) (Int, (Int, Int)) (Int, (Int, Int))
      swapTwice = slide . slide
   in runOp swapTwice (1, (2, 3)) == (1, (2, 3))

-- | Channel These slide involution where types permit — the inclusive
-- slide had no live witness of any kind after the slimming.
theseSlideInvolutionOk :: Bool
theseSlideInvolutionOk =
  let x = These 'a' (These 'b' 'c' :: These Char Char)
   in (slide . slide) x == (x :: These Char (These Char Char))

-- | Slide decomposition at @(,)@: @slide = assoc' .> tensor braid id .>
-- assoc@.  Mutation question: a hand-written slide that is an involution
-- but not this composite passes every involution check above and fails
-- here — the a<->c swap @(a,(b,c)) -> (c,(b,a))@ is the named falsifier.
-- Two named inputs so a single-scalar mutation of any factor is observed.
pairSlideDecomposeOk :: Bool
pairSlideDecomposeOk =
  let decompose :: (Int, (Int, Int)) -> (Int, (Int, Int))
      decompose = assoc' .> tensor braid id .> assoc
      inputs = [(1, (2, 3)), (0, (5, 7))]
   in all (\x -> decompose x == slide x) inputs

-- | Slide decomposition at 'Either' — the three injections, same
-- falsifier as the pair case.
eitherSlideDecomposeOk :: Bool
eitherSlideDecomposeOk =
  let decompose :: Either Int (Either Bool Char) -> Either Bool (Either Int Char)
      decompose = assoc' .> tensor braid id .> assoc
      inputs = [Left 1, Right (Left True), Right (Right 'c')]
   in all (\x -> decompose x == slide x) inputs

-- | Associator round trip at 'Either' in both directions.  A swapped
-- assoc/assoc' body pair is self-consistent — the one-direction doctests
-- keep passing — and only a round trip catches it.  Named nested values
-- per direction so a single-shape mutation of either body is observed.
eitherAssocRoundTripOk :: Bool
eitherAssocRoundTripOk =
  let xs = [Left (Left 1), Left (Right True), Right 'c'] :: [Either (Either Int Bool) Char]
      ys = [Left 1, Right (Left True), Right (Right 'c')] :: [Either Int (Either Bool Char)]
   in all (\x -> (assoc' . assoc) x == x) xs
        && all (\y -> (assoc . assoc') y == y) ys

-- | Associator round trip at 'These' in both directions.  No doctest
-- exists at all for the These associator; this is the only witness of
-- cancellation in either direction.
theseAssocRoundTripOk :: Bool
theseAssocRoundTripOk =
  let xs = [This (This 'a'), This (That True), That 1, These (This 'a') 1] :: [These (These Char Bool) Int]
      ys = [This 'a', That (This True), That (That 1), These 'a' (That 1)] :: [These Char (These Bool Int)]
   in all (\x -> (assoc' . assoc) x == x) xs
        && all (\y -> (assoc . assoc') y == y) ys

-- | The @assoc . assoc'@ cancellation half at @(,)@, the residual of the
-- wave-4a drop not already doctested at "Circuit.Traced" (the
-- @assoc' . assoc@ half lives there).
pairAssocCancelOk :: Bool
pairAssocCancelOk =
  let y = (1, (2, 3)) :: (Int, (Int, Int))
   in (assoc . assoc') y == y

-- * Composite spends of the base ladder

-- | Free-strength slide placement at 'Either'
-- ('Circuit.Trace' strength, @YankBody@ clause).  The body is slid out,
-- strengthened, and slid back: @yank (Lift slide .> strength body .>
-- Lift slide)@.  This oracle pins the placement against evaluating first
-- and strengthening at the base.
--
-- Mutation question: drop the slides in the clause and @eval (strength t)
-- (Right 3)@ exits @Left 3@ instead of @Right 42@ — the fresh payload is
-- wired straight into the loop channel, so the placements genuinely
-- differ.  @eval t 3 == 42@ pins the loop body itself, so a body mutation
-- is caught there and not attributed to the slides.
traceEitherStrengthOk :: Bool
traceEitherStrengthOk =
  let f :: Either Int Int -> Either Int Int
      f (Right n) = Left n
      f (Left 0) = Right 42
      f (Left n) = Left (n - 1)
      t :: Trace Either (->) Int Int
      t = yank (Lift f)
      leftOnly = Left 5 :: Either Int Int
      payload = Right 3 :: Either Int Int
   in eval t 3 == 42
        && eval (strength t) leftOnly == strength (eval t) leftOnly
        && eval (strength t) payload == strength (eval t) payload

-- | Superpose fusion against the lawful independent-evaluation fallback
-- on the 'Either' tensor.  The fused form spends assoc / slide / strength
-- to merge two yanks into one loop; the lawful 'Tensor'
-- ('Circuit.Trace') fallback evaluates each branch independently.  The
-- named countdown body writes distinct markers per channel, so a swapped
-- pre/post scaffold mis-wires a loop channel and the outputs differ.
-- (The sharedBy-vs-superpose discriminator cannot see a wrong
-- rearrangement — it still reads as shared vs independent.)
superposeEitherFusionOk :: Bool
superposeEitherFusionOk =
  let step :: Either Int Int -> Either Int Int
      step (Right n) = Left n
      step (Left 0) = Right 100
      step (Left n) = Left (n - 1)
      x, y :: Trace Either (->) Int Int
      x = yank (Lift step)
      y = yank (Lift step)
      fallback :: Either Int Int -> Either Int Int
      fallback = tensor (eval x) (eval y)
   in eval (superpose x y) (Left 3) == fallback (Left 3)
        && eval (superpose x y) (Right 5) == fallback (Right 5)

-- | Superpose normalisation, extensional half: a composed input
-- (@yank f . Lift g@) is one 'Knot' after normalisation and must agree
-- with the lawful independent evaluation — the surviving doctest pins
-- only the structural @"fused"@ tag.
superposeComposedOk :: Bool
superposeComposedOk =
  let k1 :: ([Int], Int) -> ([Int], [Int])
      k1 (ns, x) = (1 : ns, take 3 ns ++ [x])
      composed :: Trace (,) (->) Int [Int]
      composed = yank (Lift k1) . Lift (+ 100)
      other :: Trace (,) (->) Int Int
      other = Lift (* 2)
      fused :: (Int, Int) -> ([Int], Int)
      fused = eval (superpose composed other)
      independent :: (Int, Int) -> ([Int], Int)
      independent = eval (tensor composed other)
   in fused (3, 4) == independent (3, 4)

-- * Cross-class coherence

-- | (,) strength coherence: 'strength' must agree with @tensor id@.  A
-- strength with swapped fst/snd projections (or a tensor second-slot
-- mutation) passes involution and round-trip checks and fails here.
pairStrengthCoherenceOk :: Bool
pairStrengthCoherenceOk =
  let f = (+ 1) :: Int -> Int
      space = [(s, x) | s <- [-2 .. 2], x <- [-2 .. 2]] :: [(Int, Int)]
   in all (\p -> strength f p == tensor id f p) space

-- | Either strength coherence: 'Strength Either' is the functorial
-- action, which must agree with 'Tensor Either' slot wiring.  The space
-- mixes 'Char' and 'Int', so a leg swap is observable.
eitherStrengthCoherenceOk :: Bool
eitherStrengthCoherenceOk =
  let f = (+ 1) :: Int -> Int
      space = [Left 'a', Right 0, Right 1, Left 'b']
   in all (\x -> strength f x == tensor id f x) space

-- | These strength coherence: 'Strength These' touches only the payload
-- and the 'These' second component, never the 'This' residual — the
-- space includes @This 'a'@ so a residual-touching mutation is caught.
theseStrengthCoherenceOk :: Bool
theseStrengthCoherenceOk =
  let f = (+ 1) :: Int -> Int
      space =
        [ This 'a',
          That 0,
          That 1,
          These 'b' 2,
          These 'c' (-1)
        ]
   in all (\x -> strength f x == tensor id f x) space

-- * Uniformity / sliding oracles for Either feedback

--
-- Re-derived over living 'Yank Either': the old scaffolding (Body,
-- feedbackBody, runFlowchart) was deleted in the wave-4a sweep, so the
-- closed loops below keep feedbackBody's plumbing — @assoc .> f .> assoc'@
-- re-embeds the feedback wire as the carrier, with the vacuous 'Void'
-- carrier kept explicit — and close it with the living 'yank'.  No deleted
-- name is resurrected.

-- | Open loop body for the uniformity witness: a fresh input @a@ moves
-- onto the feedback wire; a fed-back @n@ halts with 7 or 9 by the wire
-- value's parity.
uniformitySrcOpen :: Either Void (Either Int Int) -> Either Void (Either Int Int)
uniformitySrcOpen (Right (Right a)) = Right (Left a)
uniformitySrcOpen (Right (Left n)) = Right (Right (if odd n then 7 else 9))
uniformitySrcOpen (Left v) = absurd v

-- | Target body: same loop with the feedback wire quotiented by
-- @odd :: Int -> Bool@.
uniformityTgtOpen :: Either Void (Either Bool Int) -> Either Void (Either Bool Int)
uniformityTgtOpen (Right (Right a)) = Right (Left (odd a))
uniformityTgtOpen (Right (Left b)) = Right (Right (if b then 7 else 9))
uniformityTgtOpen (Left v) = absurd v

-- | Uniformity hypothesis on the open bodies: quotienting the feedback
-- wire with @odd@ commutes with the two bodies.  Checked separately from
-- the conclusion so a hypothesis failure is not read as a law failure.
uniformityHypothesisOk :: Bool
uniformityHypothesisOk =
  let h :: Either Int Int -> Either Bool Int
      h = first odd
      payloadSpace :: [Either Void (Either Int Int)]
      payloadSpace = map Right [Right 0, Right 1, Right 2, Left 0, Left 1, Left 2]
   in all (\x -> fmap h (uniformitySrcOpen x) == uniformityTgtOpen (fmap h x)) payloadSpace

-- | Closed uniformity loops: the feedback wire becomes the carrier via
-- the associator plumbing, as in the deleted feedbackBody.
uniformitySrcClosed :: Either (Either Void Int) Int -> Either (Either Void Int) Int
uniformitySrcClosed = assoc .> uniformitySrcOpen .> assoc'

uniformityTgtClosed :: Either (Either Void Bool) Int -> Either (Either Void Bool) Int
uniformityTgtClosed = assoc .> uniformityTgtOpen .> assoc'

-- | Uniformity conclusion: a non-injective two-cell makes feedback
-- invariant under a genuine quotient of the feedback wire.  Both wires
-- carry two reachable values and the halt value depends on which wire
-- state the loop halts from, so this distinguishes "invariant under
-- quotient" from "collapse to a point" — a trace that ignored the wire
-- entirely would still agree.
uniformityOk :: Bool
uniformityOk =
  let traceOk = all (\n -> yank uniformitySrcClosed n == yank uniformityTgtClosed n) [0 .. 3]
   in uniformityHypothesisOk && traceOk

-- | A three-element cyclic group for the sliding witness.  We need an
-- isomorphism that is not self-inverse; 'Bool' has only identity,
-- negation, and constants, so it cannot carry a non-involutive iso.
data Z3 = Z0 | Z1 | Z2
  deriving (Eq, Show)

-- | Cyclic shift on 'Z3'.
nextZ3 :: Z3 -> Z3
nextZ3 Z0 = Z1
nextZ3 Z1 = Z2
nextZ3 Z2 = Z0

-- | Loop body for the sliding witness: steps through 'Z3' and halts with
-- a value depending on the wire state, so the wire is genuinely observed.
slidingF :: Either Void (Either Z3 Int) -> Either Void (Either Z3 Int)
slidingF (Right (Right a))
  | even a = Right (Left Z0)
slidingF (Right (Right _)) = Right (Left Z1)
slidingF (Right (Left Z0)) = Right (Right 10)
slidingF (Right (Left Z1)) = Right (Right 20)
slidingF (Right (Left Z2)) = Right (Right 30)
slidingF (Left v) = absurd v

-- | The sliding isomorphism: @nextZ3@ on the feedback wire, identity on
-- the payload.
slidingH :: Either Void (Either Z3 Int) -> Either Void (Either Z3 Int)
slidingH (Right (Left z)) = Right (Left (nextZ3 z))
slidingH (Right (Right a)) = Right (Right a)
slidingH (Left v) = absurd v

-- | Closed sliding loops: @h@ before @f@ versus @f@ before @h@.
slidingLhsClosed, slidingRhsClosed :: Either (Either Void Z3) Int -> Either (Either Void Z3) Int
slidingLhsClosed = assoc .> (slidingH . slidingF) .> assoc'
slidingRhsClosed = assoc .> (slidingF . slidingH) .> assoc'

-- | Sliding (dinaturality) for an isomorphism on the feedback wire.
-- @nextZ3@ is a three-cycle, not an involution, so applying the wire map
-- on the wrong side of the trace is observable: a slide applied to the
-- wrong side strands the wire state off the 3-cycle and the two traces
-- disagree.
slidingOk :: Bool
slidingOk =
  all (\n -> yank slidingLhsClosed n == yank slidingRhsClosed n) [0 .. 3]

tracedTopic :: Verbosity -> IO [Bool]
tracedTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Traced oracles: base structural laws and their composite spends"
  sequence
    [ checkV verbosity "Channel These slide preserves presence on all 7 cases" theseSlidePresenceOk,
      checkV verbosity "Channel (,) slide . slide == id" pairSlideInvolutionOk,
      checkV verbosity "Channel Either slide . slide == id on all three injections" eitherSlideInvolutionOk,
      checkV verbosity "Channel K Identity slide . slide == id" kIdentitySlideInvolutionOk,
      checkV verbosity "Channel Op slide . slide == id pointwise (the Op instance spends involution)" opSlideInvolutionOk,
      checkV verbosity "Channel These slide . slide == id where types permit" theseSlideInvolutionOk,
      checkV verbosity "slide decomposes as assoc' . tensor braid id . assoc at (,)" pairSlideDecomposeOk,
      checkV verbosity "slide decomposes as assoc' . tensor braid id . assoc at Either" eitherSlideDecomposeOk,
      checkV verbosity "associator round trip at Either in both directions" eitherAssocRoundTripOk,
      checkV verbosity "associator round trip at These in both directions" theseAssocRoundTripOk,
      checkV verbosity "Channel (,) assoc . assoc' == id (the half not doctested)" pairAssocCancelOk,
      checkV verbosity "Trace Either strength: eval-then-strengthen == strengthen-then-eval" traceEitherStrengthOk,
      checkV verbosity "superpose fusion agrees with the fallback on the Either tensor" superposeEitherFusionOk,
      checkV verbosity "superpose composed shape agrees with independent evaluation" superposeComposedOk,
      checkV verbosity "strength coherence (strength f == tensor id f)" pairStrengthCoherenceOk,
      checkV verbosity "Either strength coherence (strength f == tensor id f)" eitherStrengthCoherenceOk,
      checkV verbosity "These strength coherence (strength f == tensor id f)" theseStrengthCoherenceOk,
      checkV verbosity "Either uniformity: feedback respects non-injective two-cell" uniformityOk,
      checkV verbosity "Either sliding (dinaturality) for isomorphism" slidingOk
    ]
