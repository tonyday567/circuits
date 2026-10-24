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
import Circuit.Tensor (SemiTensor (..), Symmetric (..), Tensor, innerSwap, superpose)
import Circuit.Trace (FreeTrace)
import Circuit.Traced (Assoc (..), OuterSwap (..), Strength (..), Trace (..))
import Control.Monad (when)
import Data.Bifunctor (first)
import Data.Functor.Identity (Identity (..))
import Data.These (These (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- * Channel outerSwap witnesses

-- | Channel These outerSwap, presence-preserving on all seven shapes.
--
-- Mutation question: an outerSwap that re-routes /presence/ while staying an
-- involution — e.g. @These a (These b c) -> These a (These c b)@, which
-- keeps the involution law but swaps the b and c slots — flips a presence
-- bit here even though every involution round trip still passes.  Would
-- not survive deletion of the routing: caught.
theseOuterSwapPresenceOk :: Bool
theseOuterSwapPresenceOk =
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
   in all (\x -> presenceInput x == presenceOutput (outerSwap x)) cases

-- | Channel (,) outerSwap involution with distinct scalars per position, so a
-- one-scalar mutation of an implementation is caught.  Involution is an
-- instance obligation — the type does not guarantee it.
pairOuterSwapInvolutionOk :: Bool
pairOuterSwapInvolutionOk =
  let x = (1, (2, 3)) :: (Int, (Int, Int))
   in (outerSwap . outerSwap) x == x

-- | Channel Either outerSwap involution on all three injections.  All three
-- are needed: an outerSwap that routes @Right (Left b)@ back to @Right (Left
-- b)@ instead of @Left b@ survives the outer injections but fails on
-- @Left a@.
eitherOuterSwapInvolutionOk :: Bool
eitherOuterSwapInvolutionOk =
  let l = Left 1 :: Either Int (Either Bool Char)
      m = Right (Left True)
      r = Right (Right 'c')
   in all (\x -> (outerSwap . outerSwap) x == x) [l, m, r]

-- | Channel K Identity outerSwap involution — the sole falsifier for the
-- @K m@ outerSwap instance.  Mutation question: an outerSwap that is not its own
-- inverse — a dropped swap, or effect-layer state carried between calls —
-- breaks the round trip; an identity replacement for the body is not the
-- instance's obligation (involution is the law the type cannot check).
kIdentityOuterSwapInvolutionOk :: Bool
kIdentityOuterSwapInvolutionOk =
  let x = (1, (2, 3)) :: (Int, (Int, Int))
   in runK (outerSwap . outerSwap) x == Identity x

-- | Channel Op outerSwap involution, pointwise — the sole falsifier for the
-- Op-instance spend: @outerSwap = Op outerSwap@ is correct only because the base
-- outerSwap is its own inverse (Op composition reverses, so @outerSwap . outerSwap@
-- at @Op@ is the base outerSwap composed with itself backwards).
opOuterSwapInvolutionOk :: Bool
opOuterSwapInvolutionOk =
  let swapTwice :: Op (->) (Int, (Int, Int)) (Int, (Int, Int))
      swapTwice = outerSwap . outerSwap
   in runOp swapTwice (1, (2, 3)) == (1, (2, 3))

-- | Channel These outerSwap involution where types permit — the inclusive
-- outerSwap had no live witness of any kind after the slimming.
theseOuterSwapInvolutionOk :: Bool
theseOuterSwapInvolutionOk =
  let x = These 'a' (These 'b' 'c' :: These Char Char)
   in (outerSwap . outerSwap) x == (x :: These Char (These Char Char))

-- | OuterSwap decomposition at @(,)@: @outerSwap = assoc' .> tensor braid id .>
-- assoc@.  Mutation question: a hand-written outerSwap that is an involution
-- but not this composite passes every involution check above and fails
-- here — the a<->c swap @(a,(b,c)) -> (c,(b,a))@ is the named falsifier.
-- Two named inputs so a single-scalar mutation of any factor is observed.
pairOuterSwapDecomposeOk :: Bool
pairOuterSwapDecomposeOk =
  let decompose :: (Int, (Int, Int)) -> (Int, (Int, Int))
      decompose = assoc' .> tensor braid id .> assoc
      inputs = [(1, (2, 3)), (0, (5, 7))]
   in all (\x -> decompose x == outerSwap x) inputs

-- | OuterSwap decomposition at 'Either' — the three injections, same
-- falsifier as the pair case.
eitherOuterSwapDecomposeOk :: Bool
eitherOuterSwapDecomposeOk =
  let decompose :: Either Int (Either Bool Char) -> Either Bool (Either Int Char)
      decompose = assoc' .> tensor braid id .> assoc
      inputs = [Left 1, Right (Left True), Right (Right 'c')]
   in all (\x -> decompose x == outerSwap x) inputs

-- * Braid involution and derived innerSwap witnesses

-- | Braid involution at @(,)@ with distinct scalars per position.  The
-- class law is contractual — every instance is a literal swap — but
-- nothing else in the suite pins it per tensor.
pairBraidInvolutionOk :: Bool
pairBraidInvolutionOk =
  let inputs = [(1, 2), (3, 5)] :: [(Int, Int)]
   in all (\x -> (braid . braid) x == x) inputs

-- | Braid involution at 'Either' on both injections, heterogeneous per
-- position so a wrong-side routing is observed.
eitherBraidInvolutionOk :: Bool
eitherBraidInvolutionOk =
  let inputs = [Left 1, Right 'c'] :: [Either Int Char]
   in all (\x -> (braid . braid) x == x) inputs

-- | Braid involution at 'These' on all three shapes — including the
-- product swap in the 'These' case, which the injections alone cannot see.
theseBraidInvolutionOk :: Bool
theseBraidInvolutionOk =
  let inputs = [This 1, That 'a', These (1 :: Int) 'a']
   in all (\x -> (braid . braid) x == x) inputs

-- | Braid involution at @K m@ with @(,)@ — the sole falsifier for the
-- @K m@ braid instance.
kIdentityBraidInvolutionOk :: Bool
kIdentityBraidInvolutionOk =
  let x = (1, 2) :: (Int, Int)
   in runK (braid . braid) x == Identity x

-- | Derived 'innerSwap' involution at @(,)@ with distinct values in all
-- three positions, so a mutation that swaps the wrong wire pair is caught.
pairInnerSwapInvolutionOk :: Bool
pairInnerSwapInvolutionOk =
  let x = ((1, 2), 3) :: ((Int, Int), Int)
   in (innerSwap . innerSwap) x == x

-- | Derived 'innerSwap' involution at 'Either' on all three injections.
eitherInnerSwapInvolutionOk :: Bool
eitherInnerSwapInvolutionOk =
  let inputs = [Left (Left 1), Left (Right True), Right 'c'] :: [Either (Either Int Bool) Char]
   in all (\x -> (innerSwap . innerSwap) x == x) inputs

-- | Derived 'innerSwap' involution at 'These' on all seven shapes of
-- @These (These Char Bool) Int@.
theseInnerSwapInvolutionOk :: Bool
theseInnerSwapInvolutionOk =
  let inputs =
        [ This (This 'a'),
          This (That True),
          This (These 'a' True),
          That (1 :: Int),
          These (This 'a') 1,
          These (That True) 1,
          These (These 'a' True) 1
        ] ::
          [These (These Char Bool) Int]
   in all (\x -> (innerSwap . innerSwap) x == x) inputs

-- | 'innerSwap' decomposition at @(,)@: the defining composite
-- @braid .> outerSwap .> assoc'@ pinned against a second derivation from
-- the same canonical maps, @assoc .> strength braid .> assoc'@.  A
-- hand-written innerSwap that is an involution but routes the wrong pair
-- passes the involution check and fails here.
pairInnerSwapDecomposeOk :: Bool
pairInnerSwapDecomposeOk =
  let decompose :: ((Int, Int), Int) -> ((Int, Int), Int)
      decompose = assoc .> middle .> assoc'
      middle :: (Int, (Int, Int)) -> (Int, (Int, Int))
      middle = strength braid
      inputs = [((1, 2), 3), ((0, 5), 7)]
   in all (\x -> decompose x == innerSwap x) inputs

-- | 'innerSwap' decomposition at 'Either' — the three injections, same
-- falsifier as the pair case.
eitherInnerSwapDecomposeOk :: Bool
eitherInnerSwapDecomposeOk =
  let decompose :: Either (Either Int Bool) Char -> Either (Either Int Char) Bool
      decompose = assoc .> middle .> assoc'
      middle :: Either Int (Either Bool Char) -> Either Int (Either Char Bool)
      middle = strength braid
      inputs = [Left (Left 1), Left (Right True), Right 'c']
   in all (\x -> decompose x == innerSwap x) inputs

-- | 'innerSwap' decomposition at 'These' — all seven shapes.
theseInnerSwapDecomposeOk :: Bool
theseInnerSwapDecomposeOk =
  let decompose :: These (These Char Bool) Int -> These (These Char Int) Bool
      decompose = assoc .> middle .> assoc'
      middle :: These Char (These Bool Int) -> These Char (These Int Bool)
      middle = strength braid
      inputs =
        [ This (This 'a'),
          This (That True),
          This (These 'a' True),
          That 1,
          These (This 'a') 1,
          These (That True) 1,
          These (These 'a' True) 1
        ] ::
          [These (These Char Bool) Int]
   in all (\x -> decompose x == innerSwap x) inputs

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

-- | Free-strength outerSwap placement at 'Either'
-- ('Circuit.Trace' strength, @SigTrace@ clause).  The body is slid out,
-- strengthened, and slid back: @trace (Lift outerSwap .> strength body .>
-- Lift outerSwap)@.  This oracle pins the placement against evaluating first
-- and strengthening at the base.
--
-- Mutation question: drop the outerSwaps in the clause and @eval (strength t)
-- (Right 3)@ exits @Left 3@ instead of @Right 42@ — the fresh payload is
-- wired straight into the loop channel, so the placements genuinely
-- differ.  @eval t 3 == 42@ pins the loop body itself, so a body mutation
-- is caught there and not attributed to the outerSwaps.
traceEitherStrengthOk :: Bool
traceEitherStrengthOk =
  let f :: Either Int Int -> Either Int Int
      f (Right n) = Left n
      f (Left 0) = Right 42
      f (Left n) = Left (n - 1)
      t :: FreeTrace Either (->) Int Int
      t = trace (Lift f)
      leftOnly = Left 5 :: Either Int Int
      payload = Right 3 :: Either Int Int
   in eval t 3 == 42
        && eval (strength t) leftOnly == strength (eval t) leftOnly
        && eval (strength t) payload == strength (eval t) payload

-- | Superpose fusion against the lawful independent-evaluation fallback
-- on the 'Either' tensor.  The fused form spends assoc / outerSwap / strength
-- to merge two traces into one loop; the lawful 'Tensor'
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
      x, y :: FreeTrace Either (->) Int Int
      x = trace (Lift step)
      y = trace (Lift step)
      fallback :: Either Int Int -> Either Int Int
      fallback = tensor (eval x) (eval y)
   in eval (superpose x y) (Left 3) == fallback (Left 3)
        && eval (superpose x y) (Right 5) == fallback (Right 5)

-- | Superpose normalisation, extensional half: a composed input
-- (@trace f . Lift g@) is one 'Knot' after normalisation and must agree
-- with the lawful independent evaluation — the surviving doctest pins
-- only the structural @"fused"@ tag.
superposeComposedOk :: Bool
superposeComposedOk =
  let k1 :: ([Int], Int) -> ([Int], [Int])
      k1 (ns, x) = (1 : ns, take 3 ns ++ [x])
      composed :: FreeTrace (,) (->) Int [Int]
      composed = trace (Lift k1) . Lift (+ 100)
      other :: FreeTrace (,) (->) Int Int
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
-- Re-derived over living 'Trace Either': the old scaffolding (Body,
-- feedbackBody, runFlowchart) was deleted in the wave-4a sweep, so the
-- closed loops below keep feedbackBody's plumbing — @assoc .> f .> assoc'@
-- re-embeds the feedback wire as the carrier, with the vacuous 'Void'
-- carrier kept explicit — and close it with the living 'trace'.  No deleted
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
  let traceOk = all (\n -> trace uniformitySrcClosed n == trace uniformityTgtClosed n) [0 .. 3]
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
-- on the wrong side of the trace is observable: an outerSwap applied to the
-- wrong side strands the wire state off the 3-cycle and the two traces
-- disagree.
slidingOk :: Bool
slidingOk =
  all (\n -> trace slidingLhsClosed n == trace slidingRhsClosed n) [0 .. 3]

tracedTopic :: Verbosity -> IO [Bool]
tracedTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Traced oracles: base structural laws and their composite spends"
  sequence
    [ checkV verbosity "Channel These outerSwap preserves presence on all 7 cases" theseOuterSwapPresenceOk,
      checkV verbosity "Channel (,) outerSwap . outerSwap == id" pairOuterSwapInvolutionOk,
      checkV verbosity "Channel Either outerSwap . outerSwap == id on all three injections" eitherOuterSwapInvolutionOk,
      checkV verbosity "Channel K Identity outerSwap . outerSwap == id" kIdentityOuterSwapInvolutionOk,
      checkV verbosity "Channel Op outerSwap . outerSwap == id pointwise (the Op instance spends involution)" opOuterSwapInvolutionOk,
      checkV verbosity "Channel These outerSwap . outerSwap == id where types permit" theseOuterSwapInvolutionOk,
      checkV verbosity "outerSwap decomposes as assoc' . tensor braid id . assoc at (,)" pairOuterSwapDecomposeOk,
      checkV verbosity "outerSwap decomposes as assoc' . tensor braid id . assoc at Either" eitherOuterSwapDecomposeOk,
      checkV verbosity "braid . braid == id at (,)" pairBraidInvolutionOk,
      checkV verbosity "braid . braid == id at Either" eitherBraidInvolutionOk,
      checkV verbosity "braid . braid == id at These" theseBraidInvolutionOk,
      checkV verbosity "braid . braid == id at K Identity" kIdentityBraidInvolutionOk,
      checkV verbosity "innerSwap . innerSwap == id at (,) with distinct values in all three positions" pairInnerSwapInvolutionOk,
      checkV verbosity "innerSwap . innerSwap == id at Either on all three injections" eitherInnerSwapInvolutionOk,
      checkV verbosity "innerSwap . innerSwap == id at These on all seven shapes" theseInnerSwapInvolutionOk,
      checkV verbosity "innerSwap decomposes as assoc . strength braid . assoc' at (,)" pairInnerSwapDecomposeOk,
      checkV verbosity "innerSwap decomposes as assoc . strength braid . assoc' at Either" eitherInnerSwapDecomposeOk,
      checkV verbosity "innerSwap decomposes as assoc . strength braid . assoc' at These" theseInnerSwapDecomposeOk,
      checkV verbosity "associator round trip at Either in both directions" eitherAssocRoundTripOk,
      checkV verbosity "associator round trip at These in both directions" theseAssocRoundTripOk,
      checkV verbosity "Channel (,) assoc . assoc' == id (the half not doctested)" pairAssocCancelOk,
      checkV verbosity "FreeTrace Either strength: eval-then-strengthen == strengthen-then-eval" traceEitherStrengthOk,
      checkV verbosity "superpose fusion agrees with the fallback on the Either tensor" superposeEitherFusionOk,
      checkV verbosity "superpose composed shape agrees with independent evaluation" superposeComposedOk,
      checkV verbosity "strength coherence (strength f == tensor id f)" pairStrengthCoherenceOk,
      checkV verbosity "Either strength coherence (strength f == tensor id f)" eitherStrengthCoherenceOk,
      checkV verbosity "These strength coherence (strength f == tensor id f)" theseStrengthCoherenceOk,
      checkV verbosity "Either uniformity: feedback respects non-injective two-cell" uniformityOk,
      checkV verbosity "Either sliding (dinaturality) for isomorphism" slidingOk
    ]
