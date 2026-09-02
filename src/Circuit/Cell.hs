{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Loose bicategory of 'Circuit.Body.Body' values with varying carriers.
--
-- A KSW loose 1-cell is a body @arr (t ch a) (t ch b)@ with its carrier @ch@
-- hidden.  The 2-cells are carrier two-cells: maps @α : ch -> ch'@ that make
-- the Mealy square commute.  'Body' is the fibre at fixed carrier; 'Cell' is
-- the coproduct of those fibres, and 'Sq' / 'TwoCell' move between them.
--
-- == Carrier-tensoring composition
--
-- @cascade@ composes two bodies whose carriers are tensored:
--
-- @
--   f :: Body t ch  arr a b
--   g :: Body t ch' arr b c
--   cascade g f :: Cell t arr a c   -- carrier  t ch ch'
-- @
--
-- The composite is
--
-- @
--   assoc .> slide .> strength f .> slide .> strength g .> assoc'
-- @
--
-- using 'Circuit.Traced.assoc', 'assoc'', 'slide' and 'strength'.  No
-- braiding/'Action' is needed because 'slide' already swaps the second carrier
-- past the payload.
--
-- == Law witnesses
--
-- The bicategory laws hold only up to invertible 'Sq' witnesses: carriers
-- @ch ⊗ (ch' ⊗ ch'')@ and @(ch ⊗ ch') ⊗ ch''@ are different Haskell types, so
-- on-the-nose associativity is impossible.  The proof artifact is the
-- two-cell itself; the falsification artifact is observational, via
-- 'Circuit.Body.mergeChannel' and the 'Process' runner.
module Circuit.Cell
  ( -- * Loose 1-cell (carrier hidden)
    Cell (..),
    idCell,

    -- * Indexed 2-cell (carrier map + commuting square)
    Sq (..),
    idSq,
    vcomp,

    -- * Existential closure of Sq
    TwoCell (..),
    withTwoCell,

    -- * The two paths whose equality is the square
    downThenAcross,
    acrossThenDown,

    -- * Carrier-tensoring composition
    cascade,

    -- * Structural proof witnesses (unitors and associator)
    unitorLeft,
    unitorRight,
    unitorLeftSq,
    unitorRightSq,
    associator,
    associatorSq,

    -- * Feedback (closed loop over a carrier component)
    feedback,

    -- * Elgot dagger (feedback over 'Either' as iteration)
    elgotBody,
    elgotDagger,
    elgotFeedbackBody,

    -- * Bisimulation (behavioural quotient of bodies)
    bisimilarStates,
    isBisimulation,
    maxBisimulation,

    -- * Horizontal 2-cell algebra
    rightWhisker,
    leftWhisker,
    hcompose,
    whiskerSq,
  )
where

import Circuit.Body (Body (..), mergeChannel)
import Circuit.Category (Category (..), (.>))
import Circuit.Tensor (Tensor (..), Unit, Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Circuit.Cell
-- >>> import Circuit.Body (Body (..))

-- | Loose 1-cell: a body with its carrier type hidden.
data Cell t arr a b where
  Cell :: Body t ch arr a b -> Cell t arr a b

-- | Identity loose 1-cell at the tensor unit carrier.
--
-- The carrier is pinned to 'Unit' so that the unit law can be witnessed with
-- the unitor; without the annotation GHC would instantiate the hidden carrier
-- to 'Any'.
idCell :: forall t arr a. (Strength t arr) => Cell t arr a a
idCell = Cell (Body id :: Body t (Unit t) arr a a)

-- | Square (indexed 2-cell).  The carrier maps compose; the middle body must
-- match (a caller side condition).
data Sq t arr ch ch' a b = Sq
  { -- | Map between carriers.
    carrierMap :: arr ch ch',
    -- | Source body, over the source carrier.
    sqSrc :: Body t ch arr a b,
    -- | Target body, over the target carrier.
    sqTgt :: Body t ch' arr a b
  }

-- | Identity square on a body.
idSq :: (Category arr) => Body t ch arr a b -> Sq t arr ch ch a b
idSq b = Sq id b b

-- | Vertical composition of squares.
--
-- The middle body must match; this is a caller side condition.
vcomp ::
  (Category arr) =>
  Sq t arr ch' ch'' a b ->
  Sq t arr ch ch' a b ->
  Sq t arr ch ch'' a b
vcomp g f = Sq (carrierMap f .> carrierMap g) (sqSrc f) (sqTgt g)

-- | Existential closure of 'Sq', for stating "there exists a 2-cell".
data TwoCell t arr a b where
  TwoCell :: Sq t arr ch ch' a b -> TwoCell t arr a b

-- | Eliminator for the existential carrier types of a 'TwoCell'.
withTwoCell ::
  TwoCell t arr a b ->
  (forall ch ch'. Sq t arr ch ch' a b -> r) ->
  r
withTwoCell (TwoCell sq) k = k sq

-- | Go down (carrier map) then across (target body).
--
-- A nondegenerate two-cell witness: counter state quotiented by parity.
-- The payload is 'Char' so the carrier slot and payload slot are type-distinct;
-- slot confusion is a type error.  These examples exercise both parities and
-- both reset branches.  A paired perturbation doctest on 'acrossThenDown'
-- shows the equality can fail, so these agreement cases are not vacuous.
--
-- >>> let counter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if odd n' then 'x' else 'y')) :: Body (,) Int (->) Bool Char
-- >>> let parity = (Body $ \(b, r) -> let b' = not r && not b in (b', if b' then 'x' else 'y')) :: Body (,) Bool (->) Bool Char
-- >>> let sq = Sq odd counter parity :: Sq (,) (->) Int Bool Bool Char
-- >>> downThenAcross sq (4, False)
-- (True,'x')
-- >>> downThenAcross sq (4, True)
-- (False,'y')
-- >>> downThenAcross sq (5, False)
-- (False,'y')
downThenAcross ::
  (Tensor t arr) =>
  Sq t arr ch ch' a b ->
  arr (t ch a) (t ch' b)
downThenAcross sq = tensor (carrierMap sq) id .> morphism (sqTgt sq)

-- | Go across (source body) then down (carrier map).
--
-- Agreement cases for the same witness:
--
-- >>> let counter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if odd n' then 'x' else 'y')) :: Body (,) Int (->) Bool Char
-- >>> let parity = (Body $ \(b, r) -> let b' = not r && not b in (b', if b' then 'x' else 'y')) :: Body (,) Bool (->) Bool Char
-- >>> let sq = Sq odd counter parity :: Sq (,) (->) Int Bool Bool Char
-- >>> acrossThenDown sq (4, False)
-- (True,'x')
-- >>> acrossThenDown sq (4, True)
-- (False,'y')
-- >>> acrossThenDown sq (5, False)
-- (False,'y')
--
-- Perturbation: observe even-ness instead of odd-ness.  The two paths now
-- disagree, which proves the agreement cases above are not vacuous.
--
-- >>> let badCounter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if even n' then 'x' else 'y')) :: Body (,) Int (->) Bool Char
-- >>> let bad = Sq odd badCounter parity :: Sq (,) (->) Int Bool Bool Char
-- >>> downThenAcross bad (4, False)
-- (True,'x')
-- >>> acrossThenDown bad (4, False)
-- (True,'y')
acrossThenDown ::
  (Tensor t arr) =>
  Sq t arr ch ch' a b ->
  arr (t ch a) (t ch' b)
acrossThenDown sq = morphism (sqSrc sq) .> tensor (carrierMap sq) id

-- | Carrier-tensoring composition of loose 1-cells.
--
-- The composite has carrier @t ch ch'@ when the first body has carrier @ch@
-- and the second has carrier @ch'@.
cascade ::
  (Strength t arr) =>
  Cell t arr b c ->
  Cell t arr a b ->
  Cell t arr a c
cascade (Cell g) (Cell f) = Cell (mergeChannel g f)

-- | Indexed left unitor square.
unitorLeftSq ::
  (Unital t arr, Strength t arr) =>
  Body t ch arr a b ->
  Sq t arr (t (Unit t) ch) ch a b
unitorLeftSq b = Sq unitl (mergeChannel b (Body id)) b

-- | Left unitor witness: composing a body with the identity at the unit carrier
-- is isomorphic to the original body.
unitorLeft ::
  (Unital t arr, Strength t arr) =>
  Body t ch arr a b ->
  TwoCell t arr a b
unitorLeft b = TwoCell (unitorLeftSq b)

-- | Indexed right unitor square.
unitorRightSq ::
  (Unital t arr, Strength t arr) =>
  Body t ch arr a b ->
  Sq t arr (t ch (Unit t)) ch a b
unitorRightSq b = Sq unitr (mergeChannel (Body id) b) b

-- | Right unitor witness.
unitorRight ::
  (Unital t arr, Strength t arr) =>
  Body t ch arr a b ->
  TwoCell t arr a b
unitorRight b = TwoCell (unitorRightSq b)

-- | Indexed associator square.
associatorSq ::
  (Strength t arr) =>
  Body t ch3 arr c d ->
  Body t ch2 arr b c ->
  Body t ch1 arr a b ->
  Sq t arr (t (t ch1 ch2) ch3) (t ch1 (t ch2 ch3)) a d
associatorSq h g f =
  Sq
    assoc
    (mergeChannel h (mergeChannel g f))
    (mergeChannel (mergeChannel h g) f)

-- | Associator witness: carrier bracketing of three composed bodies is
-- isomorphic up to the associator of the tensor.
associator ::
  (Strength t arr) =>
  Body t ch3 arr c d ->
  Body t ch2 arr b c ->
  Body t ch1 arr a b ->
  TwoCell t arr a d
associator h g f = TwoCell (associatorSq h g f)

-- | Right whisker: tensor a square with an identity-on-boundaries 1-cell on
-- the right.
rightWhisker ::
  (Tensor t arr, Strength t arr) =>
  Sq t arr ch ch' a b ->
  Body t d arr b c ->
  Sq t arr (t ch d) (t ch' d) a c
rightWhisker sq r =
  Sq
    (tensor (carrierMap sq) id)
    (mergeChannel r (sqSrc sq))
    (mergeChannel r (sqTgt sq))

-- | Left whisker: tensor an identity-on-boundaries 1-cell on the left of a
-- square.
leftWhisker ::
  (Tensor t arr, Strength t arr) =>
  Body t d arr a' a ->
  Sq t arr ch ch' a b ->
  Sq t arr (t d ch) (t d ch') a' b
leftWhisker l sq =
  Sq
    (tensor id (carrierMap sq))
    (mergeChannel (sqSrc sq) l)
    (mergeChannel (sqTgt sq) l)

-- | Horizontal composition of two squares.
hcompose ::
  (Tensor t arr, Strength t arr) =>
  Sq t arr ch2 ch2' b c ->
  Sq t arr ch1 ch1' a b ->
  Sq t arr (t ch1 ch2) (t ch1' ch2') a c
hcompose sq2 sq1 =
  Sq
    (tensor (carrierMap sq1) (carrierMap sq2))
    (mergeChannel (sqSrc sq2) (sqSrc sq1))
    (mergeChannel (sqTgt sq2) (sqTgt sq1))

-- | Boundary whisker: apply tight maps to the input and output boundaries of a
-- square.  This is the `Sq` side of the interchange law; the `Poles` side is
-- `iomap` on the Moore-split representation.
whiskerSq ::
  (Tensor t arr) =>
  arr a' a ->
  arr b b' ->
  Sq t arr ch ch' a b ->
  Sq t arr ch ch' a' b'
whiskerSq f g sq =
  Sq
    (carrierMap sq)
    (Body $ tensor id f .> morphism (sqSrc sq) .> tensor id g)
    (Body $ tensor id f .> morphism (sqTgt sq) .> tensor id g)

-- | Close a feedback loop over a component @s@ of the input/output object.
--
-- The 1-cell must be of the form @Cell t arr (t s a) (t s b)@: the feedback
-- value @s@ appears as the first component of the tensor in both domain and
-- codomain.  The result moves @s@ into the hidden carrier, turning it into
-- state.  This is the guarded / state-bootstrapping feedback of KSW, not the
-- immediate fixed-point trace: yanking fails here, which is the expected
-- behaviour for a feedback category.
--
-- Implemented by reassociating so that @s@ becomes part of the carrier:
--
-- @
--   feedback (Cell (Body f)) = Cell (Body (assoc .> f .> assoc'))
-- @
feedback ::
  (Assoc t arr) =>
  Cell t arr (t s a) (t s b) ->
  Cell t arr a b
feedback (Cell (Body f)) = Cell $ Body $ assoc .> f .> assoc'

-- * Elgot dagger

-- | Build the Elgot coalgebra @[Left, f]@ from a loop body @f :: a -> Either a b@.
--
-- The resulting body has the 'Void' unit carrier and payload
-- @Either a a -> Either a b@, so it can be passed to 'feedback'.  The dagger
-- of @f@ is then a morphism @a -> b@ in 'Cell'.
elgotBody :: (a -> Either a b) -> Body Either Void (->) (Either a a) (Either a b)
elgotBody f =
  Body $ \case
    Right (Left s) -> wrap (f s)
    Right (Right a) -> wrap (f a)
    Left v -> absurd v
  where
    wrap (Left s) = Right (Left s)
    wrap (Right b) = Right (Right b)

-- | The feedback body of the Elgot dagger of @f :: a -> Either a b@.
--
-- Exposed so that callers can run it directly with a seed of type
-- @Either Void a@, which is the hidden carrier produced by 'feedback'.
elgotFeedbackBody :: (a -> Either a b) -> Body Either (Either Void a) (->) a b
elgotFeedbackBody f = Body $ assoc .> morphism (elgotBody f) .> assoc'

-- | Elgot dagger of @f :: a -> Either a b@ via 'feedback'.
elgotDagger :: (a -> Either a b) -> Cell Either (->) a b
elgotDagger f = Cell (elgotFeedbackBody f)

-- * Bisimulation

-- | Step a @(,) / (->)@ body: given a state and an input, return the next
-- state and output.
stepBody :: Body (,) s (->) a b -> s -> a -> (s, b)
stepBody (Body f) s a = f (s, a)

-- | Check whether a relation is a bisimulation between two finite-state bodies.
--
-- The relation must be over the provided state spaces; the check is exact over
-- the bounded input alphabet.  A relation @R@ is a bisimulation when for every
-- @(s1, s2) ∈ R@ and every input @a@, the outputs coincide and the successor
-- states are again @R@-related.
isBisimulation ::
  (Eq s1, Eq s2, Eq b) =>
  [a] ->
  Body (,) s1 (->) a b ->
  Body (,) s2 (->) a b ->
  [(s1, s2)] ->
  Bool
isBisimulation inputs body1 body2 rel =
  all
    ( \(s1, s2) ->
        all
          ( \a ->
              let (s1', b1) = stepBody body1 s1 a
                  (s2', b2) = stepBody body2 s2 a
               in b1 == b2 && (s1', s2') `elem` rel
          )
          inputs
    )
    rel

-- | Compute the maximal bisimulation between two finite-state bodies over a
-- bounded input alphabet.  The state spaces are supplied explicitly because a
-- 'Body' is a function and does not enumerate its own states.
maxBisimulation ::
  (Eq s1, Eq s2, Eq b) =>
  [a] ->
  [s1] ->
  [s2] ->
  Body (,) s1 (->) a b ->
  Body (,) s2 (->) a b ->
  [(s1, s2)]
maxBisimulation inputs states1 states2 body1 body2 = go initRel
  where
    initRel = [(s1, s2) | s1 <- states1, s2 <- states2]
    go rel =
      let rel' =
            filter
              ( \(s1, s2) ->
                  all
                    ( \a ->
                        let (s1', b1) = stepBody body1 s1 a
                            (s2', b2) = stepBody body2 s2 a
                         in b1 == b2 && (s1', s2') `elem` rel
                    )
                    inputs
              )
              rel
       in if rel' == rel then rel else go rel'

-- | Check whether two specific states are bisimilar.
bisimilarStates ::
  (Eq s1, Eq s2, Eq b) =>
  [a] ->
  [s1] ->
  [s2] ->
  Body (,) s1 (->) a b ->
  Body (,) s2 (->) a b ->
  s1 ->
  s2 ->
  Bool
bisimilarStates inputs states1 states2 body1 body2 s1 s2 =
  (s1, s2) `elem` maxBisimulation inputs states1 states2 body1 body2

-- | 'Category' instance for 'Cell'.
--
-- The laws hold only up to invertible 'Sq': on-the-nose associativity and
-- unitality are impossible as Haskell values because the carriers of the two
-- sides differ.  Observational witnesses live in "Axioma.Cell".
instance (Strength t arr) => Category (Cell t arr) where
  id :: forall a. Cell t arr a a
  id = idCell
  {-# INLINE id #-}

  (.) :: forall a b c. Cell t arr b c -> Cell t arr a b -> Cell t arr a c
  (.) = cascade
  {-# INLINE (.) #-}

-- | Associator for 'Cell'.
--
-- The base associator acts on the payload while the hidden carrier is
-- threaded through unchanged.
instance (Strength t arr) => Assoc t (Cell t arr) where
  assoc = Cell (Body (strength assoc))
  assoc' = Cell (Body (strength assoc'))

-- | Slide for 'Cell'.
instance (Strength t arr) => Slide t (Cell t arr) where
  slide = Cell (Body (strength slide))

-- | Tensorial strength for 'Cell'.
--
-- The hidden carrier is slid past the extra scaffolding, the payload morphism
-- is strengthened in the base category, and the carrier is slid back.
instance (Strength t arr) => Strength t (Cell t arr) where
  strength (Cell (Body f)) = Cell (Body (slide .> strength f .> slide))

-- | The trace for 'Cell'.
--
-- 'feedback' is exactly 'yank' at the carrier-hidden layer: a feedback wire
-- @s@ threaded on both boundaries is moved into the existential carrier.
instance (Strength t arr) => Yank t (Cell t arr) where
  yank = feedback
