{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Traced-monoidal-category version of 'Circuit.Cell.Cell'.
--
-- Unlike 'Cell', which existentially hides the carrier at the type level,
-- 'TCell' keeps the 'Arr'/'Knot' distinction exposed.  A plain base arrow is
-- 'Arr'; a body with a hidden feedback carrier is 'Knot'.  This makes
-- 'TCell' a direct relative of the old @Arr@/@Knot@ 'Trace' normal form and
-- of the current 'TraceG' GADT.
--
-- 'TCell' is a traced monoidal category in its own right: it has 'Category',
-- 'Assoc', 'Slide', 'Strength', and 'Yank' instances without requiring the
-- base category to be traced.  The trace is structural: 'yank' on 'Arr'
-- wraps the body in 'Knot', and 'yank' on 'Knot' reassociates to move the
-- feedback wire into the carrier.
--
-- This is the profunctor-equipment 1-cell where the carrier is hidden only
-- when you choose to tie a 'Knot', not for every morphism by default.
module Circuit.TCell
  ( -- * Traced 1-cell
    TCell (..),

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

    -- * Structural proof witnesses (unitors and associator)
    unitorLeft,
    unitorRight,
    unitorLeftSq,
    unitorRightSq,
    associator,
    associatorSq,

    -- * Horizontal 2-cell algebra
    rightWhisker,
    leftWhisker,
    hcompose,
    whiskerSq,

    -- * Bridges to Cell and TraceG
    tcellToCell,
    cellToTCell,
    tcellToTraceG,
    traceGToTCell,
  )
where

import Circuit.Body (Body (..), mergeChannel)
import Circuit.Category (Category (..), (.>))
import Circuit.Cell (Cell (..))
import Circuit.Tensor (Tensor (..), Unit, Unital (..))
import Circuit.Trace (TraceG (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Prelude hiding (id, (.))

-- | Traced 1-cell: either a plain base arrow or a body with its carrier
-- hidden at the constructor.
data TCell t arr a b where
  -- | Plain base arrow, no hidden carrier.
  Arr :: arr a b -> TCell t arr a b
  -- | Body with hidden feedback carrier @ch@.
  Knot :: Body t ch arr a b -> TCell t arr a b

-- | Square (indexed 2-cell).  Composes vertically: the carrier maps compose;
-- the middle body must match (a caller side condition).
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
downThenAcross ::
  (Tensor t arr) =>
  Sq t arr ch ch' a b ->
  arr (t ch a) (t ch' b)
downThenAcross sq = tensor (carrierMap sq) id .> morphism (sqTgt sq)

-- | Go across (source body) then down (carrier map).
acrossThenDown ::
  (Tensor t arr) =>
  Sq t arr ch ch' a b ->
  arr (t ch a) (t ch' b)
acrossThenDown sq = morphism (sqSrc sq) .> tensor (carrierMap sq) id

-- | Indexed left unitor square.
unitorLeftSq ::
  (Unital t arr, Strength t arr) =>
  Body t ch arr a b ->
  Sq t arr (t (Unit t) ch) ch a b
unitorLeftSq b = Sq unitl (mergeChannel b (Body id)) b

-- | Left unitor witness.
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

-- | Associator witness.
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
-- square.
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

-- * Bridges

-- | Collapse a 'TCell' to a 'Cell'.  'Arr' becomes a body over the unit
-- carrier; 'Knot' is already a body.
tcellToCell ::
  (Strength t arr) =>
  TCell t arr a b ->
  Cell t arr a b
tcellToCell (Arr f) = Cell (Body (strength f))
tcellToCell (Knot b) = Cell b

-- | View a 'Cell' as a 'TCell'.  The existential body becomes a 'Knot'.
cellToTCell :: Cell t arr a b -> TCell t arr a b
cellToTCell (Cell b) = Knot b

-- | View a 'TCell' as a 'TraceG'.
tcellToTraceG :: TCell t arr a b -> TraceG t arr a b
tcellToTraceG (Arr f) = LiftG f
tcellToTraceG (Knot b) = KnotG (morphism b)

-- | Fold a 'TraceG' into a 'TCell'.
traceGToTCell ::
  (Strength t arr) =>
  TraceG t arr a b ->
  TCell t arr a b
traceGToTCell (LiftG f) = Arr f
traceGToTCell (ComposeG g f) = traceGToTCell g . traceGToTCell f
traceGToTCell (KnotG f) = Knot (Body f)

-- * Category instance

instance (Strength t arr) => Category (TCell t arr) where
  id :: forall a. TCell t arr a a
  id = Arr id
  {-# INLINE id #-}

  (.) :: forall a b c. TCell t arr b c -> TCell t arr a b -> TCell t arr a c
  Arr f . Arr g = Arr (f . g)
  Arr f . Knot g = Knot (Body (morphism g .> strength f))
  Knot f . Arr g = Knot (Body (strength g .> morphism f))
  Knot f . Knot g = Knot (mergeChannel f g)
  {-# INLINE (.) #-}

-- | Associator for 'TCell'.  Plain structural arrows are lifted directly.
instance (Assoc t arr, Strength t arr) => Assoc t (TCell t arr) where
  assoc = Arr assoc
  assoc' = Arr assoc'

-- | Slide for 'TCell'.
instance (Slide t arr, Strength t arr) => Slide t (TCell t arr) where
  slide = Arr slide

-- | Tensorial strength for 'TCell'.
--
-- * 'Arr' is strengthened in the base category and lifted.
-- * 'Knot' slides the extra scaffolding past the hidden carrier, strengthens
--   the body, and slides back.
instance (Strength t arr) => Strength t (TCell t arr) where
  strength (Arr f) = Arr (strength f)
  strength (Knot (Body f)) = Knot (Body (slide .> strength f .> slide))

-- | The trace for 'TCell'.
--
-- * 'Arr' becomes a single-knot body.
-- * 'Knot' reassociates to move the feedback wire into the carrier.
instance (Strength t arr) => Yank t (TCell t arr) where
  yank (Arr f) = Knot (Body f)
  yank (Knot (Body f)) = Knot (Body (assoc .> f .> assoc'))
