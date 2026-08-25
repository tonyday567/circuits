{-# LANGUAGE GADTs #-}

-- | Loose bicategory of 'Circuit.Body.Body' values with varying carriers.
--
-- A KSW loose 1-cell is a body @arr (t ch a) (t ch b)@ with its carrier @ch@
-- hidden.  The 2-cells are carrier intertwiners: maps @α : ch -> ch'@ that make
-- the Mealy square commute.  'Body' is the fibre at fixed carrier; 'Circ' is
-- the coproduct of those fibres, and 'Sq' / 'Intertwiner' move between them.
--
-- == Carrier-tensoring composition
--
-- @cascade@ composes two bodies whose carriers are tensored:
--
-- @
--   f :: Body t ch  arr a b
--   g :: Body t ch' arr b c
--   cascade g f :: Circ t arr a c   -- carrier  t ch ch'
-- @
--
-- The composite is
--
-- @
--   assoc .> slide .> strength f .> slide .> strength g .> assoc'
-- @
--
-- using 'Circuit.Channel.assoc', 'assoc'', 'slide' and 'strength'.  No
-- braiding/'Action' is needed because 'slide' already swaps the second carrier
-- past the payload.
--
-- == Law witnesses
--
-- The bicategory laws are existence statements: carriers @ch ⊗ (ch' ⊗ ch'')@
-- and @(ch ⊗ ch') ⊗ ch''@ are different Haskell types, so associativity holds
-- only up to an invertible 'Sq'.  Tests must exhibit the intertwiner.
module Circuit.Circ
  ( -- * Loose 1-cell (carrier hidden)
    Circ (..),

    -- * Indexed 2-cell (carrier map + commuting square)
    Sq (..),

    -- * Existential closure of Sq
    Intertwiner (..),

    -- * The two paths whose equality is the square
    downThenAcross,
    acrossThenDown,

    -- * Carrier-tensoring composition
    cascade,
  )
where

import Circuit.Body (Body (..))
import Circuit.Category (Category (..), (.>))
import Circuit.Channel (Channel (..), Strength (..))
import Circuit.Tensor (Tensor (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Circuit.Circ
-- >>> import Circuit.Body (Body (..))

-- | Loose 1-cell: a body with its carrier type hidden.
data Circ t arr a b where
  Circ :: Body t ch arr a b -> Circ t arr a b

-- | Square (indexed 2-cell).  Composes vertically: the carrier maps compose,
-- and the middle body must match (a caller side condition).
data Sq t arr ch ch' a b = Sq
  { -- | Map between carriers.
    carrierMap :: arr ch ch',
    -- | Source body, over the source carrier.
    sqSrc :: Body t ch arr a b,
    -- | Target body, over the target carrier.
    sqTgt :: Body t ch' arr a b
  }

-- | Existential closure of 'Sq', for stating "there exists a 2-cell".
data Intertwiner t arr a b where
  Intertwiner :: Sq t arr ch ch' a b -> Intertwiner t arr a b

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

-- $counter-to-parity
--
-- A nondegenerate intertwiner witness: counter state quotiented by parity.
--
-- >>> let counter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', odd n')) :: Body (,) Int (->) Bool Bool
-- >>> let parity = (Body $ \(b, r) -> let b' = if r then False else not b in (b', b')) :: Body (,) Bool (->) Bool Bool
-- >>> let sq = Sq odd counter parity :: Sq (,) (->) Int Bool Bool Bool
-- >>> downThenAcross sq (5, False)
-- (False,False)
-- >>> acrossThenDown sq (5, False)
-- (False,False)
-- >>> downThenAcross sq (5, True)
-- (False,False)
-- >>> acrossThenDown sq (5, True)
-- (False,False)

-- | Carrier-tensoring composition of loose 1-cells.
--
-- The composite has carrier @t ch ch'@ when the first body has carrier @ch@
-- and the second has carrier @ch'@.
cascade ::
  (Strength t arr) =>
  Circ t arr b c ->
  Circ t arr a b ->
  Circ t arr a c
cascade (Circ g) (Circ f) =
  Circ $
    Body
      ( assoc
          .> slide
          .> strength (morphism f)
          .> slide
          .> strength (morphism g)
          .> assoc'
      )

-- | Identity loose 1-cell at the tensor unit carrier.
instance (Strength t arr) => Category (Circ t arr) where
  id :: forall a. Circ t arr a a
  id = Circ (Body id)
  {-# INLINE id #-}

  (.) :: forall a b c. Circ t arr b c -> Circ t arr a b -> Circ t arr a c
  (.) = cascade
  {-# INLINE (.) #-}
