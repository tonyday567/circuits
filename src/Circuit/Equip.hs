{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The arrow-equipment surface: channel poles, squares, and boundary tokens.
--
-- In the proarrow-equipment reading of the library the tight arrows are the
-- base @arr@ morphisms and the loose arrows are 'Circuit.Body.Body' values
-- (a body @arr (t ch a) (t ch b)@ with its carrier @ch@ exposed).  This
-- module holds the equipment furniture:
--
-- * channel poles: 'Poles', the companion/conjoint pair of an identity
--   with an explicit carrier @ch@;
-- * squares: the indexed 2-cell 'Sq' and its existential closure 'TwoCell';
-- * boundary tokens: 'Boundary' (mark or payload) and 'Stamped'
--   (occurrence-stamped values).
--
-- The bicategory laws of the loose side hold only up to invertible 'Sq'
-- witnesses: carriers @ch ⊗ (ch' ⊗ ch'')@ and @(ch ⊗ ch') ⊗ ch''@ are
-- different Haskell types, so on-the-nose associativity is impossible.  The
-- proof artifact is the two-cell itself; the falsification artifact is
-- observational, via 'Circuit.Body.mergeChannel' and the
-- 'Circuit.Process.Process' runner.
module Circuit.Equip
  ( -- * Channel poles
    Poles (..),
    close,
    plug,

    -- * Payload-split poles
    plugSplit,
    closeSplit,

    -- * Carrier-split poles
    plugBridge,
    closeBridge,

    -- * Unit-pole convenience
    poles0,
    polesK,
    splay0,

    -- * Sequential composition
    compose,
    compose0,
    (>:>),

    -- * Parallel composition
    polesTensor,

    -- * Morphism-level mapping
    iomap,
    imap,
    omap,

    -- * Unit poles and copycat
    open,
    copycat,

    -- * Unit cells
    UnitCell (..),
    unitCell,
    pointedCell,

    -- * Boxes
    box,
    boxAsymmetric,

    -- * Additive connectives
    pair,
    race,

    -- * Companion / conjoint of a tight arrow
    companionTight,
    conjointTight,

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

    -- * Boundary tokens
    Boundary (..),
    isMark,
    isPayload,
    Stamped (..),
  )
where

import Circuit.Bimonoid (Copy (copy))
import Circuit.Body (Body (..), mergeChannel)
import Circuit.Category (Category (..), CoK (..), FunctionLike (..), K (..), Pointed (..), (.>))
import Circuit.Tensor (Bias (..), Tensor (..), Unit, Unital (..))
import Circuit.Tensor qualified as Tensor
import Circuit.Traced (Assoc (..), Strength (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Circuit.Body (Body (..))
-- >>> import Circuit.Category (CoK (..), K (..), runK, (.>))
-- >>> import Circuit.Equip
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Syntax (eval)
-- >>> import Circuit.Tensor (Bias (..))
-- >>> import Data.Functor.Identity (Identity (..))
-- >>> import Data.Maybe (isNothing)

-- * Channel poles — the companion and conjoint of the identity functor.

-- | A matched pair of channel poles with explicit carrier types.
--
-- @conjoint@ is the write leg: it consumes the input payload and produces
-- the write channel, in base @arrW@.  @companion@ is the read leg: it
-- consumes the read channel and produces the output payload, in base @arrR@.
-- The diagonal @arrW ~ arrR@ recovers single-base poles; split bases host a
-- co-Kleisli write leg against a Kleisli read leg (see 'closeSplit').
--
-- When @ch ~ ch'@ the two poles share a carrier; 'close' plugs them with the
-- identity.  When @ch /= ch'@, 'plug' inserts an explicit translation between
-- the write channel and the read channel.
data Poles ch ch' arrW arrR a b = Poles
  { -- | Write leg (conjoint), producing the write channel @ch@.
    conjoint :: arrW a ch,
    -- | Read leg (companion), consuming the read channel @ch'@.
    companion :: arrR ch' b
  }

-- | Generalised polar plug.
--
-- 'plug' inserts a translation @m :: arr ch ch'@ between the write leg and the
-- read leg of a single-base 'Poles', producing a morphism @arr a b@.
--
-- >>> let p = Poles (const ()) (const 42) :: Poles () () (->) (->) () Int
-- >>> plug id p ()
-- 42
plug :: (Category arr) => arr ch ch' -> Poles ch ch' arr arr a b -> arr a b
plug m p = conjoint p .> m .> companion p

-- | Close a self-channelled 'Poles' with the identity translation.
--
-- >>> let p = Poles (const ()) (const 42) :: Poles () () (->) (->) Int Int
-- >>> close p 0
-- 42
close :: (Category arr) => Poles ch ch arr arr a a -> arr a a
close = plug id

-- | Close a payload-split pole through a pure translation.
--
-- The write leg is co-Kleisli (@c a -> ch@), the read leg is Kleisli
-- (@ch' -> m b@), and the translation between the carriers is a plain
-- function — the neutral middle.  The result is the biKleisli arrow
-- @c a -> m b@: an Input comonad on the payload side, an Output monad on
-- the result side, factorised through an explicit carrier.
--
-- >>> let p = Poles (CoK runIdentity) (K (Identity . (+1))) :: Poles Int Int (CoK Identity) (K Identity) Int Int
-- >>> closeSplit p (Identity 5)
-- Identity 6
--
-- At the @(->)@-@(->)@ corner the split close agrees with 'close':
--
-- >>> let q = Poles id (+1) :: Poles Int Int (->) (->) Int Int
-- >>> close q 5
-- 6
plugSplit :: (ch -> ch') -> Poles ch ch' (CoK c) (K m) a b -> c a -> m b
plugSplit g p ca = runK (companion p) (g (runCoK (conjoint p) ca))

-- | Close a self-channelled payload-split pole with the identity
-- translation.
closeSplit :: Poles ch ch (CoK c) (K m) a b -> c a -> m b
closeSplit = plugSplit id

-- | Close a carrier-split pole through a bridge.
--
-- The write leg is Kleisli (@a -> m ch@), the read leg is co-Kleisli
-- (@c ch' -> b@), and closing demands a bridge @m ch -> c ch'@ between the
-- monad and the comonad.  Unlike 'plugSplit', the translation between the
-- carriers is not a plain function: the bridge subsumes it, and the bridge
-- is where any seed or choice the carrier needs must be supplied.
--
-- >>> let p = Poles (K (Identity . (+1))) (CoK runIdentity) :: Poles Int Int (K Identity) (CoK Identity) Int Int
-- >>> plugBridge id p 5
-- 6
plugBridge :: (m ch -> c ch') -> Poles ch ch' (K m) (CoK c) a b -> a -> b
plugBridge bridge p a = runCoK (companion p) (bridge (runK (conjoint p) a))

-- | 'plugBridge' at a self-channelled carrier.
closeBridge :: (m ch -> c ch) -> Poles ch ch (K m) (CoK c) a b -> a -> b
closeBridge bridge = plugBridge bridge

-- * Unit-pole convenience

-- | Build a unit-channel pole from a write morphism and a read morphism.
--
-- @poles0 write receive = Poles write receive :: Poles () () arr arr a b@.
poles0 ::
  forall arr a b.
  arr a () ->
  arr () b ->
  Poles () () arr arr a b
poles0 = Poles
{-# INLINE poles0 #-}

-- | Specialization of 'poles0' for @K@ actions.
--
-- @write :: a -> m ()@ consumes the input payload; @receive :: m b@ produces
-- the output payload.
polesK ::
  forall m a b.
  (a -> m ()) ->
  m b ->
  Poles () () (K m) (K m) a b
polesK write receive = Poles (K write) (K $ const receive)

-- | Extract the primitive write and read actions from a unit-channel pole.
--
-- >>> let p = Poles (const ()) (const 42) :: Poles () () (->) (->) () Int
-- >>> let (w, r) = splay0 p
-- >>> (w (), r ())
-- ((),42)
splay0 ::
  forall arr a b.
  Poles () () arr arr a b ->
  (arr a (), arr () b)
splay0 p = (conjoint p, companion p)

-- * Sequential composition

-- | Sequential composition of 'Poles'.
--
-- The read leg of the first pole is chained through the payload to the write
-- leg of the second pole.  The middle chain lives in one base @arrM@, so the
-- second pole is diagonal; the outer write base @arrW@ is free.  No channel
-- alignment is required for this sequential composition; alignment is only
-- needed when the composite is required to sit at a uniform carrier.
--
-- >>> let p1 = Poles (const ()) (const 1 :: () -> Int) :: Poles () () (->) (->) () Int
-- >>> let p2 = Poles (const ()) (const 2 :: () -> Int) :: Poles () () (->) (->) Int Int
-- >>> box (compose p1 p2) ()
-- 2
compose ::
  (Category arrM) =>
  Poles ch1 ch1' arrW arrM a b ->
  Poles ch1' ch1' arrM arrM b c ->
  Poles ch1 ch1' arrW arrM a c
compose p1 p2 =
  Poles
    (conjoint p1)
    (companion p1 .> conjoint p2 .> companion p2)

-- | Forward-composition operator.  @p1 >:> p2 = compose p1 p2@.
(>:>) ::
  (Category arrM) =>
  Poles ch1 ch1' arrW arrM a b ->
  Poles ch1' ch1' arrM arrM b c ->
  Poles ch1 ch1' arrW arrM a c
p1 >:> p2 = compose p1 p2

infixr 1 >:>

-- | Convenience synonym for 'compose' on unit-channel poles.
compose0 ::
  (Category arrM) =>
  Poles () () arrW arrM a b ->
  Poles () () arrM arrM b c ->
  Poles () () arrW arrM a c
compose0 = compose
{-# INLINE compose0 #-}

-- * Parallel composition

-- | Parallel composition of 'Poles' over a tensor @t@.
--
-- >>> let p1 = Poles (const ()) (const 1 :: () -> Int) :: Poles () () (->) (->) () Int
-- >>> let p2 = Poles (const ()) (const 2 :: () -> Int) :: Poles () () (->) (->) () Int
-- >>> plug id (polesTensor p1 p2) ((),())
-- (1,2)
polesTensor ::
  forall t arr ch1 ch1' ch2 ch2' a b c d.
  (Tensor t arr) =>
  Poles ch1 ch1' arr arr a b ->
  Poles ch2 ch2' arr arr c d ->
  Poles (t ch1 ch2) (t ch1' ch2') arr arr (t a c) (t b d)
polesTensor p1 p2 =
  Poles
    (Tensor.tensor (conjoint p1) (conjoint p2))
    (Tensor.tensor (companion p1) (companion p2))

-- * Morphism-level mapping

-- | Precompose the input and postcompose the output.
iomap ::
  forall arrW arrR a a' b b' ch ch'.
  (Category arrW, Category arrR) =>
  arrW a' a ->
  arrR b b' ->
  Poles ch ch' arrW arrR a b ->
  Poles ch ch' arrW arrR a' b'
iomap f g (Poles i o) = Poles (f .> i) (o .> g)

-- | Precompose the input.
imap ::
  forall arrW arrR a a' b ch ch'.
  (Category arrW) =>
  arrW a' a ->
  Poles ch ch' arrW arrR a b ->
  Poles ch ch' arrW arrR a' b
imap f (Poles i o) = Poles (f .> i) o

-- | Postcompose the output.
omap ::
  forall arrW arrR a b b' ch ch'.
  (Category arrR) =>
  arrR b b' ->
  Poles ch ch' arrW arrR a b ->
  Poles ch ch' arrW arrR a b'
omap g (Poles i o) = Poles i (o .> g)

-- * Unit poles and copycat

-- | Unit poles at the monoidal unit @()@.
--
-- The write leg discards its input; the read leg discards its channel.
-- Yanking recovers the identity on @()@.
--
-- >>> let p = open :: Poles () () (->) (->) () ()
-- >>> close p ()
-- ()
open :: (Category arr) => Poles () () arr arr () ()
open = Poles id id

-- | The copycat strategy at any carrier.
--
-- With identity legs, closing is the identity on the carrier.
--
-- >>> close (copycat :: Poles Bool Bool (->) (->) Bool Bool) True
-- True
copycat :: (Category arr) => Poles ch ch arr arr ch ch
copycat = Poles id id

-- * Unit cells

-- | A unit cell: an arrow out of the monoidal unit, @arr (Unit t) ch@.
--
-- Pointing is forced exactly where a carrier must be instantiated and no
-- input supplies it. There are three discharges, and this type is the
-- explicit one:
--
-- * input: the first payload seeds the carrier — 'Circuit.Process.asProcess'
--   removes the seed of a 'Circuit.Process.ProcessP';
-- * closure: the loop seeds itself — 'Circuit.Moore.machinePToMachine'
--   removes the carrier of a 'Circuit.Moore.MachineP' via
--   'Circuit.Trace.yank', and the seed is gone from the type;
-- * explicit: the seed is data, handed to runners such as
--   'Circuit.Process.runBodyCell' and 'Circuit.Process.asProcessPCell'.
--
-- The same pointing is independently present at each open post: the seed
-- argument of 'Circuit.Process.runBody', the initial state of a
-- 'Circuit.Moore.MachineP' run, the seed field of 'Circuit.Process.ProcessP',
-- the 'Circuit.Category.Pointed' class, the unit pole 'open'. 'Pointed' is
-- the EM side (an algebra of the @Maybe@ monad, structure on the object);
-- 'UnitCell' is the same pointing as a value.
--
-- Constraint map: a cell is required exactly where a carrier must be
-- instantiated and no input supplies it (Loregian: every missing colimit
-- in the process equipment is a carrier that would have to be pointed or
-- singleton). Open layers need one: body runners, machine runs,
-- 'ProcessP', 'Either'-carried unit loops. Closed layers need none, by
-- type: 'yank' folds (self-seeding at @(,)@, starting from the input at
-- 'Either'), flowchart runners, 'machinePToMachine'.
newtype UnitCell (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) ch = UnitCell
  { runUnitCell :: arr (Unit t) ch
  }

-- | Package an arrow out of the unit as a cell. For @(->)@ this is a seed
-- function @() -> ch@; for 'K' arrows, a carrier produced under the effect.
--
-- >>> runUnitCell (unitCell (const 3) :: UnitCell (,) (->) Int) ()
-- 3
unitCell :: arr (Unit t) ch -> UnitCell t arr ch
unitCell = UnitCell

-- | A 'Circuit.Category.Pointed' carrier has the canonical cell.
--
-- >>> runUnitCell (pointedCell :: UnitCell (,) (->) ()) ()
-- ()
pointedCell :: (Pointed ch) => UnitCell (,) (->) ch
pointedCell = UnitCell (\() -> point)

-- * Boxes

-- | Close a unit-channel 'Poles' to a plain morphism.
--
-- >>> let p = Poles (const ()) (const 42) :: Poles () () (->) (->) () Int
-- >>> box p ()
-- 42
box :: (Category arr) => Poles () () arr arr a b -> arr a b
box = plug id

-- | Asymmetric box with the channel exposed on opposite sides.
--
-- >>> let p = Poles (const ()) (const 42) :: Poles () () (->) (->) () Int
-- >>> boxAsymmetric p ((), ())
-- ((),42)
boxAsymmetric ::
  forall t arr ch ch' a b.
  (Tensor t arr) =>
  Poles ch ch' arr arr a b ->
  arr (t a ch') (t ch b)
boxAsymmetric p = Tensor.tensor (conjoint p) (companion p)

-- * Additive connectives

-- | Additive conjunction: both sub-poles receive the same input and their
-- outputs are paired.
--
-- >>> let p1 = Poles (const ()) (const 1 :: () -> Int) :: Poles () () (->) (->) () Int
-- >>> let p2 = Poles (const ()) (const 2 :: () -> Int) :: Poles () () (->) (->) () Int
-- >>> plug id (pair p1 p2) ()
-- (1,2)
pair ::
  forall arr ch1 ch1' ch2 ch2' a b c.
  (Tensor (,) arr, Copy arr a) =>
  Poles ch1 ch1' arr arr a b ->
  Poles ch2 ch2' arr arr a c ->
  Poles (ch1, ch2) (ch1', ch2') arr arr a (b, c)
pair p1 p2 =
  Poles
    (copy .> Tensor.tensor (conjoint p1) (conjoint p2))
    (Tensor.tensor (companion p1) (companion p2))

-- | Additive disjunction / race: both sub-poles receive the same input, but
-- only the first output satisfying the predicate is emitted.
--
-- The predicate selects "silent" values that should be skipped. The bias
-- chooses which side to prefer when both are non-silent. The picking logic is
-- lifted into the base arrow via 'FunctionLike'.
--
-- >>> let eL = Poles (const ()) (const (Just 1)) :: Poles () () (->) (->) () (Maybe Int)
-- >>> let eR = Poles (const ()) (const (Just 2)) :: Poles () () (->) (->) () (Maybe Int)
-- >>> plug id (race isNothing LeftFirst eL eR) ()
-- Just 1
-- >>> plug id (race isNothing RightFirst eL eR) ()
-- Just 2
race ::
  forall arr ch1 ch1' ch2 ch2' a b.
  (Tensor (,) arr, Copy arr a, FunctionLike arr) =>
  (b -> Bool) ->
  Bias ->
  Poles ch1 ch1' arr arr a b ->
  Poles ch2 ch2' arr arr a b ->
  Poles (ch1, ch2) (ch1', ch2') arr arr a b
race isSilent bias p1 p2 = omap (function (pick bias)) (pair p1 p2)
  where
    pick LeftFirst (x, y) = if isSilent x then y else x
    pick RightFirst (x, y) = if isSilent y then x else y

-- * Companion / conjoint of a tight arrow

-- | The companion of a tight arrow.
--
-- The companion of @f :: arr a b@ is the pole with identity write leg and
-- read leg @f@.
--
-- >>> box (companionTight (const 42 :: () -> Int)) ()
-- 42
companionTight :: (Category arr) => arr a b -> Poles a a arr arr a b
companionTight f = Poles id f

-- | The conjoint of a tight arrow.
--
-- The conjoint of @f :: arr a b@ is the pole with write leg @f@ and identity
-- read leg.
--
-- >>> box (conjointTight (const () :: Int -> ())) 7
-- ()
conjointTight :: (Category arr) => arr a b -> Poles b b arr arr a b
conjointTight f = Poles f id

-- * Squares

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
-- square.  This is the 'Sq' side of the interchange law; the 'Poles' side is
-- 'iomap' on the explicit-carrier representation.
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

-- | Occurrence-tokens for values.
--
-- A 'Stamped' value pairs an occurrence token (a /stamp/) with a payload.
-- The stamp is an observation receipt: an id, a timestamp, a line number,
-- or any other token that names the occurrence without changing the
-- payload's meaning.
--
-- === Free theorem
--
-- The stamp is untouched by payload mapping:
--
-- @
-- stamp (fmap f s) = stamp s
-- stamped (fmap f s) = f (stamped s)
-- @
--
-- >>> let s = Stamped 42 "hello"
-- >>> stamp (fmap reverse s)
-- 42
-- >>> stamped (fmap reverse s)
-- "olleh"
data Stamped r a = Stamped
  { -- | Occurrence token / receipt.  Not touched by 'fmap'.
    stamp :: r,
    -- | The labelled payload.
    stamped :: a
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Bifunctor Stamped where
  bimap f g (Stamped r a) = Stamped (f r) (g a)
