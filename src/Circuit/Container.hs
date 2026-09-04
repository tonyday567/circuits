{-# LANGUAGE TypeFamilies #-}

-- | The container view of polynomials: @Eval p x@ as a position with
-- the pins of /that/ position assigned.
--
-- @
--   Eval p x  ≅  Σ (i :: PosAt p b). (DirAt p b -> x)
-- @
--
-- The library already carries two grades of the same polynomial shape.
-- The /flat/ grade ('Pos', 'Dir') types the direction set without
-- reference to the position; it is right for dynamics, where the
-- environment supplies a direction after the position is observed, so
-- an off-fibre direction never occurs at run time.  The /fibred/
-- grade (this module) types pins at one position; it is right for
-- read-back and routing, where something must recover the position or
-- type a pin without having been at the step that produced it.
--
-- The wall between the grades is 'Sum': a flat direction
-- @Either (Dir p) (Dir q)@ cannot be narrowed to the branch the
-- position selected, which is why 'Netlist' has no @Sum@ instance and
-- 'Chs' is write-only.  The fibre depends on the position only
-- through its 'Sum'-branch choices — the constructor, never the
-- payload — so a position splits into a promotable skeleton
-- ('Branch') and a term-level payload ('PosK' carries it).  'DirAt'
-- is then an ordinary closed family over the skeleton, and 'Sum'
-- composes freely.
--
-- The same absence is relocated, not removed: 'FlatFibre' is total
-- everywhere /except/ 'Sum', where it honestly cannot be.  Where the
-- missing @Netlist (Sum p q)@ instance blocked the netlist view, the
-- missing @FlatFibre (Sum p q)@ instance states a true fact about the
-- flat grade and blocks nothing that 'fromFlat' does not already
-- express.
--
-- /Second wall:/ @'Comp'@ does not admit a 'DirAt' equation at all —
-- its inner skeleton is determined by a /runtime/ direction, a
-- genuine term-to-type dependency that Haskell cannot express.
-- 'compToNested' is the escape hatch: @Eval p (Eval q x)@ is
-- fibre-honest at both levels by construction.  This module
-- deliberately has no @'Comp'@ cases.
--
-- /Naming:/ the existential container is 'Fibred', not @Sig@ — the
-- latter collides with 'Circuit.Syntax.Sig' in the "Circuit" umbrella.
--
-- 'PosAt' deliberately has no @Eq@/@Show@: bundling dictionaries into
-- 'PosK' is evidence-bundling, and the structural skeleton is what
-- equality is anyway.  Compare positions via 'Skel' (the term-level
-- mirror of 'Branch') and 'posOf'.
--
-- Worked examples: $fibred-view.
module Circuit.Container
  ( -- * Branch skeleton
    Branch (..),
    Skel (..),

    -- * Positions, split
    PosAt (..),
    SomePos (..),
    posOf,
    skelOf,

    -- * Pins at a position
    DirAt,
    toFlat,
    fromFlat,
    FlatFibre (..),

    -- * The container view
    Fibred (..),
    Located (..),
    Container (..),
    monoFibreFlat,
  )
where

import Circuit.Category ((.), id)
import Circuit.Poly (Dir, Eval (..), Mono, Poly (..), Pos)
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Container
-- >>> import Circuit.Poly
-- >>> import Prelude hiding (id, (.))

-- | Branch skeleton: the payload-free part of a position.  Only the
-- 'Sum' constructor choices matter to the fibre, so only they — and
-- the structural spine — appear here.
data Branch
  = BY
  | BK
  | BE
  | BL Branch
  | BR Branch
  | BP Branch Branch
  | BT Branch Branch

-- | The term-level mirror of 'Branch', with derived 'Eq'/'Show'.
-- This is the comparison vehicle for positions: 'skelOf' recovers
-- the skeleton, 'posOf' the payload.
data Skel
  = SY
  | SK
  | SE
  | SL Skel
  | SR Skel
  | SP Skel Skel
  | ST Skel Skel
  deriving (Eq, Show)

-- | A position, split: skeleton in the type index, payload in the
-- term.
--
-- 'PosK' is where the payload lives — a 'Const' position (the @o@ in
-- @Mono i o@) is a genuine runtime value and never enters the fibre,
-- so it stays out of the index.
data PosAt :: Poly -> Branch -> Type where
  PosY :: PosAt 'Y 'BY
  PosK :: c -> PosAt ('Const c) 'BK
  PosE :: PosAt ('Exp a) 'BE
  PosL :: PosAt p b -> PosAt (Sum p q) ('BL b)
  PosR :: PosAt q b -> PosAt (Sum p q) ('BR b)
  PosP :: PosAt p b -> PosAt q c -> PosAt (Prod p q) ('BP b c)
  PosT :: PosAt p b -> PosAt q c -> PosAt (PTensor p q) ('BT b c)

-- | Forget the skeleton: project a split position to the flat 'Pos'.
--
-- >>> let i = PosL (PosK (3 :: Int)) :: PosAt (Sum (Const Int) Y) ('BL 'BK)
-- >>> posOf i
-- Left 3
posOf :: PosAt p b -> Pos p
posOf = \case
  PosY -> ()
  PosK c -> c
  PosE -> ()
  PosL i -> Left (posOf i)
  PosR j -> Right (posOf j)
  PosP i j -> (posOf i, posOf j)
  PosT i j -> (posOf i, posOf j)

-- | The skeleton of a position, as a comparable term.
skelOf :: PosAt p b -> Skel
skelOf = \case
  PosY -> SY
  PosK _ -> SK
  PosE -> SE
  PosL i -> SL (skelOf i)
  PosR j -> SR (skelOf j)
  PosP i j -> SP (skelOf i) (skelOf j)
  PosT i j -> ST (skelOf i) (skelOf j)

-- | A position with its skeleton hidden existentially — the type of
-- "a position, recovered".
data SomePos :: Poly -> Type where
  SomePos :: PosAt p b -> SomePos p

-- | Pins at a position.  Depends on the skeleton only: the two 'Sum'
-- equations are the wall, dissolved.
--
-- For @'Prod'@ the fibre is the coproduct of the sub-fibres — it
-- composes freely in both 'toFibred' and 'fromFibred'.  For
-- @'PTensor'@ the fibre is the /product/, and the flat function an
-- 'ET' value stores must be narrowed ('FlatFibre') to meet it; see
-- the 'Container' instance.
type family DirAt (p :: Poly) (b :: Branch) :: Type where
  DirAt 'Y 'BY = ()
  DirAt ('Const c) 'BK = Void
  DirAt ('Exp a) 'BE = a
  DirAt (Sum p q) ('BL b) = DirAt p b
  DirAt (Sum p q) ('BR b) = DirAt q b
  DirAt (Prod p q) ('BP b c) = Either (DirAt p b) (DirAt q c)
  DirAt (PTensor p q) ('BT b c) = (DirAt p b, DirAt q c)

-- | Widen a pin to the flat 'Dir' of the whole polynomial.  Total at
-- every position.
toFlat :: PosAt p b -> DirAt p b -> Dir p
toFlat = \case
  PosY -> \() -> ()
  PosK _ -> absurd
  PosE -> id
  PosL i -> \d -> Left (toFlat i d)
  PosR j -> \d -> Right (toFlat j d)
  PosP i j -> either (Left . toFlat i) (Right . toFlat j)
  PosT i j -> \(d1, d2) -> (toFlat i d1, toFlat j d2)

-- | Narrow a flat direction to the pins of one position.  Total
-- exactly off 'Sum'; on a wrong branch there is no pin to return,
-- which is the wall restated positively.
--
-- >>> let i = PosL (PosK (3 :: Int)) :: PosAt (Sum (Const Int) Y) ('BL 'BK)
-- >>> fromFlat i (Right ())
-- Nothing
-- >>> let m = PosP (PosK (5 :: Int)) PosE :: PosAt (Mono Int Int) ('BP 'BK 'BE)
-- >>> fromFlat m (toFlat m (Right 7))
-- Just (Right 7)
fromFlat :: PosAt p b -> Dir p -> Maybe (DirAt p b)
fromFlat = \case
  PosY -> \() -> Just ()
  PosK _ -> absurd
  PosE -> \d -> Just d
  PosL i -> \case
    Left d -> fromFlat i d
    Right _ -> Nothing
  PosR j -> \case
    Left _ -> Nothing
    Right d -> fromFlat j d
  PosP i j -> either (fmap Left . fromFlat i) (fmap Right . fromFlat j)
  PosT i j -> \(d1, d2) -> (,) <$> fromFlat i d1 <*> fromFlat j d2

-- | The flat direction is total exactly off 'Sum'.  Every structural
-- constructor except 'Sum' (and @'Comp'@, which has no 'DirAt' at
-- all) has an instance; the missing @Sum@ instance is the relocated
-- wall — a true fact about the flat grade, not an obstruction.
class FlatFibre (p :: Poly) where
  -- | Narrow a flat direction to the pins, totality witnessed by the
  -- instance itself.
  narrow :: PosAt p b -> Dir p -> DirAt p b

instance FlatFibre 'Y where
  narrow PosY () = ()

instance FlatFibre ('Const c) where
  narrow _ = absurd

instance FlatFibre ('Exp a) where
  narrow PosE d = d

instance (FlatFibre p, FlatFibre q) => FlatFibre (Prod p q) where
  narrow (PosP i j) = either (Left . narrow i) (Right . narrow j)

instance (FlatFibre p, FlatFibre q) => FlatFibre (PTensor p q) where
  narrow (PosT i j) (d1, d2) = (narrow i d1, narrow j d2)

-- | The Σ: a position with the pins of /that/ position assigned.
-- Matching on the 'PosAt' refines the skeleton index @b@, so the pin
-- map is already typed at the fibre.
--
-- >>> let v = ES (Left (EK (3 :: Int))) :: Eval (Sum (Const Int) Y) Bool
-- >>> case toFibred v of Fibred j _ -> posOf j
-- Left 3
-- >>> case fromFibred (toFibred v) of ES (Left (EK c)) -> c; _ -> 0
-- 3
data Fibred :: Poly -> Type -> Type where
  Fibred :: PosAt p b -> (DirAt p b -> x) -> Fibred p x

-- | Recover a split position from a flat one.  Total at every
-- structural constructor /including/ 'Sum' — unlike 'FlatFibre', the
-- position is in hand, so the branch is known.
class Located (p :: Poly) where
  posAt :: Pos p -> SomePos p

instance Located 'Y where
  posAt () = SomePos PosY

instance Located ('Const c) where
  posAt = SomePos . PosK

instance Located ('Exp a) where
  posAt () = SomePos PosE

instance (Located p, Located q) => Located (Sum p q) where
  posAt = \case
    Left i -> case posAt i of SomePos pi -> SomePos (PosL pi)
    Right j -> case posAt j of SomePos pj -> SomePos (PosR pj)

instance (Located p, Located q) => Located (Prod p q) where
  posAt (i, j) = case (posAt i, posAt j) of
    (SomePos pi, SomePos pj) -> SomePos (PosP pi pj)

instance (Located p, Located q) => Located (PTensor p q) where
  posAt (i, j) = case (posAt i, posAt j) of
    (SomePos pi, SomePos pj) -> SomePos (PosT pi pj)

-- | The container isomorphism: 'Eval' values are positions with pin
-- assignments.  Instances exist at every structural constructor
-- including 'Sum' — the round trip 'netRoundTrip' cannot express.
--
-- The @'PTensor'@ instance additionally demands 'FlatFibre' on both
-- factors: an 'ET' value stores a flat function, and meeting the
-- product fibre requires narrowing that is total only off 'Sum'.
class Container (p :: Poly) where
  toFibred :: Eval p x -> Fibred p x
  fromFibred :: Fibred p x -> Eval p x

instance Container 'Y where
  toFibred (EY x) = Fibred PosY (\() -> x)
  fromFibred (Fibred PosY k) = EY (k ())

instance Container ('Const c) where
  toFibred (EK c) = Fibred (PosK c) absurd
  fromFibred (Fibred (PosK c) _) = EK c

instance Container ('Exp a) where
  toFibred (EE f) = Fibred PosE f
  fromFibred (Fibred PosE k) = EE k

instance (Container p, Container q) => Container (Sum p q) where
  toFibred (ES e) = case e of
    Left u -> case toFibred u of Fibred i k -> Fibred (PosL i) k
    Right v -> case toFibred v of Fibred j k -> Fibred (PosR j) k
  fromFibred (Fibred i k) = case i of
    PosL i' -> ES (Left (fromFibred (Fibred i' k)))
    PosR j' -> ES (Right (fromFibred (Fibred j' k)))

instance (Container p, Container q) => Container (Prod p q) where
  toFibred (EP (u, v)) = case (toFibred u, toFibred v) of
    (Fibred i f, Fibred j g) -> Fibred (PosP i j) (either f g)
  fromFibred (Fibred (PosP i j) k) =
    EP (fromFibred (Fibred i (k . Left)), fromFibred (Fibred j (k . Right)))

instance
  (Located p, Located q, FlatFibre p, FlatFibre q) =>
  Container (PTensor p q)
  where
  toFibred (ET (i, j) f) = case (posAt i, posAt j) of
    (SomePos pi, SomePos pj) -> Fibred (PosT pi pj) (\(dp, dq) -> f (toFlat pi dp, toFlat pj dq))
  fromFibred (Fibred (PosT i j) k) =
    ET (posOf i, posOf j) (\(d1, d2) -> k (narrow i d1, narrow j d2))

-- | The two grades agree definitionally on the monomial fragment: the
-- fibre of @Mono i o@ is the flat direction, on the nose.  Accepted
-- by the compiler alone — if the 'DirAt' equations above have a typo,
-- this witness stops compiling.
monoFibreFlat :: DirAt (Mono Int Int) ('BP 'BK 'BE) :~: Dir (Mono Int Int)
monoFibreFlat = Refl

-- $fibred-view
--
-- The wall, in one session:
--
-- >>> let v = ES (Right (EY True)) :: Eval (Sum (Const Int) Y) Bool
-- >>> case toFibred v of Fibred (PosR PosY) k -> (Right (), k ())
-- (Right (),True)
--
-- A 'Sum' value on the /right/ branch yields a position whose pins
-- are the /right/ factor's — the thing 'Netlist' cannot say.
