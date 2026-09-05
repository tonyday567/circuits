{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Finite relations, in two reference-semantics grades.
--
-- * 'Rel': explicit finite relations. Any type equipped with a 'Fin'
--   listing of inhabitants can serve as an object; morphisms are lists of
--   pairs. Composition requires 'Eq' on the middle type, so this grade is
--   intentionally not an instance of the unconstrained
--   'Circuit.Category.Category' tower: the monoidal unitors and
--   associators need explicit 'Fin' evidence. Use the named combinators
--   directly when working with finite relations.
-- * 'FinRel': finite-dimensional linear relations over GF(2), for boolean
--   signal-flow graphs. Objects are natural numbers (encoded as 'FinObj'),
--   morphisms are GF(2)-linear relations presented as the row space of a
--   matrix with @(n+m)@ columns. Values are 'Bool', addition is 'xor',
--   multiplication is '&&'. The category carries the cartesian monoidal
--   structure @(,)@, is traced, and supports the copy/discard/plus/zero
--   generators that 'Circuit.Net' uses for wiring.
--
-- Both grades are intentionally small and self-contained: they are the
-- minimal reference semantics needed to decide equality of wiring
-- diagrams, over an arbitrary finite listing or over a two-element field.
module Circuit.Rel
  ( -- * Explicit finite relations: objects
    Fin (..),

    -- * Explicit finite relations: morphisms
    Rel (..),

    -- * Explicit finite relations: category structure
    relId,
    relComp,

    -- * Explicit finite relations: monoidal structure
    relPar,
    relSwap,
    relAssoc,
    relAssoc',
    relUnitl,
    relUnitl',
    relUnitr,
    relUnitr',

    -- * Explicit finite relations: bimonoid generators (require explicit finite set)
    relCopy,
    relDiscard,
    relPlus,
    relZero,

    -- * Explicit finite relations: convenience
    Finite (..),

    -- * GF(2) linear relations: objects
    FinObj (..),
    KnownDim (..),

    -- * GF(2) linear relations: morphisms
    FinRel (..),

    -- * GF(2) linear relations: smart constructors
    finId,
    compFinRel,
    parFinRel,
    traceFinRel,
    finScalar,
    wiring,
  )
where

import Circuit.Bimonoid (Copy (..), Discard (..), Merge (..), Zero (..))
import Circuit.Category (Category (..))
import Data.Kind (Type)
import Data.List (findIndex, transpose)
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat, Nat, natVal)
import Prelude hiding (id, (.))

-- * Explicit finite relations

-- | Explicit finite set of values.
newtype Fin a = Fin {inhabitants :: [a]}

-- | A relation from @a@ to @b@, represented as a list of pairs.
newtype Rel a b = Rel {pairs :: [(a, b)]}
  deriving (Eq, Show)

-- | Identity relation on a finite set.
relId :: Fin a -> Rel a a
relId (Fin as) = Rel [(a, a) | a <- as]

-- | Relational composition: @R ; S@ contains @(a, c)@ whenever there exists a
-- @b@ with @(a, b) ∈ R@ and @(b, c) ∈ S@.
relComp :: (Eq b) => Rel b c -> Rel a b -> Rel a c
relComp (Rel r2) (Rel r1) =
  Rel [(a, c) | (a, b1) <- r1, (b2, c) <- r2, b1 == b2]

-- | Parallel (monoidal) product of relations.
relPar :: Rel a b -> Rel c d -> Rel (a, c) (b, d)
relPar (Rel r1) (Rel r2) =
  Rel [((a, c), (b, d)) | (a, b) <- r1, (c, d) <- r2]

-- | Swap the two components of a product.
relSwap :: Fin a -> Fin b -> Rel (a, b) (b, a)
relSwap (Fin as) (Fin bs) =
  Rel [((a, b), (b, a)) | a <- as, b <- bs]

-- | Associator @((a, b), c) -> (a, (b, c))@.
relAssoc :: Fin a -> Fin b -> Fin c -> Rel ((a, b), c) (a, (b, c))
relAssoc (Fin as) (Fin bs) (Fin cs) =
  Rel [(((a, b), c), (a, (b, c))) | a <- as, b <- bs, c <- cs]

-- | Inverse associator @(a, (b, c)) -> ((a, b), c)@.
relAssoc' :: Fin a -> Fin b -> Fin c -> Rel (a, (b, c)) ((a, b), c)
relAssoc' (Fin as) (Fin bs) (Fin cs) =
  Rel [((a, (b, c)), ((a, b), c)) | a <- as, b <- bs, c <- cs]

-- | Left unitor @((), a) -> a@.
relUnitl :: Fin a -> Rel ((), a) a
relUnitl (Fin as) = Rel [(((), a), a) | a <- as]

-- | Inverse left unitor @a -> ((), a)@.
relUnitl' :: Fin a -> Rel a ((), a)
relUnitl' (Fin as) = Rel [(a, ((), a)) | a <- as]

-- | Right unitor @(a, ()) -> a@.
relUnitr :: Fin a -> Rel (a, ()) a
relUnitr (Fin as) = Rel [((a, ()), a) | a <- as]

-- | Inverse right unitor @a -> (a, ())@.
relUnitr' :: Fin a -> Rel a (a, ())
relUnitr' (Fin as) = Rel [(a, (a, ())) | a <- as]

-- | Copy relation: @a ↦ (a, a)@.
relCopy :: Fin a -> Rel a (a, a)
relCopy (Fin as) = Rel [(a, (a, a)) | a <- as]

-- | Discard relation: @a ↦ ()@ for every inhabitant.
relDiscard :: Fin a -> Rel a ()
relDiscard (Fin as) = Rel [(a, ()) | a <- as]

-- | Merge relation for a finite magma: @((x, y), x `add` y)@ when the result
-- is an inhabitant of the finite set.
relPlus :: (Eq a) => Fin a -> (a -> a -> a) -> Rel (a, a) a
relPlus (Fin as) add =
  Rel [((x, y), z) | x <- as, y <- as, let z = add x y, z `elem` as]

-- | Point relation: the unit for 'relPlus' at a chosen element.
relZero :: a -> Rel () a
relZero a = Rel [((), a)]

-- | Types with a canonical finite enumeration.
class Finite a where
  finite :: Fin a

instance Finite () where
  finite = Fin [()]

instance Finite Bool where
  finite = Fin [False, True]

instance (Finite a, Finite b) => Finite (a, b) where
  finite = Fin [(a, b) | a <- inhabitants finite, b <- inhabitants finite]

-- * GF(2) linear relations

-- * GF(2) arithmetic

-- | Addition in GF(2) is exclusive-or.
gf2add :: Bool -> Bool -> Bool
gf2add = (/=)

-- | Multiplication in GF(2) is conjunction.
gf2mul :: Bool -> Bool -> Bool
gf2mul = (&&)

-- | Additive unit of GF(2).
gf2zero :: Bool
gf2zero = False

-- | Multiplicative unit of GF(2).
gf2one :: Bool
gf2one = True

-- | Additive inverse in GF(2) is the identity.
gf2neg :: Bool -> Bool
gf2neg = id

-- | Multiplicative inverse in GF(2) is the identity.
gf2inv :: Bool -> Bool
gf2inv = id

-- * Objects

-- | Object token for a finite-dimensional space of dimension @n@.
data FinObj (n :: Nat) = FinObj
  deriving (Eq, Ord, Show)

-- | Dimension evidence for objects closed under the @(,)@ tensor.
--
-- @()@ has dimension 0, 'FinObj n' has dimension @n@, and pairs add.
class KnownDim a where
  dimVal :: Proxy a -> Int

instance KnownDim () where
  dimVal _ = 0

instance (KnownNat n) => KnownDim (FinObj n) where
  dimVal _ = fromIntegral (natVal (Proxy @n))

instance (KnownDim a, KnownDim b) => KnownDim (a, b) where
  dimVal _ = dimVal (Proxy @a) + dimVal (Proxy @b)

-- * Morphisms

-- | A GF(2)-linear relation @n -> m@.
--
-- Internally a matrix whose rows span the relation:
--
-- @
--   { (take n v, drop n v) | v in row space }
-- @
--
-- The stored dimensions are trusted; the matrix is kept in reduced row
-- echelon form for canonical equality.
data FinRel (n :: Type) (m :: Type) = FinRel
  { finInDim :: !Int,
    finOutDim :: !Int,
    finMat :: ![[Bool]]
  }
  deriving (Show)

instance Eq (FinRel n m) where
  FinRel _ _ m1 == FinRel _ _ m2 = rref m1 == rref m2

-- * Matrix primitives over GF(2)

zeros :: Int -> [Bool]
zeros n = replicate n gf2zero

vscale :: Bool -> [Bool] -> [Bool]
vscale c = map (gf2mul c)

vdot :: [Bool] -> [Bool] -> Bool
vdot xs ys = foldr gf2add gf2zero (zipWith gf2mul xs ys)

-- | Matrix (rows) times vector.
mxv :: [[Bool]] -> [Bool] -> [Bool]
mxv m v = map (vdot v) m

setAt :: Int -> a -> [a] -> [a]
setAt i x xs = take i xs ++ [x] ++ drop (i + 1) xs

swapRows :: Int -> Int -> [a] -> [a]
swapRows i j xs
  | i == j = xs
  | otherwise = setAt i (xs !! j) (setAt j (xs !! i) xs)

-- | Reduced row echelon form over GF(2).  Zero rows are removed.
rref :: [[Bool]] -> [[Bool]]
rref rows = filter (any (/= gf2zero)) (go rows 0 0)
  where
    go m r c
      | r >= length m || c >= width m = m
      | otherwise =
          case findPivot m r c of
            Nothing -> go m r (c + 1)
            Just pr ->
              let m' = swapRows r pr m
                  pivotRow = m' !! r
                  pivotVal = pivotRow !! c
                  m'' = setAt r (vscale (gf2inv pivotVal) pivotRow) m'
                  m''' = eliminate c r m''
               in go m''' (r + 1) (c + 1)

    width m = maybe 0 length (listToMaybe m)

    findPivot m r c =
      fmap (+ r) (findIndex ((/= gf2zero) . (!! c)) (drop r m))

    eliminate c r m =
      [ if i == r
          then row
          else
            let factor = row !! c
             in zipWith (\x y -> gf2add x (gf2mul factor y)) row (m !! r)
      | (i, row) <- zip [0 ..] m
      ]

-- | Basis for the nullspace of a matrix with the given column width.
--
-- The matrix may have zero rows; in that case the nullspace is the whole
-- space of the given dimension.
nullspace :: Int -> [[Bool]] -> [[Bool]]
nullspace width rows =
  let rrefm = rref rows
      pivots = mapMaybe (listToMaybe . map fst . filter ((/= gf2zero) . snd) . zip [0 ..]) rrefm
      freeCols = filter (`notElem` pivots) [0 .. width - 1]
      basis =
        [ let vec = [if c == f then gf2one else gf2zero | c <- [0 .. width - 1]]
              pivotVals = [gf2neg (row !! f) | row <- rrefm]
              vec' = foldl' (\v (pc, val) -> setAt pc val v) vec (zip pivots pivotVals)
           in vec'
        | f <- freeCols
        ]
   in basis

-- * Wiring and generators

-- | Build a wiring isomorphism from explicit dimensions and a permutation.
mkWiring ::
  Int ->
  Int ->
  (Int -> Int) ->
  FinRel a b
mkWiring dIn dOut perm =
  let rows =
        [ [ if j == i || j == dIn + perm i
              then gf2one
              else gf2zero
          | j <- [0 .. dIn + dOut - 1]
          ]
        | i <- [0 .. dIn - 1]
        ]
   in FinRel dIn dOut (rref rows)

-- | Build a wiring isomorphism from a permutation.
wiring ::
  forall a b.
  (KnownDim a, KnownDim b) =>
  (Int -> Int) ->
  FinRel a b
wiring = mkWiring (dimVal (Proxy @a)) (dimVal (Proxy @b))

finId ::
  forall a.
  (KnownDim a) =>
  FinRel a a
finId =
  let n = dimVal (Proxy @a)
      rows =
        [ [if j == i || j == n + i then gf2one else gf2zero | j <- [0 .. 2 * n - 1]]
        | i <- [0 .. n - 1]
        ]
   in FinRel n n (rref rows)

finCopy ::
  forall n.
  (KnownNat n) =>
  FinRel (FinObj n) (FinObj n, FinObj n)
finCopy =
  let n = fromIntegral (natVal (Proxy @n))
      rows =
        [ [ if j == i || j == n + i || j == 2 * n + i
              then gf2one
              else gf2zero
          | j <- [0 .. 3 * n - 1]
          ]
        | i <- [0 .. n - 1]
        ]
   in FinRel n (2 * n) (rref rows)

finDiscard ::
  forall n.
  (KnownNat n) =>
  FinRel (FinObj n) ()
finDiscard =
  let n = fromIntegral (natVal (Proxy @n))
      rows = [[if j == i then gf2one else gf2zero | j <- [0 .. n - 1]] | i <- [0 .. n - 1]]
   in FinRel n 0 (rref rows)

finPlus ::
  forall n.
  (KnownNat n) =>
  FinRel (FinObj n, FinObj n) (FinObj n)
finPlus =
  let n = fromIntegral (natVal (Proxy @n))
      rows =
        concatMap
          ( \i ->
              [ [if j == i || j == 2 * n + i then gf2one else gf2zero | j <- [0 .. 3 * n - 1]],
                [if j == n + i || j == 2 * n + i then gf2one else gf2zero | j <- [0 .. 3 * n - 1]]
              ]
          )
          [0 .. n - 1]
   in FinRel (2 * n) n (rref rows)

finZero ::
  forall n.
  (KnownNat n) =>
  FinRel () (FinObj n)
finZero =
  let n = fromIntegral (natVal (Proxy @n))
   in FinRel 0 n []

finScalar ::
  forall n.
  (KnownNat n) =>
  Bool ->
  FinRel (FinObj n) (FinObj n)
finScalar c =
  let n = fromIntegral (natVal (Proxy @n))
      rows =
        [ [ if j == i
              then gf2one
              else
                if j == n + i
                  then c
                  else gf2zero
          | j <- [0 .. 2 * n - 1]
          ]
        | i <- [0 .. n - 1]
        ]
   in FinRel n n (rref rows)

-- * Category structure (named constrained combinators)

--
-- The unconstrained class tower does not carry object evidence, so 'FinRel'
-- provides its structure as named combinators with explicit 'KnownDim'
-- constraints rather than as 'Category'/'Tensor'/'Traced' instances.

compFinRel ::
  forall a b c.
  FinRel b c ->
  FinRel a b ->
  FinRel a c
compFinRel (FinRel pOut m rowsB) (FinRel n pIn rowsA) =
  if pIn /= pOut
    then error "compFinRel: middle dimension mismatch"
    else
      let rA = length rowsA
          rB = length rowsB
          (aIn, aOut) = unzip (map (splitAt n) rowsA)
          (bIn, bOut) = unzip (map (splitAt pIn) rowsB)
          kRows =
            [ [aOutRow !! i | aOutRow <- aOut] ++ [bInRow !! i | bInRow <- bIn]
            | i <- [0 .. pIn - 1]
            ]
          basis = nullspace (rA + rB) kRows
          rows =
            [ let (x, y) = splitAt rA v
                  a = mxv (transpose aIn) x
                  c = mxv (transpose bOut) y
               in a ++ c
            | v <- basis
            ]
       in FinRel n m (rref rows)

-- * Monoidal / traced structure

parFinRel ::
  forall a b c d.
  FinRel a b ->
  FinRel c d ->
  FinRel (a, c) (b, d)
parFinRel (FinRel n p rowsA) (FinRel m q rowsB) =
  let rowA (aIn, aOut) = aIn ++ zeros m ++ aOut ++ zeros q
      rowB (bIn, bOut) = zeros n ++ bIn ++ zeros p ++ bOut
      rows =
        map (rowA . splitAt n) rowsA
          ++ map (rowB . splitAt m) rowsB
   in FinRel (n + m) (p + q) (rref rows)

traceFinRel ::
  forall a b c.
  (KnownDim a, KnownDim b, KnownDim c) =>
  FinRel (a, b) (a, c) ->
  FinRel b c
traceFinRel (FinRel inDim _ rows) =
  let aDim = dimVal (Proxy @a)
      bDim = dimVal (Proxy @b)
      cDim = dimVal (Proxy @c)
      splitRow row =
        let (ab, ac) = splitAt inDim row
            (aIn, bIn) = splitAt aDim ab
            (aOut, cOut) = splitAt aDim ac
         in (aIn, bIn, aOut, cOut)
      parts = map splitRow rows
      bInRows = [bIn | (_, bIn, _, _) <- parts]
      cOutRows = [cOut | (_, _, _, cOut) <- parts]
      kRows =
        [ [gf2add (aIn !! i) (aOut !! i) | (aIn, _, aOut, _) <- parts]
        | i <- [0 .. aDim - 1]
        ]
      basis = nullspace (length rows) kRows
      bcRows =
        [ let b = mxv (transpose bInRows) v
              c = mxv (transpose cOutRows) v
           in b ++ c
        | v <- basis
        ]
   in FinRel bDim cDim (rref bcRows)

-- * Bimonoid generators

instance (KnownNat n) => Copy FinRel (FinObj n) where
  copy = finCopy

instance (KnownNat n) => Discard FinRel (FinObj n) where
  discard = finDiscard

instance (KnownNat n) => Merge FinRel (FinObj n) where
  plus = finPlus

instance (KnownNat n) => Zero FinRel (FinObj n) where
  zero = finZero

finCopyUnit :: FinRel () ((), ())
finCopyUnit = FinRel 0 0 []

finDiscardUnit :: FinRel () ()
finDiscardUnit = FinRel 0 0 []

finPlusUnit :: FinRel ((), ()) ()
finPlusUnit = FinRel 0 0 []

finZeroUnit :: FinRel () ()
finZeroUnit = FinRel 0 0 []

instance Copy FinRel () where
  copy = finCopyUnit

instance Discard FinRel () where
  discard = finDiscardUnit

instance Merge FinRel () where
  plus = finPlusUnit

instance Zero FinRel () where
  zero = finZeroUnit
