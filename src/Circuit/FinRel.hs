{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Finite-dimensional linear relations over a field.
--
-- This is the semantic base category for signal-flow graphs: objects are
-- natural numbers (encoded as 'FinObj'), morphisms are linear relations
-- presented as the row space of a matrix with @(n+m)@ columns.
--
-- The first spike is over GF(2): values are 'Bool', addition is 'xor',
-- multiplication is '&&'.  The category carries the cartesian monoidal
-- structure @(,)@, is traced, and supports the copy/discard/plus/zero
-- generators that 'Circuit.Net' uses for wiring.
module Circuit.FinRel
  ( -- * Field
    Field (..),

    -- * Objects
    FinObj (..),
    KnownDim (..),

    -- * Morphisms
    FinRel (..),

    -- * Smart constructors
    finId,
    compFinRel,
    parFinRel,
    unitlFinRel,
    unitl'FinRel,
    unitrFinRel,
    unitr'FinRel,
    swapFinRel,
    assocFinRel,
    assoc'FinRel,
    slideFinRel,
    strengthFinRel,
    traceFinRel,
    finCopy,
    finDiscard,
    finPlus,
    finZero,
    finScalar,
    wiring,
  )
where

import Circuit.Category (Category (..), (.>))
import Circuit.Dagger (Copy (..), Discard (..), Merge (..), Zero (..))
import Data.Kind (Type)
import Data.List (findIndex, foldl', transpose)
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat, Nat, natVal)
import Prelude hiding (id, (.))

-- ===========================================================================
-- Field
-- ===========================================================================

-- | A minimal field class for the linear-algebra core.
class (Eq k) => Field k where
  fzero :: k
  fone :: k
  fadd :: k -> k -> k
  fmul :: k -> k -> k
  fneg :: k -> k
  finv :: k -> k

instance Field Bool where
  fzero = False
  fone = True
  fadd = (/=)
  fmul = (&&)
  fneg = id
  finv = id

-- ===========================================================================
-- Objects
-- ===========================================================================

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

-- ===========================================================================
-- Morphisms
-- ===========================================================================

-- | A linear relation @n -> m@ over the field @k@.
--
-- Internally a matrix whose rows span the relation:
--
-- @
--   { (take n v, drop n v) | v in row space }
-- @
--
-- The stored dimensions are trusted; the matrix is kept in reduced row
-- echelon form for canonical equality.
data FinRel (k :: Type) (n :: Type) (m :: Type) = FinRel
  { finInDim :: !Int,
    finOutDim :: !Int,
    finMat :: ![[k]]
  }
  deriving (Show)

instance (Field k) => Eq (FinRel k n m) where
  FinRel _ _ m1 == FinRel _ _ m2 = rref m1 == rref m2

-- ===========================================================================
-- Matrix primitives
-- ===========================================================================

zeros :: (Field k) => Int -> [k]
zeros n = replicate n fzero

vscale :: (Field k) => k -> [k] -> [k]
vscale c = map (fmul c)

vdot :: (Field k) => [k] -> [k] -> k
vdot xs ys = foldr fadd fzero (zipWith fmul xs ys)

-- | Matrix (rows) times vector.
mxv :: (Field k) => [[k]] -> [k] -> [k]
mxv m v = map (vdot v) m

setAt :: Int -> a -> [a] -> [a]
setAt i x xs = take i xs ++ [x] ++ drop (i + 1) xs

swapRows :: Int -> Int -> [a] -> [a]
swapRows i j xs
  | i == j = xs
  | otherwise = setAt i (xs !! j) (setAt j (xs !! i) xs)

-- | Reduced row echelon form.  Zero rows are removed.
rref :: (Field k) => [[k]] -> [[k]]
rref rows = filter (any (/= fzero)) (go rows 0 0)
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
                  m'' = setAt r (vscale (finv pivotVal) pivotRow) m'
                  m''' = eliminate c r m''
               in go m''' (r + 1) (c + 1)

    width m = maybe 0 length (listToMaybe m)

    findPivot m r c =
      fmap (+ r) (findIndex ((/= fzero) . (!! c)) (drop r m))

    eliminate c r m =
      [ if i == r
          then row
          else
            let factor = row !! c
             in zipWith (\x y -> fadd x (fmul factor y)) row (m !! r)
      | (i, row) <- zip [0 ..] m
      ]

-- | Basis for the nullspace of a matrix with the given column width.
--
-- The matrix may have zero rows; in that case the nullspace is the whole
-- space of the given dimension.
nullspace :: (Field k) => Int -> [[k]] -> [[k]]
nullspace width rows =
  let rrefm = rref rows
      pivots = mapMaybe (listToMaybe . map fst . filter ((/= fzero) . snd) . zip [0 ..]) rrefm
      freeCols = filter (`notElem` pivots) [0 .. width - 1]
      basis =
        [ let vec = [if c == f then fone else fzero | c <- [0 .. width - 1]]
              pivotVals = [fneg (row !! f) | row <- rrefm]
              vec' = foldl' (\v (pc, val) -> setAt pc val v) vec (zip pivots pivotVals)
           in vec'
        | f <- freeCols
        ]
   in basis

-- ===========================================================================
-- Wiring and generators
-- ===========================================================================

-- | Build a wiring isomorphism from explicit dimensions and a permutation.
mkWiring ::
  (Field k) =>
  Int ->
  Int ->
  (Int -> Int) ->
  FinRel k a b
mkWiring dIn dOut perm =
  let rows =
        [ [ if j == i || j == dIn + perm i
              then fone
              else fzero
          | j <- [0 .. dIn + dOut - 1]
          ]
        | i <- [0 .. dIn - 1]
        ]
   in FinRel dIn dOut (rref rows)

-- | Build a wiring isomorphism from a permutation.
wiring ::
  forall k a b.
  (Field k, KnownDim a, KnownDim b) =>
  (Int -> Int) ->
  FinRel k a b
wiring = mkWiring (dimVal (Proxy @a)) (dimVal (Proxy @b))

finId ::
  forall k a.
  (Field k, KnownDim a) =>
  FinRel k a a
finId =
  let n = dimVal (Proxy @a)
      rows =
        [ [if j == i || j == n + i then fone else fzero | j <- [0 .. 2 * n - 1]]
        | i <- [0 .. n - 1]
        ]
   in FinRel n n (rref rows)

finCopy ::
  forall k n.
  (Field k, KnownNat n) =>
  FinRel k (FinObj n) (FinObj n, FinObj n)
finCopy =
  let n = fromIntegral (natVal (Proxy @n))
      rows =
        [ [ if j == i || j == n + i || j == 2 * n + i
              then fone
              else fzero
          | j <- [0 .. 3 * n - 1]
          ]
        | i <- [0 .. n - 1]
        ]
   in FinRel n (2 * n) (rref rows)

finDiscard ::
  forall k n.
  (Field k, KnownNat n) =>
  FinRel k (FinObj n) ()
finDiscard =
  let n = fromIntegral (natVal (Proxy @n))
      rows = [[if j == i then fone else fzero | j <- [0 .. n - 1]] | i <- [0 .. n - 1]]
   in FinRel n 0 (rref rows)

finPlus ::
  forall k n.
  (Field k, KnownNat n) =>
  FinRel k (FinObj n, FinObj n) (FinObj n)
finPlus =
  let n = fromIntegral (natVal (Proxy @n))
      rows =
        concatMap
          ( \i ->
              [ [if j == i || j == 2 * n + i then fone else fzero | j <- [0 .. 3 * n - 1]],
                [if j == n + i || j == 2 * n + i then fone else fzero | j <- [0 .. 3 * n - 1]]
              ]
          )
          [0 .. n - 1]
   in FinRel (2 * n) n (rref rows)

finZero ::
  forall k n.
  (KnownNat n) =>
  FinRel k () (FinObj n)
finZero =
  let n = fromIntegral (natVal (Proxy @n))
   in FinRel 0 n []

finScalar ::
  forall k n.
  (Field k, KnownNat n) =>
  k ->
  FinRel k (FinObj n) (FinObj n)
finScalar c =
  let n = fromIntegral (natVal (Proxy @n))
      rows =
        [ [ if j == i
              then fone
              else
                if j == n + i
                  then c
                  else fzero
          | j <- [0 .. 2 * n - 1]
          ]
        | i <- [0 .. n - 1]
        ]
   in FinRel n n (rref rows)

-- ===========================================================================
-- Category structure (named constrained combinators)
--
-- The unconstrained class tower no longer carries object evidence, so 'FinRel'
-- provides its structure as named combinators with explicit 'KnownDim'
-- constraints rather than as 'Category'/'Tensor'/'Traced' instances.
-- ===========================================================================

compFinRel ::
  forall k a b c.
  (Field k) =>
  FinRel k b c ->
  FinRel k a b ->
  FinRel k a c
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

-- ===========================================================================
-- Monoidal / traced structure
-- ===========================================================================

unitlFinRel ::
  forall k a.
  (Field k, KnownDim a) =>
  FinRel k ((), a) a
unitlFinRel = mkWiring (dimVal (Proxy @a)) (dimVal (Proxy @a)) id

unitl'FinRel ::
  forall k a.
  (Field k, KnownDim a) =>
  FinRel k a ((), a)
unitl'FinRel = mkWiring (dimVal (Proxy @a)) (dimVal (Proxy @a)) id

unitrFinRel ::
  forall k a.
  (Field k, KnownDim a) =>
  FinRel k (a, ()) a
unitrFinRel = mkWiring (dimVal (Proxy @a)) (dimVal (Proxy @a)) id

unitr'FinRel ::
  forall k a.
  (Field k, KnownDim a) =>
  FinRel k a (a, ())
unitr'FinRel = mkWiring (dimVal (Proxy @a)) (dimVal (Proxy @a)) id

parFinRel ::
  forall k a b c d.
  (Field k) =>
  FinRel k a b ->
  FinRel k c d ->
  FinRel k (a, c) (b, d)
parFinRel (FinRel n p rowsA) (FinRel m q rowsB) =
  let rowA (aIn, aOut) = aIn ++ zeros m ++ aOut ++ zeros q
      rowB (bIn, bOut) = zeros n ++ bIn ++ zeros p ++ bOut
      rows =
        map (rowA . splitAt n) rowsA
          ++ map (rowB . splitAt m) rowsB
   in FinRel (n + m) (p + q) (rref rows)

swapFinRel ::
  forall k a b.
  (Field k, KnownDim a, KnownDim b) =>
  FinRel k (a, b) (b, a)
swapFinRel =
  let n = dimVal (Proxy @a)
      m = dimVal (Proxy @b)
   in mkWiring (n + m) (m + n) $ \i ->
        if i < n then m + i else i - n

assocFinRel ::
  forall k a b c.
  (Field k, KnownDim a, KnownDim b, KnownDim c) =>
  FinRel k ((a, b), c) (a, (b, c))
assocFinRel =
  let n = dimVal (Proxy @a)
      m = dimVal (Proxy @b)
      l = dimVal (Proxy @c)
   in mkWiring (n + m + l) (n + m + l) id

assoc'FinRel ::
  forall k a b c.
  (Field k, KnownDim a, KnownDim b, KnownDim c) =>
  FinRel k (a, (b, c)) ((a, b), c)
assoc'FinRel =
  let n = dimVal (Proxy @a)
      m = dimVal (Proxy @b)
      l = dimVal (Proxy @c)
   in mkWiring (n + m + l) (n + m + l) id

slideFinRel ::
  forall k a b c.
  (Field k, KnownDim a, KnownDim b, KnownDim c) =>
  FinRel k (a, (b, c)) (b, (a, c))
slideFinRel =
  let n = dimVal (Proxy @a)
      m = dimVal (Proxy @b)
      l = dimVal (Proxy @c)
   in mkWiring (n + m + l) (m + n + l) $ \i ->
        if i < n
          then m + i
          else
            if i < n + m
              then i - n
              else i

strengthFinRel ::
  forall k a b c.
  (Field k, KnownDim a) =>
  FinRel k b c ->
  FinRel k (a, b) (a, c)
strengthFinRel = parFinRel finId

traceFinRel ::
  forall k a b c.
  (Field k, KnownDim a, KnownDim b, KnownDim c) =>
  FinRel k (a, b) (a, c) ->
  FinRel k b c
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
        [ [fadd (aIn !! i) (aOut !! i) | (aIn, _, aOut, _) <- parts]
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

-- ===========================================================================
-- Bimonoid generators
-- ===========================================================================

instance (Field k, KnownNat n) => Copy (FinRel k) (FinObj n) where
  copy = finCopy

instance (Field k, KnownNat n) => Discard (FinRel k) (FinObj n) where
  discard = finDiscard

instance (Field k, KnownNat n) => Merge (FinRel k) (FinObj n) where
  plus = finPlus

instance (KnownNat n) => Zero (FinRel k) (FinObj n) where
  zero = finZero

finCopyUnit :: FinRel k () ((), ())
finCopyUnit = FinRel 0 0 []

finDiscardUnit :: FinRel k () ()
finDiscardUnit = FinRel 0 0 []

finPlusUnit :: FinRel k ((), ()) ()
finPlusUnit = FinRel 0 0 []

finZeroUnit :: FinRel k () ()
finZeroUnit = FinRel 0 0 []

instance Copy (FinRel k) () where
  copy = finCopyUnit

instance Discard (FinRel k) () where
  discard = finDiscardUnit

instance Merge (FinRel k) () where
  plus = finPlusUnit

instance Zero (FinRel k) () where
  zero = finZeroUnit
