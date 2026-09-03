-- | Optic oracles — mixed optics as residual maps.
--
-- Every positive family is paired with a perturbation, so that a passing
-- check is known not to be vacuous: an optic that fails the round-trip law, a
-- sample that discriminates, and a residual change that is nevertheless
-- observationally invisible.
module Axioma.Optic
  ( opticTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Category (Category (..), (.>))
import Circuit.Equip (Poles (..))
import Circuit.Optic
  ( Optic (..),
    POptic (..),
    composeOptic,
    composePOptic,
    identityOptic,
    identityPOptic,
    lensAsOptic,
    opticAsLens,
    opticUpdate,
    popticPoles,
    popticUpdate,
  )
import Control.Monad (when)
import Data.Void (Void)
import Prelude hiding (id, (.))

-- * Cartesian witnesses

-- | Lens focusing the first component of a pair.  Residual: the second
-- component.
firstLens :: POptic (,) String (->) Int Int (Int, String) (Int, String)
firstLens = POptic (\(n, s) -> (s, n)) (\(s, n) -> (n, s))

-- | Lens focusing the second component of a pair.  Residual: the first
-- component.  Both legs are the identity because the residual is already in
-- the leading slot.
secondLens :: POptic (,) Int (->) String String (Int, String) (Int, String)
secondLens = POptic id id

-- | A well-typed optic that is /not/ lawful: the backward leg perturbs the
-- residual on the way out, so updating with the identity is not the identity.
--
-- This is the falsification artifact for the round-trip law.  'POptic' carries
-- no lawfulness condition, and the wiki's open thread — lawfulness as
-- coalgebra for the comonad induced by the round-trip witness — is exactly
-- the gap this witnesses.
badLens :: POptic (,) String (->) Int Int (Int, String) (Int, String)
badLens = POptic (\(n, s) -> (s, n)) (\(s, n) -> (n, s ++ "!"))

-- | Outer lens: focus the @(Int, Bool)@ half of a nested pair.
outerLens ::
  POptic (,) String (->) (Int, Bool) (Int, Bool) ((Int, Bool), String) ((Int, Bool), String)
outerLens = POptic (\(p, s) -> (s, p)) (\(s, p) -> (p, s))

-- | Inner lens: focus the @Int@ of an @(Int, Bool)@.
innerLens :: POptic (,) Bool (->) Int Int (Int, Bool) (Int, Bool)
innerLens = POptic (\(n, b) -> (b, n)) (\(b, n) -> (n, b))

-- * Cocartesian witness

-- | Prism matching the @Left@ branch.  The residual is the branch that did
-- not match.
--
-- @'Circuit.Tensor.Unit' 'Either'@ is uninhabited, which is what denied the
-- old 'Circuit.Body.SomeBody' an identity.  'Optic' has no such problem:
-- the residual is produced by the forward leg, never stored.  The @Either@
-- identity oracle below is the observable consequence.
prismLeft :: POptic Either String (->) Int Int (Either Int String) (Either Int String)
prismLeft =
  POptic
    ( \case
        Left n -> Right n
        Right s -> Left s
    )
    ( \case
        Left s -> Right s
        Right n -> Left n
    )

-- * Helpers

incFocus :: Int -> Int
incFocus = (+ 1)

reverseFocus :: String -> String
reverseFocus = reverse

-- | Extensional agreement over a bounded sample.
sameOn :: (Eq r) => [s] -> (s -> r) -> (s -> r) -> Bool
sameOn xs f g = all (\x -> f x == g x) xs

-- | Bounded sample of the cartesian whole.
wholes :: [(Int, String)]
wholes = [(n, s) | n <- [0, 3, 7], s <- ["", "hello", "ab"]]

-- | Bounded sample of the nested whole.
nested :: [((Int, Bool), String)]
nested = [((n, b), s) | n <- [0, 3], b <- [True, False], s <- ["", "hi"]]

-- | Bounded sample of the sum whole.
branches :: [Either Int String]
branches = [Left 0, Left 3, Right "", Right "hi"]

opticTopic :: Verbosity -> IO [Bool]
opticTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Optic oracles"
  sequence
    [ -- update action
      checkV verbosity "identity optic updates the focus unchanged" $
        popticUpdate (identityPOptic :: POptic (,) () (->) Int Int Int Int) incFocus 3 == 4,
      checkV verbosity "firstLens updates the first component" $
        popticUpdate firstLens incFocus (3, "hello") == (4, "hello"),
      checkV verbosity "secondLens updates the second component" $
        popticUpdate secondLens reverseFocus (3, "hello") == (3, "olleh"),
      -- lens laws
      checkV verbosity "lens get-put (update with identity is identity)" $
        sameOn wholes (popticUpdate firstLens id) id,
      checkV verbosity "lens put-get (the written focus reads back)" $
        sameOn wholes (popticUpdate firstLens (const 9) .> fst) (const 9),
      checkV verbosity "lens put-put (the last write wins)" $
        sameOn
          wholes
          (popticUpdate firstLens (const 7) .> popticUpdate firstLens (const 9))
          (popticUpdate firstLens (const 9)),
      -- falsification: the laws above are not automatic
      checkV verbosity "an unlawful optic is well-typed and fails get-put" $
        not (sameOn wholes (popticUpdate badLens id) id),
      checkV verbosity "the unlawful optic still passes put-get (the failure is specific)" $
        sameOn wholes (popticUpdate badLens (const 9) .> fst) (const 9),
      -- composition
      checkV verbosity "popticUpdate is functorial through composePOptic" $
        sameOn
          nested
          (popticUpdate (composePOptic innerLens outerLens) incFocus)
          (popticUpdate outerLens (popticUpdate innerLens incFocus)),
      checkV verbosity "functoriality holds for the unlawful optic too (it is structural)" $
        sameOn
          wholes
          (popticUpdate (composePOptic identityPOptic badLens) incFocus)
          (popticUpdate badLens incFocus),
      checkV verbosity "composePOptic right unit (identity on the inside)" $
        sameOn
          wholes
          (popticUpdate (composePOptic identityPOptic firstLens) incFocus)
          (popticUpdate firstLens incFocus),
      checkV verbosity "composePOptic left unit (identity on the outside)" $
        sameOn
          wholes
          (popticUpdate (composePOptic firstLens identityPOptic) incFocus)
          (popticUpdate firstLens incFocus),
      checkV verbosity "the nested sample discriminates (functoriality is not vacuous)" $
        not
          ( sameOn
              nested
              (popticUpdate (composePOptic innerLens outerLens) incFocus)
              (popticUpdate (composePOptic innerLens outerLens) (const 0))
          ),
      -- Either / prisms
      checkV verbosity "Either identity optic updates the focus unchanged" $
        popticUpdate (identityPOptic :: POptic Either Void (->) Int Int Int Int) incFocus 3 == 4,
      checkV verbosity "prism updates the matching branch only" $
        sameOn
          branches
          (popticUpdate prismLeft incFocus)
          ( \case
              Left n -> Left (n + 1)
              Right s -> Right s
          ),
      checkV verbosity "prism get-put" $
        sameOn branches (popticUpdate prismLeft id) id,
      checkV verbosity "prism composition with the Either identity agrees" $
        sameOn
          branches
          (popticUpdate (composePOptic identityPOptic prismLeft) incFocus)
          (popticUpdate prismLeft incFocus),
      -- the residual is a coend, not a product
      checkV verbosity "polynomial-lens round trip changes the residual but not the behaviour" $
        sameOn
          wholes
          (opticUpdate (lensAsOptic (opticAsLens (Optic firstLens))) incFocus)
          (popticUpdate firstLens incFocus),
      checkV verbosity "the round trip of the unlawful optic is still unlawful" $
        not
          ( sameOn
              wholes
              (opticUpdate (lensAsOptic (opticAsLens (Optic badLens))) id)
              id
          ),
      -- poles action
      checkV verbosity "popticPoles suffixes the backward leg onto the companion" $
        let p = Poles fst (\ch -> (ch, 7)) :: Poles String String (->) (String, Int) (String, Int)
         in companion (popticPoles firstLens p) "hi" == (7, "hi"),
      checkV verbosity "popticPoles read pole agrees with the backward leg" $
        let p = Poles fst (\ch -> (ch, 7)) :: Poles String String (->) (String, Int) (String, Int)
         in companion (popticPoles firstLens p) "hi" == popticBackward firstLens ("hi", 7)
    ]
