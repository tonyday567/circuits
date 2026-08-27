{-# LANGUAGE TypeApplications #-}

-- | Optic oracles — mixed optics as residual maps.
module Axioma.Optic
  ( opticTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Channel (Channel (..))
import Circuit.Optic (Optic (..), composeOptic, identityOptic, opticUpdate)
import Circuit.Tensor (Tensor (..))
import Control.Monad (when)
import Prelude hiding (id, (.))

-- | Lens focusing on the first component of a pair.
--
-- Domain and codomain whole are both @(Int, String)@; the focus is @Int@ and
-- the residual is @String@.
firstLens :: Optic (,) (->) String Int Int (Int, String) (Int, String)
firstLens =
  Optic
    { opticForward = \(n, s) -> (s, n),
      opticBackward = \(s, n') -> (n', s)
    }

-- | Lens focusing on the second component of a pair.
secondLens :: Optic (,) (->) Int String String (Int, String) (Int, String)
secondLens =
  Optic
    { opticForward = \(n, s) -> (n, s),
      opticBackward = \(n, s') -> (n, s')
    }

-- | Increment an @Int@ focus.
incFocus :: Int -> Int
incFocus = (+ 1)

-- | Reverse a @String@ focus.
reverseFocus :: String -> String
reverseFocus = reverse

opticTopic :: Verbosity -> IO [Bool]
opticTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Optic oracles"
  sequence
    [ checkV verbosity "identity optic updates the focus unchanged" $
        opticUpdate @((,)) @((->)) identityOptic incFocus (3 :: Int) == 4,
      checkV verbosity "firstLens updates the first component" $
        opticUpdate firstLens incFocus (3, "hello") == (4, "hello"),
      checkV verbosity "secondLens updates the second component" $
        opticUpdate secondLens reverseFocus (3, "hello") == (3, "olleh"),
      checkV verbosity "composition with identity recovers the original optic" $
        let composite = composeOptic @((,)) @((->)) identityOptic firstLens
         in opticUpdate composite incFocus (3, "hello") == opticUpdate firstLens incFocus (3, "hello")
    ]
