# circuits — imports and pragmas

Imports for using circuits.  The umbrella module `Circuit` re-exports everything.

```haskell
import Circuit
```

That's it.  `Circuit` brings in `Circuit(..)`, `Wire`, `Step`, `Co(..)`, `Contra(..)`, `close`, `reify`, `Trace(..)`, `cellIO`, `Monoid(..)`, `Comonoid(..)`, `Dagger(..)`, `Bimonoid`, `transpose`, `Net`, `upgrade`, `loom`, `melt`, `Hyper(..)`, `lift`, `lower`, `base`, `push`, `run`, `encode`, `encodeEither`, `runEither`, `flatten`, `Braided(..)`, `ambient`, `assoc`, `seed`, `absorb`, `release`, `coassoc`, `coseed`, `coabsorbL`, `coabsorbR`, `coreleaseL`, `coreleaseR`, `ambientBy`, `MonoidalP(..)`.

LANGUAGE pragmas used internally: `CPP`, `RankNTypes`, `UndecidableInstances`, `ConstraintKinds`, `GADTs`, `FlexibleInstances`.

For user code: `GHC2021` covers most, add `BlockArguments` if you want `\\case` style.  `Prelude hiding (Monoid)` if you bring in `Circuit` unqualified.

`>>>` and `Kleisli` come from `Control.Arrow` and `Control.Category` — not re-exported by Circuit.

## three tags

`Lift` embeds a base arrow. `Compose` sequences circuits. `Knot` introduces a feedback channel.

The tensor choice lives in the type argument: `(,)` for lazy coinductive sharing, `Either` for iteration (`Left` = continue, `Right` = exit).

## minimal example

```haskell
import Circuit
import Control.Arrow (Kleisli(..), runKleisli)
import Control.Category ((>>>))
import Data.Bool (bool)
import System.IO (Handle, IOMode(ReadMode), hClose, hGetLine, hIsEOF, openFile)

openf :: Circuit (Kleisli IO) t FilePath Handle
openf = Lift (Kleisli (\fp -> openFile fp ReadMode))

countLines :: Circuit (Kleisli IO) Either Handle (Handle, Int)
countLines = Knot (Kleisli step)
  where
    step (Left (h, n)) =
      hIsEOF h >>= bool
        (hGetLine h >> pure (Left (h, n + 1)))
        (pure (Right (h, n)))
    step (Right h) = pure (Left (h, 0))

pipeline :: Circuit (Kleisli IO) Either FilePath Int
pipeline = openf >>> countLines >>> Lift (Kleisli (\(h, n) -> hClose h >> pure n))

-- paste into ghci:
-- runKleisli (reify pipeline) "readme.md"
```
