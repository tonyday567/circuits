# stable-marriage ⟜ concurrent coroutines

From Kidney & Wu, *Hyperfunctions: Communicating Continuations* (POPL 2026, §5.3),
following Allison (1983). Men and women are independent coroutines that communicate
by message-passing. Men propose; women accept or jilt. Jilting wakes a suspended man,
who proposes to his next choice. The algorithm runs until all men are engaged.

Unlike a sequential pipeline, control transfers between coroutines — a woman's
decision to jilt wakes that man's coroutine, which resumes proposing. The order
depends on who jilts whom.

## types

```haskell
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (elemIndex)

type Man   = String
type Woman = String
type Rankings a = Map a [a]
```

## coroutines

A coroutine is a state machine: `Coro s i o` holds internal state `s`, receives
input `i`, and produces output `o` plus a new state.

```haskell
data Coro s i o = Coro
  { coStep  :: s -> i -> (o, s)
  , coState :: s
  }

send :: Coro s i o -> i -> (o, Coro s i o)
send co i = let (o, s') = coStep co (coState co) i
            in (o, co { coState = s' })
```

A man's state is his remaining preference list. His input is `()` (wake-up
signal). His output is the next woman to propose to.

```haskell
manCoro :: Man -> [Woman] -> Coro [Woman] () (Maybe Woman)
manCoro name prefs = Coro
  { coStep = \remaining () ->
      case remaining of
        []    -> (Nothing, [])
        (w:ws) -> (Just w, ws)
  , coState = prefs
  }
```

A woman's state is her current fiancé and preference list. Her input is a
suitor. Her output is `(accepted, Maybe jiltedMan)`.

```haskell
data WomanState = WomanState
  { wsFiance :: Maybe Man
  , wsRanks  :: [Man]
  }

womanCoro :: Woman -> [Man] -> Coro WomanState Man (Bool, Maybe Man)
womanCoro _ ranks = Coro
  { coStep = \st@WomanState{wsFiance, wsRanks} suitor ->
      let rankOf m = elemIndex m wsRanks
          better a b = case (rankOf a, rankOf b) of
            (Just ra, Just rb) -> ra < rb
            _                  -> False
      in case wsFiance of
        Nothing ->
          ((True, Nothing), st { wsFiance = Just suitor })
        Just current ->
          if better suitor current
            then ((True, Just current), st { wsFiance = Just suitor })
            else ((False, Nothing), st)
  , coState = WomanState Nothing ranks
  }
```

## scheduler

The scheduler picks a free man (pending/jilted first), runs his coroutine,
routes the proposal to the woman's coroutine, and handles jilting by
moving the jilted man to the pending queue.

```haskell
data System = System
  { sysMen     :: Map Man (Coro [Woman] () (Maybe Woman))
  , sysWomen   :: Map Woman (Coro WomanState Man (Bool, Maybe Man))
  , sysEngaged :: Map Woman Man
  , sysFreeMen :: [Man]
  , sysPending :: [Man]
  , sysLog     :: [String]
  }

step :: System -> System
step sys@System{sysMen, sysWomen, sysEngaged, sysFreeMen, sysPending, sysLog} =
  let (man, newPending, newFree) = case sysPending of
        (m:ps) -> (m, ps, sysFreeMen)
        []     -> case sysFreeMen of
                    (m:fs) -> (m, [], fs)
                    []     -> error "No free men"
  in case Map.lookup man sysMen of
      Nothing -> sys
      Just manCo ->
        let (mproposal, manCo') = send manCo ()
        in case mproposal of
          Nothing ->
            sys { sysMen     = Map.insert man manCo' sysMen
                , sysFreeMen = newFree
                , sysPending = newPending
                , sysLog     = sysLog ++ [man ++ " has no one left"]
                }
          Just woman ->
            case Map.lookup woman sysWomen of
              Nothing -> sys
              Just womanCo ->
                let ((accepted, mJilted), womanCo') = send womanCo man
                    logEntry = man ++ " → " ++ woman ++ "; "
                               ++ (if accepted then "accepted" else "rejected")
                               ++ case mJilted of
                                    Just j -> "; jilts " ++ j
                                    Nothing -> ""
                in if accepted
                   then
                     let engagements' = Map.insert woman man sysEngaged
                         (pending', free') = case mJilted of
                           Just j -> (j : newPending, filter (/= j) newFree)
                           Nothing -> (newPending, newFree)
                     in sys { sysMen     = Map.insert man manCo' sysMen
                            , sysWomen   = Map.insert woman womanCo' sysWomen
                            , sysEngaged = engagements'
                            , sysFreeMen = free'
                            , sysPending = pending'
                            , sysLog     = sysLog ++ [logEntry]
                            }
                   else
                     sys { sysMen     = Map.insert man manCo' sysMen
                          , sysWomen   = Map.insert woman womanCo' sysWomen
                          , sysFreeMen = man : newFree
                          , sysPending = newPending
                          , sysLog     = sysLog ++ [logEntry]
                          }

stableMarriage ::
  Rankings Man -> Rankings Woman -> ([String], Map Woman Man)
stableMarriage mranks wranks =
  let men   = Map.keys mranks
      women = Map.keys wranks
      initSys = System
        { sysMen     = Map.fromList [(m, manCoro m (mranks Map.! m)) | m <- men]
        , sysWomen   = Map.fromList [(w, womanCoro w (wranks Map.! w)) | w <- women]
        , sysEngaged = Map.empty
        , sysFreeMen = men
        , sysPending = []
        , sysLog     = []
        }
      go sys | null (sysFreeMen sys) && null (sysPending sys) = sys
             | otherwise = go (step sys)
      final = go initSys
  in (sysLog final, sysEngaged final)
```

## test data

From the paper.

```haskell
mranks :: Rankings Man
mranks = Map.fromList
  [ ("Aaron", ["Ciara", "Annie", "Betty"])
  , ("Barry", ["Ciara", "Betty", "Annie"])
  , ("Conor", ["Ciara", "Annie", "Betty"])
  ]

wranks :: Rankings Woman
wranks = Map.fromList
  [ ("Annie", ["Barry", "Conor", "Aaron"])
  , ("Betty", ["Aaron", "Barry", "Conor"])
  , ("Ciara", ["Conor", "Aaron", "Barry"])
  ]
```

## run

```
>>> let (log, result) = stableMarriage mranks wranks
>>> mapM_ putStrLn log
Aaron → Ciara; accepted
Barry → Ciara; rejected
Barry → Betty; accepted
Conor → Ciara; accepted; jilts Aaron
Aaron → Annie; accepted

>>> result
fromList [("Annie","Aaron"),("Betty","Barry"),("Ciara","Conor")]
```

## reference

- Kidney & Wu, POPL 2026, §5.3 — the Co monad with delimited continuations
- `examples/spec.md` — the paper's full concurrent encoding
- `examples/coroutine-hyper.hs` — Coro→Channel encoding
- `examples/channel-basics.md` — the turn-based pipeline pattern
