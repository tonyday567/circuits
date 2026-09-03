-- | Split-pole bridge probes.
--
-- The carrier placement of a split pole is
--
-- @
--   conjoint  :: a -> m ch      -- K m
--   companion :: c ch' -> b     -- CoK c
-- @
--
-- and 'Circuit.Equip.plugBridge' closes it only through a bridge
-- @m ch -> c ch'@ between the monad and the comonad.  This module
-- hand-rolls the candidate pairs and records, as oracles, what each bridge
-- demands and what each loses.
module Axioma.Split
  ( splitTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Category (CoK (..), Comonad (..), K (..))
import Circuit.Equip (Poles (..), close, plugBridge)
import Control.Monad (when)
import Data.Functor.Identity (Identity (..))
import Data.Monoid (Sum (..))

-- * Hand-rolled pairs

-- | Writer-shaped functor: payload with a log.
newtype Wr w a = Wr (a, w)
  deriving (Eq, Show)

instance Functor (Wr w) where
  fmap f (Wr (a, w)) = Wr (f a, w)

instance (Monoid w) => Applicative (Wr w) where
  pure a = Wr (a, mempty)
  Wr (f, w) <*> Wr (a, w') = Wr (f a, w <> w')

instance (Monoid w) => Monad (Wr w) where
  Wr (a, w) >>= f = let Wr (b, w') = f a in Wr (b, w <> w')

-- | Env-shaped functor: an environment with a value — the same functor as
-- 'Wr', swapped.
newtype Env e a = Env (e, a)
  deriving (Eq, Show)

instance Functor (Env e) where
  fmap f (Env (e, a)) = Env (e, f a)

instance Comonad (Env e) where
  extract (Env (_, a)) = a
  duplicate (Env (e, a)) = Env (e, Env (e, a))

-- | Store: an observation function with a current position.
data Store s a = Store (s -> a) s

instance Functor (Store s) where
  fmap f (Store g s) = Store (f . g) s

instance Comonad (Store s) where
  extract (Store g s) = g s
  duplicate (Store g s) = Store (\s' -> Store g s') s

-- | Traced: a computation reading a monoid.
newtype Traced w a = Traced {runTraced :: w -> a}

instance Functor (Traced w) where
  fmap f (Traced g) = Traced (f . g)

instance (Monoid w) => Comonad (Traced w) where
  extract (Traced g) = g mempty
  duplicate (Traced g) = Traced (\w -> Traced (\w' -> g (w <> w')))

-- | State: the classic state monad.
newtype State s a = State {runState :: s -> (a, s)}

instance Functor (State s) where
  fmap f (State g) = State (\s -> let (a, s') = g s in (f a, s'))

instance Applicative (State s) where
  pure a = State (\s -> (a, s))
  State f <*> State g = State (\s -> let (h, s') = f s; (a, s'') = g s' in (h a, s''))

instance Monad (State s) where
  State g >>= f = State (\s -> let (a, s') = g s; State h = f a in h s')

-- * Bridges

-- | The smoke test: 'Wr' and 'Env' are the same functor, so the bridge is
-- an isomorphism.
wrToEnv :: Wr w a -> Env w a
wrToEnv (Wr (a, w)) = Env (w, a)

-- | The other half of the smoke test.
envToWr :: Env w a -> Wr w a
envToWr (Env (e, a)) = Wr (a, e)

-- | State-to-Store needs a seed: the bridge carries it explicitly.
stateToStore :: s -> State s a -> Store s a
stateToStore s0 (State f) = Store (\s -> fst (f s)) s0

-- | Store-to-State exists unconditionally, but the next state is the input
-- state: the transition is forgotten.
storeToState :: Store s a -> State s a
storeToState (Store g _) = State (\s -> (g s, s))

-- | Writer-to-Traced exists unconditionally but discards the trace
-- argument.
wrToTraced :: Wr w a -> Traced w a
wrToTraced (Wr (a, _)) = Traced (const a)

-- | Traced-to-Writer needs a monoid unit to read at.
tracedToWr :: (Monoid w) => Traced w a -> Wr w a
tracedToWr (Traced g) = Wr (g mempty, mempty)

-- | List-to-Identity needs a 'Monoid' (fold) — the merge/zero shape — or a
-- choice (head, partial; not provided here).
listToIdentity :: (Monoid a) => [a] -> Identity a
listToIdentity = Identity . mconcat

-- | Identity-to-List is free and faithful.
identityToList :: Identity a -> [a]
identityToList = pure . runIdentity

-- * Sampled observation

-- | Sampled observation of a 'Store': the home position plus the
-- observation function's values at the sample points.
obsStore :: [s] -> Store s a -> (s, [a])
obsStore samples (Store g s) = (s, map g samples)

-- * Oracles

-- | Split-pole bridge oracles.
splitTopic :: Verbosity -> IO [Bool]
splitTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Split-pole bridge oracles"
  sequence
    [ checkV verbosity "Wr/Env bridge is an isomorphism (smoke test)" $
        let ws = [Wr (i, "w") | i <- [0 .. 3]] :: [Wr String Int]
            es = [Env (i, 'x') | i <- [0 .. 3]] :: [Env Int Char]
         in all (\w -> envToWr (wrToEnv w) == w) ws
              && all (\e -> wrToEnv (envToWr e) == e) es,
      checkV verbosity "State/Store bridge: the seed is visible in the close" $
        let p =
              Poles (K (\a -> State (\s -> (a + s, s + 1)))) (CoK extract) ::
                Poles Int Int (K (State Int)) (CoK (Store Int)) Int Int
         in plugBridge (stateToStore 0) p 5 == 5
              && plugBridge (stateToStore 10) p 5 == 15,
      checkV verbosity "Store-to-State forgets the transition" $
        let st = State (\s -> (s * 2, s + 1)) :: State Int Int
         in runState st 5 == (10, 6)
              && runState (storeToState (stateToStore 0 st)) 5 == (10, 5),
      checkV verbosity "Wr-to-Traced bridge discards the trace argument" $
        let t = wrToTraced (Wr (42, "log")) :: Traced String Int
         in runTraced t "a" == 42 && runTraced t "b" == 42,
      checkV verbosity "Traced-to-Wr reads at the monoid unit" $
        tracedToWr (Traced length) == Wr (0, "" :: String),
      checkV verbosity "list bridge folds; identity-to-list is free but the round trip loses the tails" $
        listToIdentity [Sum 1, Sum 2, Sum 3] == Identity (Sum 6)
          && identityToList (listToIdentity [Sum 1, Sum 2, Sum 3]) == [Sum 6],
      checkV verbosity "plugBridge at Identity agrees with close at (->)" $
        let split =
              Poles (K (Identity . (+ 1))) (CoK runIdentity) ::
                Poles Int Int (K Identity) (CoK Identity) Int Int
            plain = Poles (+ 1) id :: Poles Int Int (->) (->) Int Int
         in plugBridge id split 5 == close plain 5,
      checkV verbosity "Store comonad identity laws (sampled)" $
        let st = Store (* 2) 3 :: Store Int Int
            samples = [0 .. 4]
         in obsStore samples (extract (duplicate st)) == obsStore samples st
              && obsStore samples (extend extract st) == obsStore samples st
    ]
