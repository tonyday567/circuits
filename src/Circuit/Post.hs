{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Addressed posts, causal ancestry, and stream-generic logs and inboxes.
--
-- A 'Post' is polymorphic in both its address type @n@ and its body @a@.
-- 'Circuit.Shared.Stamped' supplies occurrence receipts without becoming part
-- of the post itself. 'Circuit.Channel' supplies the construction and read
-- interfaces used by logs and inboxes.
module Circuit.Post
  ( -- * Posts
    Post (..),
    PostId,
    mkPost,
    mkChannelPost,
    replyTo,
    synthesis,
    sortNub,

    -- * Ancestry
    indexToIdMap,
    branches,
    branchesByIndex,
    cone,
    coneByIndex,

    -- * Logs
    Log,
    emptyLog,
    watch,
    post,

    -- * Inboxes and delivery
    Inbox,
    emptyInbox,
    appendInbox,
    unconsInbox,
    inboxWho,
    inboxSubs,
    deliversTo,
  )
where

import Circuit.Channel (Cons (..), Snoc (..), These (..), Uncons (..))
import Data.List (nub, sort)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (listToMaybe)
import Numeric.Natural (Natural)

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Circuit.Post

-- | Absolute post identity. In a stamped log this is the id assigned by the
-- writer. In a chronological pure log, 'indexToIdMap' assigns ids @[0..]@.
type PostId = Natural

-- | One addressed entry with a finite audience and finite causal parents.
--
-- 'channel' selects channel addressing; 'to' carries the resolved audience.
-- 'thread' contains parent ids. Smart constructors keep parent ids as a
-- sorted, duplicate-free set.
--
-- >>> let p = mkPost "alice" ["bob"] "hi" :: Post String String
-- >>> (from p, channel p, to p, thread p, body p)
-- ("alice",Nothing,["bob"],[],"hi")
data Post n a = Post
  { from :: n,
    channel :: Maybe n,
    to :: [n],
    thread :: [PostId],
    body :: a
  }
  deriving (Show, Eq, Ord, Functor)

-- | A fresh root addressed by its audience list.
mkPost :: n -> [n] -> a -> Post n a
mkPost f t = Post f Nothing t []

-- | A fresh root in a named channel. The channel is the address; the audience
-- list records resolved membership at post time.
mkChannelPost :: n -> n -> [n] -> a -> Post n a
mkChannelPost f c t = Post f (Just c) t []

-- | Reply to one parent id. The audience is the parent's sender followed by
-- the parent's other audience members, excluding the replier. The reply
-- inherits the parent's channel.
--
-- >>> let p = mkChannelPost "alice" "room" ["bob", "carol"] () :: Post String ()
-- >>> let r = replyTo "bob" 7 p ()
-- >>> (channel r, to r, thread r)
-- (Just "room",["alice","carol"],[7])
replyTo :: (Eq n) => n -> PostId -> Post n a -> b -> Post n b
replyTo who parentId p b =
  Post
    { from = who,
      channel = channel p,
      to = from p : filter (/= who) (to p),
      thread = [parentId],
      body = b
    }

-- | One descendant of several parents. Parent ids are sorted and deduplicated;
-- synthesis carries no channel and uses its explicit audience.
--
-- >>> thread (synthesis "sum" ["audience"] [3, 1, 3, 2] ())
-- [1,2,3]
synthesis :: n -> [n] -> [PostId] -> a -> Post n a
synthesis who audience parentIds b =
  Post
    { from = who,
      channel = Nothing,
      to = audience,
      thread = sortNub parentIds,
      body = b
    }

-- | Sorted, duplicate-free finite-set representation.
sortNub :: (Ord a) => [a] -> [a]
sortNub = nub . sort

-- | Assign positional ids @[0..]@ to a chronological list of posts.
indexToIdMap :: [Post n a] -> Map PostId (Post n a)
indexToIdMap = Map.fromList . zip [0 ..]

nextId :: Map PostId (Post n a) -> PostId
nextId m = if Map.null m then 0 else fst (Map.findMax m) + 1

-- | Paths from a post to its causal roots, resolved by exact 'PostId'.
--
-- The current post is outside the map and receives the id after the largest
-- key. Only edges strictly below the id of the post being expanded are
-- followed. Dangling, future, self, and cyclic edges therefore terminate at
-- the point where no prior parent can be resolved. A rootless or cyclic path
-- contributes no completed branch.
--
-- >>> let p0 = mkPost "a" ["b"] (); p1 = replyTo "b" 0 p0 (); p2 = replyTo "c" 1 p1 ()
-- >>> branchesByIndex [p0, p1] p2
-- [["c","b","a"]]
branches :: Map PostId (Post n a) -> Post n a -> [[n]]
branches priorMap = go (nextId priorMap)
  where
    go selfId p =
      case thread p of
        [] -> [[from p]]
        is -> concatMap (branchStep selfId p) is

    branchStep selfId p i =
      if i >= selfId
        then []
        else case Map.lookup i priorMap of
          Nothing -> []
          Just q -> map (from p :) (go i q)

-- | Resolve branches by assigning positional ids to a chronological prior log.
branchesByIndex :: [Post n a] -> Post n a -> [[n]]
branchesByIndex prior = branches (indexToIdMap prior)

-- | Every sender occurring on any branch, as a sorted, duplicate-free set.
-- The current post's sender is included whenever it has at least one resolved
-- branch.
cone :: (Ord n) => Map PostId (Post n a) -> Post n a -> [n]
cone priorMap p = sortNub (concat (branches priorMap p))

-- | Resolve a cone by assigning positional ids to a chronological prior log.
coneByIndex :: (Ord n) => [Post n a] -> Post n a -> [n]
coneByIndex prior = cone (indexToIdMap prior)

-- | A stream of bare posts. With list-backed logs, 'post' conses newest-first
-- and 'watch' returns addressed posts oldest-first.
type Log f = f

-- | Empty log.
emptyLog :: forall n a f. (Cons f (Post n a)) => f
emptyLog = consNil @f @(Post n a)

-- | Commit a post to the log.
post :: (Cons f (Post n a)) => Post n a -> f -> f
post = cons

-- | Read every post addressed to any subscription, oldest-first.
--
-- >>> let p0 = mkPost "a" ["me"] (1 :: Int); p1 = mkPost "b" ["me"] (2 :: Int)
-- >>> map body (watch @String @Int @[Post String Int] ["me"] (post p1 (post p0 (emptyLog @String @Int @[Post String Int]))))
-- [1,2]
watch :: forall n a f. (Eq n, Uncons f (Post n a)) => [n] -> f -> [Post n a]
watch subs = go []
  where
    go acc stream =
      case uncons stream of
        That _ -> acc
        This p -> if deliversTo p subs then p : acc else acc
        These p rest -> go (if deliversTo p subs then p : acc else acc) rest

-- | Addressed unread-post stream and its subscriptions. The constructor is
-- private; use 'emptyInbox', 'appendInbox', and 'unconsInbox'.
newtype Inbox n f = Inbox {unInbox :: ([n], f)}
  deriving (Show, Eq)

-- | Empty inbox for the supplied subscriptions.
emptyInbox :: forall n a f. (Uncons f (Post n a)) => [n] -> Inbox n f
emptyInbox subs = Inbox (subs, nil @f @(Post n a))

-- | Append a post at the oldest-first read end's tail.
appendInbox :: (Snoc f (Post n a)) => Post n a -> Inbox n f -> Inbox n f
appendInbox p (Inbox (subs, f)) = Inbox (subs, snoc f p)

-- | Primary subscription, if one was supplied.
inboxWho :: Inbox n f -> Maybe n
inboxWho = listToMaybe . fst . unInbox

-- | All subscriptions for the inbox.
inboxSubs :: Inbox n f -> [n]
inboxSubs = fst . unInbox

-- | Channel posts deliver by channel membership. Unchannelled posts deliver
-- when the audience intersects the subscriptions.
--
-- An audience element is just a name: there is no null, discard or broadcast
-- sentinel in the predicate, so an empty audience delivers nowhere. The legacy
-- convention in which a single empty recipient means "nobody" lives in
-- `Circuit.Parser.Framing`, the wire codec, which decodes that audience as an
-- empty one before it reaches a post; it is not part of this predicate.
deliversTo :: (Eq n) => Post n a -> [n] -> Bool
deliversTo p subs =
  case channel p of
    Just c -> c `elem` subs
    Nothing -> any (`elem` to p) subs

-- | Peel the oldest addressed post, discarding skipped non-matching posts.
-- Empty and exhausted inboxes return 'That'.
unconsInbox :: forall n a f. (Eq n, Uncons f (Post n a)) => Inbox n f -> These (Post n a) (Inbox n f)
unconsInbox (Inbox (subs, f)) = go f
  where
    go stream =
      case uncons stream of
        That rest -> That (Inbox (subs, rest))
        This p
          | deliversTo p subs -> This p
          | otherwise -> That (emptyInbox @n @a subs)
        These p rest
          | deliversTo p subs -> These p (Inbox (subs, rest))
          | otherwise -> go rest
