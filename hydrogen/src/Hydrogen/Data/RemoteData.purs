-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // data // remote-data
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A data type for values fetched from a remote source.
-- |
-- | RemoteData represents the complete lifecycle of an async request:
-- |
-- | ```
-- | NotAsked --> Loading --> Success a
-- |                    \--> Failure e
-- | ```
-- |
-- | This eliminates impossible states. You cannot have both an error and data.
-- | You cannot forget to handle the loading state. The compiler enforces it.
-- |
-- | ## Laws
-- |
-- | RemoteData forms a lawful Monad where:
-- | - `pure = Success`
-- | - `>>=` short-circuits on NotAsked, Loading, Failure (left-to-right)
-- |
-- | The Applicative instance is "first failure" semantics:
-- | - If any argument is `Failure`, the result is `Failure`
-- | - If any argument is `Loading`, the result is `Loading`  
-- | - If any argument is `NotAsked`, the result is `NotAsked`
-- |
-- | Priority order: Failure > Loading > NotAsked > Success
-- |
-- | ## Semigroup
-- |
-- | `<>` takes the "most progressed" value:
-- | - `Success a <> Success b = Success b` (right-biased)
-- | - `Success a <> Loading = Success a` (success wins)
-- | - `Failure e <> Success a = Success a` (success wins over failure)
-- | - `Loading <> Failure e = Failure e` (failure wins over loading)
-- |
-- | This means you can use `<>` to "upgrade" state as responses arrive.
module Hydrogen.Data.RemoteData
  ( RemoteData(NotAsked, Loading, Failure, Success)
  -- Construction
  , fromEither
  , fromMaybe
  -- Elimination
  , toEither
  , toMaybe
  , fold
  , withDefault
  -- Predicates
  , isNotAsked
  , isLoading
  , isFailure
  , isSuccess
  -- Transformations
  , mapError
  -- Combining
  , map2
  , map3
  , map4
  , sequence
  , traverse
  ) where

import Prelude
  ( class Applicative
  , class Apply
  , class Bind
  , class Eq
  , class Functor
  , class Monad
  , class Monoid
  , class Ord
  , class Semigroup
  , class Show
  , mempty
  , pure
  , show
  , (<>)
  , (<$>)
  , (<*>)
  )

import Control.Alt (class Alt)
import Control.Plus (class Plus)
import Data.Bifunctor (class Bifunctor)
import Data.Either (Either(Left, Right))
import Data.Foldable (class Foldable)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Maybe (maybe) as Maybe
import Data.Traversable (class Traversable)
import Data.Traversable (sequence, traverse) as T

-- | Represents data that is fetched from a remote source.
-- |
-- | - `NotAsked` - Request has not been made yet
-- | - `Loading` - Request is in flight
-- | - `Failure e` - Request failed with error `e`
-- | - `Success a` - Request succeeded with value `a`
data RemoteData e a
  = NotAsked
  | Loading
  | Failure e
  | Success a

derive instance eqRemoteData :: (Eq e, Eq a) => Eq (RemoteData e a)
derive instance ordRemoteData :: (Ord e, Ord a) => Ord (RemoteData e a)
derive instance functorRemoteData :: Functor (RemoteData e)

instance showRemoteData :: (Show e, Show a) => Show (RemoteData e a) where
  show NotAsked = "NotAsked"
  show Loading = "Loading"
  show (Failure e) = "(Failure " <> show e <> ")"
  show (Success a) = "(Success " <> show a <> ")"

-- | First-failure Applicative semantics.
-- | Priority: Failure > Loading > NotAsked > Success
instance applyRemoteData :: Apply (RemoteData e) where
  apply (Success f) (Success a) = Success (f a)
  apply (Failure e) _ = Failure e
  apply _ (Failure e) = Failure e
  apply Loading _ = Loading
  apply _ Loading = Loading
  apply NotAsked _ = NotAsked
  apply _ NotAsked = NotAsked

instance applicativeRemoteData :: Applicative (RemoteData e) where
  pure = Success

instance bindRemoteData :: Bind (RemoteData e) where
  bind NotAsked _ = NotAsked
  bind Loading _ = Loading
  bind (Failure e) _ = Failure e
  bind (Success a) f = f a

instance monadRemoteData :: Monad (RemoteData e)

-- | Bifunctor: map over both error and success types
instance bifunctorRemoteData :: Bifunctor RemoteData where
  bimap _ _ NotAsked = NotAsked
  bimap _ _ Loading = Loading
  bimap f _ (Failure e) = Failure (f e)
  bimap _ g (Success a) = Success (g a)

-- | Alt: first success wins, NotAsked is identity
-- | 
-- | Laws:
-- | - `NotAsked <|> x = x` (left identity for Plus)
-- | - `Success a <|> _ = Success a` (success is absorbing on left)
-- | - `_ <|> Success a = Success a` (success wins)
-- |
-- | For non-Success: prefer the "more progressed" state
-- | Priority: Failure > Loading > NotAsked
instance altRemoteData :: Alt (RemoteData e) where
  alt NotAsked r = r  -- NotAsked is identity (must come first for Plus law)
  alt l NotAsked = l  -- NotAsked is identity (right side too)
  alt (Success a) _ = Success a
  alt _ (Success a) = Success a
  alt (Failure e) _ = Failure e  -- Failure > Loading
  alt _ (Failure e) = Failure e
  alt Loading Loading = Loading

-- | Plus: NotAsked is the identity for Alt
instance plusRemoteData :: Plus (RemoteData e) where
  empty = NotAsked

-- | Semigroup: combine by taking most-progressed state
-- | Success > Failure > Loading > NotAsked (for structure)
-- | When both are Success, right-biased (takes second value)
instance semigroupRemoteData :: Semigroup a => Semigroup (RemoteData e a) where
  append (Success a) (Success b) = Success (a <> b)
  append (Success a) _ = Success a
  append _ (Success a) = Success a
  append (Failure e) _ = Failure e
  append _ (Failure e) = Failure e
  append Loading _ = Loading
  append _ Loading = Loading
  append NotAsked NotAsked = NotAsked

-- | Monoid: NotAsked is identity
instance monoidRemoteData :: Semigroup a => Monoid (RemoteData e a) where
  mempty = NotAsked

-- | Foldable: only Success contains a value to fold
instance foldableRemoteData :: Foldable (RemoteData e) where
  foldr f b = case _ of
    Success a -> f a b
    _ -> b
  foldl f b = case _ of
    Success a -> f b a
    _ -> b
  foldMap f = case _ of
    Success a -> f a
    _ -> mempty

-- | Traversable: traverse the success case
instance traversableRemoteData :: Traversable (RemoteData e) where
  traverse f = case _ of
    NotAsked -> pure NotAsked
    Loading -> pure Loading
    Failure e -> pure (Failure e)
    Success a -> Success <$> f a
  sequence = case _ of
    NotAsked -> pure NotAsked
    Loading -> pure Loading
    Failure e -> pure (Failure e)
    Success fa -> Success <$> fa

-- =============================================================================
--                                                               // construction
-- =============================================================================

-- | Convert from Either. Left becomes Failure, Right becomes Success.
fromEither :: forall e a. Either e a -> RemoteData e a
fromEither (Left e) = Failure e
fromEither (Right a) = Success a

-- | Convert from Maybe. Nothing becomes the provided error, Just becomes Success.
fromMaybe :: forall e a. e -> Maybe a -> RemoteData e a
fromMaybe e = Maybe.maybe (Failure e) Success

-- =============================================================================
--                                                                // elimination
-- =============================================================================

-- | Convert to Either. NotAsked and Loading become Left with provided error.
toEither :: forall e a. e -> RemoteData e a -> Either e a
toEither pending = case _ of
  NotAsked -> Left pending
  Loading -> Left pending
  Failure e -> Left e
  Success a -> Right a

-- | Extract Success value as Maybe. Everything else is Nothing.
toMaybe :: forall e a. RemoteData e a -> Maybe a
toMaybe (Success a) = Just a
toMaybe _ = Nothing

-- | Eliminate RemoteData by providing handlers for each case.
-- |
-- | ```purescript
-- | fold 
-- |   { notAsked: HH.text "Click to load"
-- |   , loading: spinner
-- |   , failure: \e -> errorMessage e
-- |   , success: \data -> renderData data
-- |   }
-- |   remoteData
-- | ```
fold
  :: forall e a r
   . { notAsked :: r
     , loading :: r
     , failure :: e -> r
     , success :: a -> r
     }
  -> RemoteData e a
  -> r
fold handlers = case _ of
  NotAsked -> handlers.notAsked
  Loading -> handlers.loading
  Failure e -> handlers.failure e
  Success a -> handlers.success a

-- | Get Success value or fall back to default.
withDefault :: forall e a. a -> RemoteData e a -> a
withDefault def = case _ of
  Success a -> a
  _ -> def

-- =============================================================================
--                                                                 // predicates
-- =============================================================================

isNotAsked :: forall e a. RemoteData e a -> Boolean
isNotAsked NotAsked = true
isNotAsked _ = false

isLoading :: forall e a. RemoteData e a -> Boolean
isLoading Loading = true
isLoading _ = false

isFailure :: forall e a. RemoteData e a -> Boolean
isFailure (Failure _) = true
isFailure _ = false

isSuccess :: forall e a. RemoteData e a -> Boolean
isSuccess (Success _) = true
isSuccess _ = false

-- =============================================================================
--                                                            // transformations
-- =============================================================================

-- | Map over the error type only.
mapError :: forall e1 e2 a. (e1 -> e2) -> RemoteData e1 a -> RemoteData e2 a
mapError _ NotAsked = NotAsked
mapError _ Loading = Loading
mapError f (Failure e) = Failure (f e)
mapError _ (Success a) = Success a

-- =============================================================================
--                                                                  // combining
-- =============================================================================

-- | Combine two RemoteData values. Both must succeed.
map2 :: forall e a b c. (a -> b -> c) -> RemoteData e a -> RemoteData e b -> RemoteData e c
map2 f ra rb = f <$> ra <*> rb

-- | Combine three RemoteData values. All must succeed.
map3 :: forall e a b c d. (a -> b -> c -> d) -> RemoteData e a -> RemoteData e b -> RemoteData e c -> RemoteData e d
map3 f ra rb rc = f <$> ra <*> rb <*> rc

-- | Combine four RemoteData values. All must succeed.
map4 :: forall e a b c d r. (a -> b -> c -> d -> r) -> RemoteData e a -> RemoteData e b -> RemoteData e c -> RemoteData e d -> RemoteData e r
map4 f ra rb rc rd = f <$> ra <*> rb <*> rc <*> rd

-- | Sequence an array of RemoteData into RemoteData of array.
-- | All must succeed for the result to be Success.
sequence :: forall e a. Array (RemoteData e a) -> RemoteData e (Array a)
sequence = T.sequence

-- | Traverse with a function that returns RemoteData.
traverse :: forall e a b. (a -> RemoteData e b) -> Array a -> RemoteData e (Array b)
traverse = T.traverse
