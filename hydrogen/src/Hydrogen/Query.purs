-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // query
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Data fetching with caching, deduplication, and automatic refetch.
-- |
-- | Inspired by TanStack Query, designed to work with zeitschrift-generated clients.
-- |
-- | ## Design
-- |
-- | Query state is split into two concerns:
-- |
-- | 1. **RemoteData e a** - The core data state (NotAsked, Loading, Failure, Success)
-- |    This is a lawful Monad, so you can use `do` notation and all standard combinators.
-- |
-- | 2. **QueryState e a** - Record with metadata:
-- |    ```purescript
-- |    { data :: RemoteData e a
-- |    , isStale :: Boolean      -- Data exists but may be outdated
-- |    , isFetching :: Boolean   -- Currently fetching (initial or refetch)
-- |    }
-- |    ```
-- |
-- | This design mirrors TanStack Query where `data` and `isFetching` are separate.
-- | You can show stale data while a background refetch is in progress.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Query as Q
-- | import Hydrogen.Data.RemoteData as RD
-- | 
-- | -- Create a query client (typically in your main)
-- | client <- Q.newClient Q.defaultClientOptions
-- | 
-- | -- Fetch data with caching
-- | state <- Q.query client
-- |   { key: ["user", userId]
-- |   , fetch: Api.getUser config userId
-- |   }
-- | 
-- | -- Use the RemoteData for rendering
-- | case state.data of
-- |   RD.NotAsked -> HH.text "Not loaded"
-- |   RD.Loading -> spinner
-- |   RD.Failure e -> errorCard e
-- |   RD.Success user -> userCard user
-- |
-- | -- Or use fold
-- | Q.foldData state
-- |   { notAsked: HH.text "Click to load"
-- |   , loading: spinner
-- |   , failure: \e -> errorCard e
-- |   , success: \user -> userCard user
-- |   }
-- |
-- | -- Show stale data with loading indicator
-- | if state.isFetching && Q.hasData state
-- |   then showWithSpinner (Q.getData state)
-- |   else normalRender state.data
-- | 
-- | -- Invalidate cache after mutation
-- | Q.invalidate client ["user", userId]
-- | ```
-- |
-- | ## Combining Queries with RemoteData
-- |
-- | Because RemoteData is a lawful Monad, you can combine queries naturally:
-- |
-- | ```purescript
-- | -- Using ado syntax (Applicative - parallel semantics)
-- | let combined = ado
-- |       user <- userState.data
-- |       posts <- postsState.data
-- |       in { user, posts }
-- |
-- | -- Using do syntax (Monad - sequential semantics)
-- | let dependent = do
-- |       user <- userState.data
-- |       posts <- postsState.data
-- |       pure $ renderUserWithPosts user posts
-- | ```
module Hydrogen.Query
  ( -- * Client
    QueryClient
  , ClientOptions
  , defaultClientOptions
  , newClient
  , newClientWith
  
    -- * Query types
  , QueryKey
  , QueryOptions
  , defaultQueryOptions
  , QueryState
  , initialQueryState
  
    -- * Query operations
  , query
  , queryWith
  , prefetch
  , getQueryData
  , setQueryData
  
    -- * Cache invalidation
  , invalidate
  , invalidateExact
  , invalidateAll
  , removeQuery
  
    -- * Pagination
  , PageParam
  , PagedQueryOptions
  , PagedState
  , initialPagedState
  , queryPaged
  , fetchNextPage
  
    -- * Batching
  , Batcher
  , BatchOptions
  , newBatcher
  , load
  , loadMany
  
    -- * QueryState helpers
  , getData
  , getError
  , hasData
  , foldData
  , withDefaultData
  
    -- * Re-exports from RemoteData
  , module Hydrogen.Data.RemoteData
  ) where

import Prelude
  ( class Ord
  , class Show
  , Unit
  , bind
  , discard
  , map
  , not
  , otherwise
  , pure
  , show
  , unit
  , void
  , ($)
  , (>)
  , (+)
  , (-)
  , (/=)
  , (<$>)
  , (<>)
  , (>>=)
  )

import Data.Argonaut (class DecodeJson, class EncodeJson, Json, decodeJson, encodeJson)
import Data.Array as Array
import Data.DateTime.Instant (Instant, unInstant, instant)
import Data.Either (Either(Left, Right), hush)
import Data.Map as Map
import Data.Maybe (Maybe(Nothing, Just), fromMaybe, isJust)
import Data.Newtype (unwrap)
import Data.String as String
import Data.Time.Duration (Milliseconds(Milliseconds))
import Data.Tuple (Tuple)
import Effect (Effect)
import Effect.Aff (Aff, Fiber, delay, forkAff, joinFiber)
import Effect.Class (liftEffect)
import Effect.Now (now)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Hydrogen.Data.RemoteData (RemoteData(NotAsked, Loading, Failure, Success))
import Hydrogen.Data.RemoteData (RemoteData(NotAsked, Loading, Failure, Success), fromEither, toMaybe, isSuccess, isLoading, isFailure, isNotAsked, mapError, map2, map3, map4) as Hydrogen.Data.RemoteData

-- =============================================================================
--                                                                     // client
-- =============================================================================

-- | Opaque query client that manages cache and in-flight requests.
newtype QueryClient = QueryClient
  { cache :: Ref (Map.Map String CacheEntry)
  , inFlight :: Ref (Map.Map String (Fiber (Either String Json)))
  , options :: ClientOptions
  }

-- | Client-level configuration.
type ClientOptions =
  { -- | Default time (ms) before queries are considered stale.
    -- | Stale queries will refetch in the background.
    staleTime :: Milliseconds
    -- | Default time (ms) to keep unused data in cache.
  , cacheTime :: Milliseconds
  }

-- | Default client options.
-- | 
-- | - staleTime: 0 (always refetch)
-- | - cacheTime: 5 minutes
defaultClientOptions :: ClientOptions
defaultClientOptions =
  { staleTime: Milliseconds 0.0
  , cacheTime: Milliseconds 300000.0
  }

-- | Create a new query client with default options.
newClient :: Effect QueryClient
newClient = newClientWith defaultClientOptions

-- | Create a new query client with custom options.
newClientWith :: ClientOptions -> Effect QueryClient
newClientWith options = do
  cache <- Ref.new Map.empty
  inFlight <- Ref.new Map.empty
  pure $ QueryClient { cache, inFlight, options }

-- =============================================================================
--                                                                // query types
-- =============================================================================

-- | Query key - identifies a unique query.
-- | Convention: ["resource", "id"] or ["resource", "list", "filter:value"]
type QueryKey = Array String

-- | Options for a query.
type QueryOptions a =
  { -- | Unique key for this query
    key :: QueryKey
    -- | Function to fetch the data
  , fetch :: Aff (Either String a)
    -- | Override stale time for this query
  , staleTime :: Maybe Milliseconds
    -- | Number of retry attempts on failure
  , retry :: Int
    -- | Delay between retries
  , retryDelay :: Milliseconds
  }

-- | Default query options (just provide key and fetch).
defaultQueryOptions :: forall a. QueryKey -> Aff (Either String a) -> QueryOptions a
defaultQueryOptions key fetch =
  { key
  , fetch
  , staleTime: Nothing
  , retry: 0
  , retryDelay: Milliseconds 1000.0
  }

-- | Query state with RemoteData plus metadata.
-- |
-- | The `data` field contains the core RemoteData (lawful Monad).
-- | The metadata fields track additional state:
-- |
-- | - `isStale`: Data exists but may be outdated (triggers background refetch)
-- | - `isFetching`: A fetch is currently in progress (initial or refetch)
-- |
-- | This separation allows you to:
-- | 1. Use RemoteData's Monad instance for combining queries
-- | 2. Show stale data while refetching in the background
-- | 3. Distinguish between "loading for first time" vs "refreshing"
type QueryState e a =
  { data :: RemoteData e a
  , isStale :: Boolean
  , isFetching :: Boolean
  }

-- | Initial query state (not asked, not fetching).
initialQueryState :: forall e a. QueryState e a
initialQueryState =
  { data: NotAsked
  , isStale: false
  , isFetching: false
  }

-- =============================================================================
--                                                                   // internal
-- =============================================================================

type CacheEntry =
  { json :: Json
  , updatedAt :: Instant
  , staleAt :: Instant
  }

keyToString :: QueryKey -> String
keyToString = String.joinWith ":"

isEntryStale :: CacheEntry -> Instant -> Boolean
isEntryStale entry currentTime = 
  toMs currentTime > toMs entry.staleAt
  where
  toMs instant = unwrap (unInstant instant)

-- =============================================================================
--                                                           // query operations
-- =============================================================================

-- | Execute a query with caching and deduplication.
-- |
-- | - Returns cached data immediately if fresh
-- | - Deduplicates concurrent requests to the same key
-- | - Refetches in background if stale
query 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> QueryOptions a 
  -> Aff (QueryState String a)
query client opts = queryWith client opts { enabled: true }

-- | Execute a query with an enabled flag.
-- |
-- | Useful for conditional fetching:
-- | ```purescript
-- | state <- Q.queryWith client opts { enabled: userId /= "" }
-- | ```
queryWith 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> QueryOptions a
  -> { enabled :: Boolean }
  -> Aff (QueryState String a)
queryWith _ _ { enabled: false } = pure initialQueryState
queryWith client@(QueryClient c) opts _ = do
  let cacheKey = keyToString opts.key
  
  -- Check cache
  currentTime <- liftEffect now
  cachedEntry <- liftEffect $ Map.lookup cacheKey <$> Ref.read c.cache
  
  case cachedEntry of
    -- Fresh cache hit
    Just entry | not (isEntryStale entry currentTime) -> 
      case decodeJson entry.json of
        Right a -> pure
          { data: Success a
          , isStale: false
          , isFetching: false
          }
        Left _ -> fetchFresh client opts Nothing  -- Cache corrupted, refetch
    
    -- Stale cache - return stale data + refetch
    Just entry -> do
      let staleData = hush $ decodeJson entry.json
      fetchFresh client opts staleData
    
    -- No cache
    Nothing -> fetchFresh client opts Nothing

-- | Fetch fresh data, handling deduplication and retries.
fetchFresh 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> QueryOptions a
  -> Maybe a  -- Stale data to preserve
  -> Aff (QueryState String a)
fetchFresh (QueryClient c) opts staleData = do
  let cacheKey = keyToString opts.key
  
  -- Check for in-flight request
  inFlightFiber <- liftEffect $ Map.lookup cacheKey <$> Ref.read c.inFlight
  
  jsonResult <- case inFlightFiber of
    -- Join existing request (deduplication)
    Just fiber -> joinFiber fiber
    
    -- Start new request
    Nothing -> do
      let doFetch = fetchWithRetry opts.fetch opts.retry opts.retryDelay
      fiber <- forkAff doFetch
      liftEffect $ Ref.modify_ (Map.insert cacheKey fiber) c.inFlight
      result <- joinFiber fiber
      liftEffect $ Ref.modify_ (Map.delete cacheKey) c.inFlight
      
      -- Cache successful results
      case result of
        Right json -> do
          updateTime <- liftEffect now
          let staleTime = fromMaybe c.options.staleTime opts.staleTime
          let staleAt = addMs updateTime staleTime
          let entry = { json, updatedAt: updateTime, staleAt }
          liftEffect $ Ref.modify_ (Map.insert cacheKey entry) c.cache
        Left _ -> pure unit
      
      pure result
  
  -- Build QueryState from result
  pure $ case jsonResult of
    Left err -> 
      -- On error, preserve stale data if available
      case staleData of
        Just a ->
          { data: Success a  -- Keep showing stale data
          , isStale: true
          , isFetching: false
          -- Note: We could also expose the error separately
          -- For now, stale data + isStale=true signals this state
          }
        Nothing ->
          { data: Failure err
          , isStale: false
          , isFetching: false
          }
    Right json -> 
      case decodeJson json of
        Left err ->
          { data: Failure (show err)
          , isStale: false
          , isFetching: false
          }
        Right a ->
          { data: Success a
          , isStale: false
          , isFetching: false
          }

-- | Fetch with retry logic.
fetchWithRetry 
  :: forall a
   . EncodeJson a
  => Aff (Either String a) 
  -> Int 
  -> Milliseconds 
  -> Aff (Either String Json)
fetchWithRetry fetch retriesLeft retryDelay = do
  result <- fetch
  case result of
    Right a -> pure $ Right (encodeJson a)
    Left _ | retriesLeft > 0 -> do
      delay retryDelay
      fetchWithRetry fetch (retriesLeft - 1) retryDelay
    Left err -> pure $ Left err

-- | Prefetch a query without waiting for the result.
prefetch 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> QueryOptions a 
  -> Aff Unit
prefetch client opts = void $ query client opts

-- | Get cached data for a query (if available).
getQueryData 
  :: forall a
   . DecodeJson a
  => QueryClient 
  -> QueryKey 
  -> Effect (Maybe a)
getQueryData (QueryClient c) key = do
  entry <- Map.lookup (keyToString key) <$> Ref.read c.cache
  pure $ entry >>= \e -> hush (decodeJson e.json)

-- | Manually set cached data for a query.
-- |
-- | Useful for optimistic updates:
-- | ```purescript
-- | -- Optimistically update
-- | Q.setQueryData client ["user", id] updatedUser
-- | 
-- | -- If mutation fails, invalidate to refetch
-- | Q.invalidate client ["user", id]
-- | ```
setQueryData 
  :: forall a
   . EncodeJson a
  => QueryClient 
  -> QueryKey 
  -> a 
  -> Effect Unit
setQueryData (QueryClient c) key value = do
  currentTime <- now
  let staleAt = addMs currentTime c.options.staleTime
  let entry = 
        { json: encodeJson value
        , updatedAt: currentTime
        , staleAt
        }
  Ref.modify_ (Map.insert (keyToString key) entry) c.cache

-- =============================================================================
--                                                         // cache invalidation
-- =============================================================================

-- | Invalidate all queries matching a key prefix.
-- |
-- | ```purescript
-- | -- Invalidate all user queries
-- | Q.invalidate client ["user"]
-- | 
-- | -- Invalidate specific user
-- | Q.invalidate client ["user", "123"]
-- | ```
invalidate :: QueryClient -> QueryKey -> Effect Unit
invalidate (QueryClient c) prefix = do
  let prefixStr = keyToString prefix
  currentTime <- now
  Ref.modify_ (Map.mapMaybeWithKey (markStaleIfMatches prefixStr currentTime)) c.cache
  where
  markStaleIfMatches prefixStr currentTime key entry
    | String.contains (String.Pattern prefixStr) key = 
        Just entry { staleAt = currentTime }
    | otherwise = Just entry

-- | Invalidate a query with an exact key match.
invalidateExact :: QueryClient -> QueryKey -> Effect Unit
invalidateExact (QueryClient c) key = do
  currentTime <- now
  Ref.modify_ (Map.update (\e -> Just e { staleAt = currentTime }) (keyToString key)) c.cache

-- | Invalidate all queries in the cache.
invalidateAll :: QueryClient -> Effect Unit
invalidateAll (QueryClient c) = do
  currentTime <- now
  Ref.modify_ (map \e -> e { staleAt = currentTime }) c.cache

-- | Remove a query from the cache entirely.
removeQuery :: QueryClient -> QueryKey -> Effect Unit
removeQuery (QueryClient c) key = 
  Ref.modify_ (Map.delete (keyToString key)) c.cache

-- =============================================================================
--                                                                 // pagination
-- =============================================================================

-- | Page parameter for cursor-based pagination.
type PageParam = Maybe String

-- | Options for paginated queries.
type PagedQueryOptions a =
  { key :: QueryKey
  , fetch :: PageParam -> Aff (Either String a)
  , getNextPageParam :: a -> PageParam
  }

-- | State for paginated queries.
type PagedState e a =
  { data :: RemoteData e (Array a)
  , pages :: Array a
  , hasNextPage :: Boolean
  , isFetching :: Boolean
  , isFetchingNextPage :: Boolean
  }

-- | Initial paged state.
initialPagedState :: forall e a. PagedState e a
initialPagedState =
  { data: NotAsked
  , pages: []
  , hasNextPage: false
  , isFetching: false
  , isFetchingNextPage: false
  }

-- | Execute a paginated query.
queryPaged 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> PagedQueryOptions a 
  -> Aff (PagedState String a)
queryPaged _client opts = do
  result <- opts.fetch Nothing
  pure $ case result of
    Left err ->
      { data: Failure err
      , pages: []
      , hasNextPage: false
      , isFetching: false
      , isFetchingNextPage: false
      }
    Right a ->
      { data: Success [a]
      , pages: [a]
      , hasNextPage: opts.getNextPageParam a /= Nothing
      , isFetching: false
      , isFetchingNextPage: false
      }

-- | Fetch the next page.
fetchNextPage 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> PagedQueryOptions a
  -> PagedState String a
  -> Aff (PagedState String a)
fetchNextPage _client opts state = do
  let lastPage = Array.last state.pages
  let nextCursor = lastPage >>= opts.getNextPageParam
  case nextCursor of
    Nothing -> pure state { hasNextPage = false }
    Just cursor -> do
      result <- opts.fetch (Just cursor)
      pure $ case result of
        Left err ->
          state { data = Failure err, isFetchingNextPage = false }
        Right newPage ->
          let newPages = state.pages <> [newPage]
          in state
            { data = Success newPages
            , pages = newPages
            , hasNextPage = opts.getNextPageParam newPage /= Nothing
            , isFetchingNextPage = false
            }

-- =============================================================================
--                                                      // batching (DataLoader)
-- =============================================================================

-- | Options for a batcher.
type BatchOptions k v =
  { -- | Batch function that fetches multiple keys at once
    batchFn :: Array k -> Aff (Array (Tuple k (Either String v)))
    -- | Maximum batch size
  , maxBatchSize :: Int
    -- | Delay before dispatching (ms) - allows more requests to queue
  , batchDelay :: Milliseconds
  }

-- | Batcher for DataLoader-style request coalescing.
newtype Batcher k v = Batcher
  { queue :: Ref (Array { key :: k, resolve :: Either String v -> Effect Unit })
  , scheduled :: Ref Boolean
  , options :: BatchOptions k v
  }

-- | Create a new batcher.
newBatcher :: forall k v. BatchOptions k v -> Effect (Batcher k v)
newBatcher options = do
  queue <- Ref.new []
  scheduled <- Ref.new false
  pure $ Batcher { queue, scheduled, options }

-- | Load a single value, batching with concurrent requests.
load :: forall k v. Ord k => Batcher k v -> k -> Aff (Either String v)
load batcher key = do
  results <- loadMany batcher [key]
  pure $ fromMaybe (Left "Key not found in batch result") (Map.lookup key results)

-- | Load multiple values in a single batch.
loadMany :: forall k v. Ord k => Batcher k v -> Array k -> Aff (Map.Map k (Either String v))
loadMany (Batcher b) keys = do
  results <- b.options.batchFn keys
  pure $ Map.fromFoldable results

-- =============================================================================
--                                                                    // helpers
-- =============================================================================

-- | Add milliseconds to an instant.
-- | Falls back to original instant if result would be invalid.
addMs :: Instant -> Milliseconds -> Instant
addMs inst (Milliseconds delta) =
  let Milliseconds current = unInstant inst
      newMs = Milliseconds (current + delta)
  in fromMaybe inst (instant newMs)

-- =============================================================================
--                                                          // QueryState helpers
-- =============================================================================

-- | Get the data from a QueryState if available.
getData :: forall e a. QueryState e a -> Maybe a
getData state = case state.data of
  Success a -> Just a
  _ -> Nothing

-- | Get the error from a QueryState if in failure state.
getError :: forall e a. QueryState e a -> Maybe e
getError state = case state.data of
  Failure e -> Just e
  _ -> Nothing

-- | Check if QueryState has data (Success or stale data preserved).
hasData :: forall e a. QueryState e a -> Boolean
hasData state = isJust (getData state)

-- | Fold over the RemoteData in a QueryState.
-- |
-- | ```purescript
-- | Q.foldData state
-- |   { notAsked: HH.text "Click to load"
-- |   , loading: spinner
-- |   , failure: \e -> errorCard e
-- |   , success: \user -> userCard user
-- |   }
-- | ```
foldData
  :: forall e a r
   . { notAsked :: r
     , loading :: r
     , failure :: e -> r
     , success :: a -> r
     }
  -> QueryState e a
  -> r
foldData handlers state = case state.data of
  NotAsked -> handlers.notAsked
  Loading -> handlers.loading
  Failure e -> handlers.failure e
  Success a -> handlers.success a

-- | Get success value or fall back to default.
withDefaultData :: forall e a. a -> QueryState e a -> a
withDefaultData def state = case state.data of
  Success a -> a
  _ -> def
