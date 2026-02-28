# Hydrogen.Query

Data fetching with caching, deduplication, and stale-while-revalidate.

Inspired by TanStack Query, designed for PureScript/Halogen applications.

## Overview

```purescript
import Hydrogen.Query as Q
import Hydrogen.Data.RemoteData as RD

-- Create a query client (once, at app startup)
client <- Q.newClient

-- Fetch data with automatic caching
state <- Q.query client
  { key: ["user", userId]
  , fetch: Api.getUser config userId
  }

-- The state contains RemoteData + metadata
-- state :: { data :: RemoteData String User, isStale :: Boolean, isFetching :: Boolean }

-- Render based on the RemoteData
case state.data of
  RD.NotAsked -> mempty
  RD.Loading -> loadingSpinner
  RD.Failure err -> errorCard err
  RD.Success user -> renderUser user

-- Or use fold
Q.foldData state
  { notAsked: mempty
  , loading: loadingSpinner
  , failure: errorCard
  , success: renderUser
  }

-- Show stale data with refresh indicator
when (state.isFetching && Q.hasData state) $
  renderWithRefreshing (Q.getData state)
```

## Design

Query state is split into two concerns:

1. **RemoteData e a** — The core data state (NotAsked, Loading, Failure, Success).
   This is a **lawful Monad**, so you can use `do` notation and all standard combinators.

2. **QueryState e a** — A record with metadata:
   ```purescript
   type QueryState e a =
     { data :: RemoteData e a
     , isStale :: Boolean      -- Data exists but may be outdated
     , isFetching :: Boolean   -- Currently fetching (initial or refetch)
     }
   ```

This design mirrors TanStack Query where `data` and `isFetching` are separate.
You can show stale data while a background refetch is in progress.

### Why This Design?

Previous versions used a 5-state `QueryResult` type that tried to encode staleness
in the sum type itself (`QueryRefetching a`, `QueryError e (Maybe a)`). This broke
the Monad laws:

```purescript
-- Monad right-identity law: m >>= pure ≡ m
QueryRefetching 42 >>= pure = QuerySuccess 42 ≠ QueryRefetching 42  -- BROKEN!
```

By using the lawful 4-state `RemoteData` + separate metadata, we get:
- **Full Monad instance** — use `do` notation freely
- **Better composability** — combine queries with standard operators
- **Clear separation** — data state vs. fetch state

## Core Concepts

### Query Keys

Every query has a key — an array of strings that uniquely identifies it:

```purescript
["user", "123"]           -- User with ID 123
["users", "list"]         -- List of all users
["posts", "user:123"]     -- Posts for user 123
["search", "query:foo"]   -- Search results for "foo"
```

Keys are used for:
- **Caching**: Same key = same cached data
- **Deduplication**: Concurrent requests to same key share one fetch
- **Invalidation**: Invalidate by prefix (`["user"]` invalidates all user queries)

### RemoteData States

```
NotAsked      -- No request made yet
    │
    ▼
Loading       -- Fetch in progress
    │
    ├──▶ Success a    -- Fetch succeeded
    │
    └──▶ Failure e    -- Fetch failed
```

### QueryState Metadata

In addition to the `RemoteData` in `state.data`, QueryState tracks:

- `isStale: Boolean` — Data exists but is past its stale time
- `isFetching: Boolean` — A fetch is currently in progress

This allows patterns like:

```purescript
-- Show stale data with a "refreshing" indicator
if state.isFetching && Q.hasData state
  then renderData (Q.getData state) <> refreshingBadge
  else case state.data of ...
```

## Basic Usage

### Creating a Client

```purescript
main :: Effect Unit
main = do
  -- Default options: staleTime=0, cacheTime=5min
  client <- Q.newClient
  
  -- Or with custom options
  client <- Q.newClientWith
    { staleTime: Milliseconds 30000.0   -- Fresh for 30s
    , cacheTime: Milliseconds 600000.0  -- Keep in cache 10min
    }
  
  -- Pass client through your app (via context, props, etc.)
  runHalogenAff $ runUI (component client) ...
```

### Simple Query

```purescript
fetchUser :: Q.QueryClient -> String -> Aff (Q.QueryState String User)
fetchUser client userId = Q.query client
  { key: ["user", userId]
  , fetch: Api.getUser config userId
  , staleTime: Nothing     -- Use client default
  , retry: 3               -- Retry 3 times on failure
  , retryDelay: Milliseconds 1000.0
  }
```

### Conditional Fetching

```purescript
-- Only fetch if we have a userId
state <- Q.queryWith client opts { enabled: userId /= "" }
```

### Prefetching

```purescript
-- Fetch in background (for hover prefetch, etc.)
Q.prefetch client
  { key: ["user", nextUserId]
  , fetch: Api.getUser config nextUserId
  , ...
  }
```

## Cache Operations

### Manual Cache Updates

```purescript
-- Optimistically update after mutation
handleSubmit newUser = do
  -- Update cache immediately
  liftEffect $ Q.setQueryData client ["user", newUser.id] newUser
  
  -- Then do the actual mutation
  result <- Api.updateUser config newUser
  
  -- If it failed, invalidate to refetch
  when (isLeft result) $
    liftEffect $ Q.invalidate client ["user", newUser.id]
```

### Invalidation

```purescript
-- Invalidate specific query
Q.invalidateExact client ["user", "123"]

-- Invalidate all queries matching prefix
Q.invalidate client ["user"]  -- All user queries
Q.invalidate client ["posts"] -- All post queries

-- Nuclear option
Q.invalidateAll client
```

### Reading Cache

```purescript
-- Check if we have cached data
mUser <- Q.getQueryData client ["user", "123"]
case mUser of
  Just user -> log $ "Cached: " <> user.name
  Nothing -> log "Not in cache"
```

## Combining Queries

Because `RemoteData` is a **lawful Monad**, you can combine queries naturally:

### Using ado (Applicative — parallel semantics)

```purescript
renderDashboard :: Aff (RemoteData String DashboardData)
renderDashboard = do
  userState <- Q.query client userOpts
  postsState <- Q.query client postsOpts
  statsState <- Q.query client statsOpts
  
  -- Extract RemoteData and combine with ado
  pure $ ado
    user <- userState.data
    posts <- postsState.data
    stats <- statsState.data
    in { user, posts, stats }
```

### Using do (Monad — sequential semantics)

```purescript
-- Dependent fetches in RemoteData
let result :: RemoteData String Dashboard
    result = do
      user <- userState.data
      posts <- postsState.data
      pure $ makeDashboard user posts
```

### Using applicative operators

```purescript
mkDashboard <$> userState.data <*> postsState.data <*> statsState.data
  where
  mkDashboard user posts stats = { user, posts, stats }
```

### State Propagation

When combining RemoteData values:

| Combined states | Result |
|-----------------|--------|
| All `Success` | `Success` |
| Any `Failure` | `Failure` (first one wins) |
| Any `Loading` (no failures) | `Loading` |
| Any `NotAsked` (no failures/loading) | `NotAsked` |

## Pagination

```purescript
type Page = { items :: Array Item, nextCursor :: Maybe String }

pagedOpts :: Q.PagedQueryOptions Page
pagedOpts =
  { key: ["items", "list"]
  , fetch: \cursor -> Api.listItems config { cursor, limit: 20 }
  , getNextPageParam: _.nextCursor
  }

-- Initial fetch
state <- Q.queryPaged client pagedOpts

-- Load more
state' <- Q.fetchNextPage client pagedOpts state

-- Check if more available
case state'.data of
  RD.Success pages | state'.hasNextPage -> showLoadMoreButton
  _ -> mempty
```

## Request Batching

For DataLoader-style batching (e.g., fetch N users in one request):

```purescript
-- Create a batcher
userBatcher <- Q.newBatcher
  { batchFn: \ids -> Api.getUsersByIds config ids
  , maxBatchSize: 100
  , batchDelay: Milliseconds 10.0  -- Wait 10ms to collect requests
  }

-- Load single user (batched with concurrent requests)
result <- Q.load userBatcher "user-123"

-- Load multiple
results <- Q.loadMany userBatcher ["user-1", "user-2", "user-3"]
```

## Helper Functions

### Extracting Data from QueryState

```purescript
Q.getData state        -- Maybe a (from Success only)
Q.getError state       -- Maybe e (from Failure only)
Q.hasData state        -- Boolean
Q.withDefaultData [] state  -- Use default if no data
```

### Pattern Matching with foldData

```purescript
Q.foldData
  { notAsked: HH.text "Click to load"
  , loading: loadingSpinner
  , failure: \e -> errorCard e
  , success: \a -> renderData a
  }
  state
```

### Handling Stale-While-Revalidate

```purescript
renderQuery :: forall a. Q.QueryState String a -> (a -> HTML) -> HTML
renderQuery state render =
  if state.isFetching && Q.hasData state
    -- Show stale data with loading indicator
    then HH.div_
      [ maybe mempty render (Q.getData state)
      , refreshingBadge
      ]
    -- Normal render
    else Q.foldData
      { notAsked: mempty
      , loading: loadingSpinner
      , failure: errorCard
      , success: render
      }
      state
```

## RemoteData Directly

The `Hydrogen.Data.RemoteData` module is re-exported from `Hydrogen.Query`.
You can also import it directly:

```purescript
import Hydrogen.Data.RemoteData (RemoteData(..))
import Hydrogen.Data.RemoteData as RD

-- Construction
RD.fromEither (Right 42)  -- Success 42
RD.fromEither (Left "err")  -- Failure "err"

-- Predicates
RD.isSuccess (Success 42)  -- true
RD.isLoading Loading       -- true

-- Elimination
RD.fold
  { notAsked: "..."
  , loading: "..."
  , failure: \e -> "..."
  , success: \a -> "..."
  }
  remoteData

RD.withDefault 0 (Success 42)  -- 42
RD.withDefault 0 Loading       -- 0

-- Combining
RD.map2 (+) (Success 1) (Success 2)  -- Success 3
RD.map3 f ra rb rc
RD.map4 f ra rb rc rd
RD.sequence [Success 1, Success 2]   -- Success [1, 2]
```

## Migration from QueryResult

If you were using the old 5-state `QueryResult`, here's how to migrate:

| Old (QueryResult) | New (QueryState + RemoteData) |
|-------------------|-------------------------------|
| `QueryIdle` | `state.data == NotAsked` |
| `QueryLoading` | `state.data == Loading` |
| `QuerySuccess a` | `state.data == Success a` |
| `QueryError e Nothing` | `state.data == Failure e` |
| `QueryRefetching a` | `state.data == Success a` + `state.isFetching == true` |
| `QueryError e (Just a)` | `state.data == Success a` + `state.isStale == true` |

Key changes:
- Extract `.data` to get the `RemoteData` for Monad operations
- Check `isFetching` and `isStale` separately for UI state
- Use `foldData` instead of `fold` (same signature, works on QueryState)
