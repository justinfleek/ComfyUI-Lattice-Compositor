-- | Lattice.Services.Security.AuditLog.Query - Query functions
-- |
-- | @module Lattice.Services.Security.AuditLog.Query
-- | @description Functions for querying and exporting audit logs.
-- |
-- | All functions require a LoggingContext for Bridge access.
-- |
-- | Source: ui/src/services/security/auditLog.ts

module Lattice.Services.Security.AuditLog.Query
  ( -- * Query
    queryAuditLog
  , getAuditStats
    -- * Export
  , exportAuditLog
    -- * Maintenance
  , clearAuditLog
  ) where

import Prelude
import Effect.Aff (Aff, attempt)
import Effect.Class (liftEffect)
import Effect.Console (log, warn, error)
import Data.Argonaut.Core (stringify)
import Data.Argonaut.Encode (encodeJson)
import Data.Argonaut.Parser (jsonParser)
import Data.Array (length, catMaybes, filter, sortBy, take, drop)
import Data.Either (Either(..), hush)
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Ord (comparing)
import Data.Tuple (Tuple(..))
import Foreign.Object as Obj

import Lattice.Services.Security.AuditLog.Types
  ( AuditCategory
  , AuditSeverity
  , AuditLogEntry
  , AuditLogQuery
  , AuditLogStats
  , defaultQuery
  , categoryToString
  , severityToString
  , storeName
  , maxEntries
  )
import Lattice.Services.Security.AuditLog.Context
  ( LoggingContext
  , getSessionId
  , getBridgeClient
  , getCurrentISOTimestamp
  )
import Lattice.Services.Security.AuditLog.Encode (encodeEntryRecord)
import Lattice.Services.Security.AuditLog.Decode (decodeEntry)
import Lattice.Services.Security.AuditLog.Logging (logSecurityWarning)
import Lattice.Services.Bridge.Client as Bridge

-- ────────────────────────────────────────────────────────────────────────────
-- Query Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Query audit log entries
-- |
-- | @param ctx Logging context with Bridge client
-- | @param query Query parameters
-- | @returns Array of matching entries
queryAuditLog :: LoggingContext -> AuditLogQuery -> Aff (Array AuditLogEntry)
queryAuditLog ctx query = do
  let bridgeClient = getBridgeClient ctx
  result <- attempt $ Bridge.storageGetAll bridgeClient storeName
  case result of
    Left err -> do
      liftEffect $ warn ("[AUDIT] Query failed: " <> show err)
      pure []
    Right entryStrings -> do
      let parsedJsons = catMaybes (map (hush <<< jsonParser) entryStrings)
          allEntries = catMaybes (map decodeEntry parsedJsons)
          -- Apply query filters
          filtered = applyFilters query allEntries
          -- Sort by timestamp descending (newest first)
          sorted = sortBy (comparing (_.timestamp >>> negate')) filtered
          -- Apply pagination
          offset = fromMaybe 0 query.offset
          limit = fromMaybe maxEntries query.limit
          paginated = take limit (drop offset sorted)
      pure paginated
  where
    -- Negate for descending sort
    negate' :: String -> String
    negate' s = s  -- Timestamps are ISO 8601, lexicographic sort works

-- | Apply query filters to entries
applyFilters :: AuditLogQuery -> Array AuditLogEntry -> Array AuditLogEntry
applyFilters query entries = foldl applyFilter entries filters
  where
    filters =
      [ filterByCategory query.category
      , filterBySeverity query.severity
      , filterByTool query.toolName
      , filterBySession query.sessionId
      , filterByTimeRange query.startTime query.endTime
      ]
    
    applyFilter :: Array AuditLogEntry -> (Array AuditLogEntry -> Array AuditLogEntry) -> Array AuditLogEntry
    applyFilter es f = f es

filterByCategory :: Maybe AuditCategory -> Array AuditLogEntry -> Array AuditLogEntry
filterByCategory Nothing entries = entries
filterByCategory (Just cat) entries = filter (\e -> e.category == cat) entries

filterBySeverity :: Maybe AuditSeverity -> Array AuditLogEntry -> Array AuditLogEntry
filterBySeverity Nothing entries = entries
filterBySeverity (Just sev) entries = filter (\e -> e.severity == sev) entries

filterByTool :: Maybe String -> Array AuditLogEntry -> Array AuditLogEntry
filterByTool Nothing entries = entries
filterByTool (Just tool) entries = filter (\e -> e.toolName == Just tool) entries

filterBySession :: Maybe String -> Array AuditLogEntry -> Array AuditLogEntry
filterBySession Nothing entries = entries
filterBySession (Just sid) entries = filter (\e -> e.sessionId == sid) entries

filterByTimeRange :: Maybe String -> Maybe String -> Array AuditLogEntry -> Array AuditLogEntry
filterByTimeRange startTime endTime entries =
  let afterStart = case startTime of
        Nothing -> entries
        Just start -> filter (\e -> e.timestamp >= start) entries
      beforeEnd = case endTime of
        Nothing -> afterStart
        Just end -> filter (\e -> e.timestamp <= end) afterStart
  in beforeEnd

-- | Get audit log statistics
-- |
-- | @param ctx Logging context with Bridge client
-- | @returns Statistics about the audit log
getAuditStats :: LoggingContext -> Aff AuditLogStats
getAuditStats ctx = do
  entries <- queryAuditLog ctx (defaultQuery { limit = Just maxEntries })
  let stats = foldl aggregateEntry emptyStats entries
  pure stats { totalEntries = length entries }

-- ────────────────────────────────────────────────────────────────────────────
-- Export Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Export audit log as JSON string
-- |
-- | @param ctx Logging context
-- | @param query Query to filter exported entries
-- | @returns JSON string of export data
exportAuditLog :: LoggingContext -> AuditLogQuery -> Aff String
exportAuditLog ctx query = do
  entries <- queryAuditLog ctx query
  stats <- getAuditStats ctx
  timestamp <- liftEffect getCurrentISOTimestamp

  let sessionId = getSessionId ctx
      exportData = Obj.fromFoldable
        [ Tuple "exportedAt" (encodeJson timestamp)
        , Tuple "sessionId" (encodeJson sessionId)
        , Tuple "totalEntries" (encodeJson stats.totalEntries)
        , Tuple "entries" (encodeJson (map encodeEntryRecord entries))
        ]

  pure (stringify (encodeJson exportData))

-- ────────────────────────────────────────────────────────────────────────────
-- Maintenance
-- ────────────────────────────────────────────────────────────────────────────

-- | Clear audit log (requires confirmation code)
-- |
-- | @param ctx Logging context
-- | @param confirmationCode Must be "CLEAR_AUDIT_LOG" to proceed
-- | @returns True if cleared successfully
clearAuditLog :: LoggingContext -> String -> Aff Boolean
clearAuditLog ctx confirmationCode =
  if confirmationCode /= "CLEAR_AUDIT_LOG"
    then do
      liftEffect $ warn "[AUDIT] Clear rejected: invalid code"
      pure false
    else do
      logSecurityWarning ctx "Audit log cleared" Nothing
      let bridgeClient = getBridgeClient ctx
      result <- attempt $ Bridge.storageClear bridgeClient storeName
      case result of
        Left err -> do
          liftEffect $ error ("[AUDIT] Clear failed: " <> show err)
          pure false
        Right cleared -> do
          if cleared
            then liftEffect $ log "[AUDIT] Cleared"
            else liftEffect $ warn "[AUDIT] Clear returned false"
          pure cleared

-- ────────────────────────────────────────────────────────────────────────────
-- Internal
-- ────────────────────────────────────────────────────────────────────────────

emptyStats :: AuditLogStats
emptyStats =
  { totalEntries: 0
  , byCategory: Map.empty
  , bySeverity: Map.empty
  , byToolName: Map.empty
  , oldestEntry: Nothing
  , newestEntry: Nothing
  }

aggregateEntry :: AuditLogStats -> AuditLogEntry -> AuditLogStats
aggregateEntry stats entry =
  stats
    { byCategory = incrementMap (categoryToString entry.category) stats.byCategory
    , bySeverity = incrementMap (severityToString entry.severity) stats.bySeverity
    , byToolName = case entry.toolName of
        Just t -> incrementMap t stats.byToolName
        Nothing -> stats.byToolName
    , oldestEntry = case stats.oldestEntry of
        Nothing -> Just entry.timestamp
        Just old -> if entry.timestamp < old then Just entry.timestamp else Just old
    , newestEntry = case stats.newestEntry of
        Nothing -> Just entry.timestamp
        Just new -> if entry.timestamp > new then Just entry.timestamp else Just new
    }

incrementMap :: String -> Map String Int -> Map String Int
incrementMap key m = Map.insert key (fromMaybe 0 (Map.lookup key m) + 1) m
