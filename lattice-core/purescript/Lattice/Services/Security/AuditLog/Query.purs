-- | Lattice.Services.Security.AuditLog.Query - Query functions
-- |
-- | @module Lattice.Services.Security.AuditLog.Query
-- | @description Functions for querying and exporting audit logs.
-- |
-- | Source: ui/src/services/security/auditLog.ts

module Lattice.Services.Security.AuditLog.Query
  ( -- * Query
    queryAuditLog
  , getAuditStats
    -- * Export
  , exportAuditLog
  , downloadAuditLog
    -- * Maintenance
  , clearAuditLog
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, attempt)
import Effect.Class (liftEffect)
import Effect.Console (log, warn, error)
import Data.Argonaut.Core (Json, stringify)
import Data.Argonaut.Encode (encodeJson)
import Data.Array (length, catMaybes)
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String.CodeUnits as SCU
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
import Lattice.Services.Security.AuditLog.FFI
  ( getSessionId
  , getCurrentISOTimestamp
  , queryEntriesImpl
  , clearStoreImpl
  , downloadBlobImpl
  )
import Lattice.Services.Security.AuditLog.Encode (encodeEntry, encodeQuery)
import Lattice.Services.Security.AuditLog.Decode (decodeEntry)
import Lattice.Services.Security.AuditLog.Logging (logSecurityWarning)

-- ────────────────────────────────────────────────────────────────────────────
-- Query Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Query audit log entries
queryAuditLog :: AuditLogQuery -> Aff (Array AuditLogEntry)
queryAuditLog query = do
  result <- attempt $ queryEntriesImpl storeName (encodeQuery query)
  case result of
    Left err -> do
      liftEffect $ warn ("[AUDIT] Query failed: " <> show err)
      pure []
    Right entries ->
      pure (catMaybes (map decodeEntry entries))

-- | Get audit log statistics
getAuditStats :: Aff AuditLogStats
getAuditStats = do
  entries <- queryAuditLog (defaultQuery { limit = Just maxEntries })
  let stats = foldl aggregateEntry emptyStats entries
  pure stats { totalEntries = length entries }

-- ────────────────────────────────────────────────────────────────────────────
-- Export Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Export audit log as JSON string
exportAuditLog :: AuditLogQuery -> Aff String
exportAuditLog query = do
  entries <- queryAuditLog query
  stats <- getAuditStats
  sessionId <- liftEffect getSessionId
  timestamp <- liftEffect getCurrentISOTimestamp

  let exportData = Obj.fromFoldable
        [ Tuple "exportedAt" (encodeJson timestamp)
        , Tuple "sessionId" (encodeJson sessionId)
        , Tuple "totalEntries" (encodeJson stats.totalEntries)
        , Tuple "entries" (encodeJson (map encodeEntry entries))
        ]

  pure (stringify (encodeJson exportData))

-- | Download audit log as file
downloadAuditLog :: AuditLogQuery -> Aff Unit
downloadAuditLog query = do
  json <- exportAuditLog query
  timestamp <- liftEffect getCurrentISOTimestamp
  let filename = "lattice-audit-" <> SCU.take 10 timestamp <> ".json"
  liftEffect $ downloadBlobImpl json filename

-- ────────────────────────────────────────────────────────────────────────────
-- Maintenance
-- ────────────────────────────────────────────────────────────────────────────

-- | Clear audit log (requires confirmation code)
clearAuditLog :: String -> Aff Boolean
clearAuditLog confirmationCode =
  if confirmationCode /= "CLEAR_AUDIT_LOG"
    then do
      liftEffect $ warn "[AUDIT] Clear rejected: invalid code"
      pure false
    else do
      logSecurityWarning "Audit log cleared" Nothing
      result <- attempt $ clearStoreImpl storeName
      case result of
        Left err -> do
          liftEffect $ error ("[AUDIT] Clear failed: " <> show err)
          pure false
        Right _ -> do
          liftEffect $ log "[AUDIT] Cleared"
          pure true

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
