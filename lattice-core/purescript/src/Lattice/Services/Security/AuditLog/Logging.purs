-- | Lattice.Services.Security.AuditLog.Logging - Logging functions
-- |
-- | @module Lattice.Services.Security.AuditLog.Logging
-- | @description Functions for writing audit log entries.
-- |
-- | All logging functions require a LoggingContext which provides:
-- | - Session ID for correlating entries
-- | - Bridge client for persisting to IndexedDB
-- |
-- | Source: ui/src/services/security/auditLog.ts

module Lattice.Services.Security.AuditLog.Logging
  ( -- * Core Logging
    logAuditEntry
    -- * Specialized Logging
  , logToolCall
  , logToolResult
  , logRateLimit
  , logVRAMCheck
  , logUserConfirmation
  , logSecurityWarning
  ) where

import Prelude
import Data.Functor (void)
import Data.Int (round)
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Aff (Aff, attempt, launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log, warn, error)
import Effect.Now as Now
import Data.Argonaut.Core (Json, stringify)
import Data.Argonaut.Decode (decodeJson, JsonDecodeError(..))
import Data.Argonaut.Encode (encodeJson)
import Data.Argonaut.Parser (jsonParser)
import Data.DateTime.Instant (unInstant)
import Data.Time.Duration (Milliseconds(..))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.String (toLower, contains, Pattern(..))
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Obj

import Lattice.Services.Security.AuditLog.Types
  ( AuditCategory(..)
  , AuditSeverity(..)
  , AuditLogMetadata
  , categoryToString
  , storeName
  , maxEntries
  )
import Lattice.Services.Security.AuditLog.Context
  ( LoggingContext
  , getSessionId
  , getBridgeClient
  , getCurrentISOTimestamp
  )
import Lattice.Services.Security.AuditLog.Encode (encodeEntryToString)
import Lattice.Services.Bridge.Client as Bridge
import Lattice.Utils.Uuid5.Core (uuid5Default)

-- ────────────────────────────────────────────────────────────────────────────
-- Core Logging
-- ────────────────────────────────────────────────────────────────────────────

-- | Log an audit entry
-- |
-- | @param ctx Logging context with session ID and Bridge client
-- | @param entry Entry to log
-- | @postcondition Entry is written to IndexedDB and console
logAuditEntry :: LoggingContext
              -> { category :: AuditCategory
                 , severity :: AuditSeverity
                 , toolName :: Maybe String
                 , toolArguments :: Maybe (Object Json)
                 , message :: String
                 , success :: Maybe Boolean
                 , userAction :: Maybe String
                 , metadata :: Maybe AuditLogMetadata
                 }
              -> Aff Unit
logAuditEntry ctx entry = do
  timestamp <- liftEffect getCurrentISOTimestamp
  entryId <- liftEffect generateEntryId

  let sessionId = getSessionId ctx
      fullEntry =
        { id: Just entryId
        , timestamp
        , category: entry.category
        , severity: entry.severity
        , toolName: entry.toolName
        , toolArguments: entry.toolArguments
        , message: entry.message
        , success: entry.success
        , sessionId
        , userAction: entry.userAction
        , metadata: entry.metadata
        }

  liftEffect $ logToConsole entry.severity entry.category entry.message entry.toolArguments

  -- Persist to IndexedDB via Bridge
  let bridgeClient = getBridgeClient ctx
      entryJson = encodeEntryToString fullEntry
  result <- attempt $ Bridge.storagePut bridgeClient storeName entryId entryJson
  case result of
    Left err -> liftEffect $ warn ("[SECURITY AUDIT] Failed to log: " <> show err)
    Right false -> liftEffect $ warn "[SECURITY AUDIT] Storage returned false"
    Right true -> pure unit

  -- Prune old entries asynchronously
  liftEffect $ launchAff_ (void $ pruneOldEntries ctx)

-- | Generate a unique entry ID using UUID5 with timestamp
generateEntryId :: Effect String
generateEntryId = do
  instant <- Now.now
  let (Milliseconds ms) = unInstant instant
      name = "audit-entry:" <> show (round ms :: Int)
  pure (uuid5Default name)

-- ────────────────────────────────────────────────────────────────────────────
-- Specialized Logging
-- ────────────────────────────────────────────────────────────────────────────

-- | Log tool call
logToolCall :: LoggingContext -> String -> Object Json -> Maybe String -> Aff Unit
logToolCall ctx toolName args userAction =
  logAuditEntry ctx
    { category: CatToolCall
    , severity: SevInfo
    , toolName: Just toolName
    , toolArguments: Just (sanitizeArguments args)
    , message: "Tool call: " <> toolName
    , success: Nothing
    , userAction
    , metadata: Nothing
    }

-- | Log tool result
logToolResult :: LoggingContext -> String -> Boolean -> String -> Maybe AuditLogMetadata -> Aff Unit
logToolResult ctx toolName success message metadata =
  logAuditEntry ctx
    { category: CatToolResult
    , severity: if success then SevInfo else SevWarning
    , toolName: Just toolName
    , toolArguments: Nothing
    , message
    , success: Just success
    , userAction: Nothing
    , metadata
    }

-- | Log rate limit event
logRateLimit :: LoggingContext -> String -> Int -> Int -> Aff Unit
logRateLimit ctx toolName current maxCount =
  logAuditEntry ctx
    { category: CatRateLimit
    , severity: SevWarning
    , toolName: Just toolName
    , toolArguments: Nothing
    , message: "Rate limit: " <> toolName <> " " <> show current <> "/" <> show maxCount
    , success: Nothing
    , userAction: Nothing
    , metadata: Just (Obj.fromFoldable
        [ Tuple "currentCount" (encodeJson current)
        , Tuple "maxCount" (encodeJson maxCount)
        ])
    }

-- | Log VRAM check
logVRAMCheck :: LoggingContext -> String -> Boolean -> Int -> Int -> Aff Unit
logVRAMCheck ctx toolName passed required available =
  logAuditEntry ctx
    { category: CatVRAMCheck
    , severity: if passed then SevInfo else SevWarning
    , toolName: Just toolName
    , toolArguments: Nothing
    , message: "VRAM " <> (if passed then "OK" else "FAIL") <> ": " <> show required <> "/" <> show available <> "MB"
    , success: Just passed
    , userAction: Nothing
    , metadata: Just (Obj.fromFoldable
        [ Tuple "required" (encodeJson required)
        , Tuple "available" (encodeJson available)
        ])
    }

-- | Log user confirmation
logUserConfirmation :: LoggingContext -> String -> Boolean -> Aff Unit
logUserConfirmation ctx toolName confirmed =
  logAuditEntry ctx
    { category: CatUserConfirmation
    , severity: if confirmed then SevInfo else SevWarning
    , toolName: Just toolName
    , toolArguments: Nothing
    , message: (if confirmed then "APPROVED: " else "DECLINED: ") <> toolName
    , success: Just confirmed
    , userAction: Nothing
    , metadata: Nothing
    }

-- | Log security warning
logSecurityWarning :: LoggingContext -> String -> Maybe AuditLogMetadata -> Aff Unit
logSecurityWarning ctx message metadata =
  logAuditEntry ctx
    { category: CatSecurityWarning
    , severity: SevCritical
    , toolName: Nothing
    , toolArguments: Nothing
    , message: "SECURITY: " <> message
    , success: Nothing
    , userAction: Nothing
    , metadata
    }

-- ────────────────────────────────────────────────────────────────────────────
-- Internal
-- ────────────────────────────────────────────────────────────────────────────

logToConsole :: AuditSeverity -> AuditCategory -> String -> Maybe (Object Json) -> Effect Unit
logToConsole severity category message args = do
  let prefix = "[AUDIT] [" <> categoryToString category <> "] "
  let argsStr = case args of
        Just a -> " " <> stringify (encodeJson a)
        Nothing -> ""
  case severity of
    SevError -> error (prefix <> message <> argsStr)
    SevCritical -> error (prefix <> message <> argsStr)
    SevWarning -> warn (prefix <> message <> argsStr)
    SevInfo -> log (prefix <> message <> argsStr)

sanitizeArguments :: Object Json -> Object Json
sanitizeArguments args = Obj.mapWithKey sanitizeArg args
  where
    sensitiveKeys = ["password", "secret", "token", "key", "apikey", "auth"]
    isSensitive k = Array.any (\s -> contains (Pattern s) (toLower k)) sensitiveKeys
    sanitizeArg key val
      | isSensitive key = encodeJson "[REDACTED]"
      | otherwise = val

-- | Prune old entries to keep storage bounded
-- |
-- | Queries current count and deletes oldest entries if over maxEntries.
-- | Gets all entries, sorts by timestamp, deletes oldest ones.
pruneOldEntries :: LoggingContext -> Aff Int
pruneOldEntries ctx = do
  let bridgeClient = getBridgeClient ctx
  count <- Bridge.storageCount bridgeClient storeName
  if count > maxEntries
    then do
      -- Get all entries to find oldest ones to delete
      allEntries <- Bridge.storageGetAll bridgeClient storeName
      let entriesToDelete = count - maxEntries
          -- Entries are stored with timestamp-based keys
          -- Sort by key (which contains timestamp) and take oldest
          sortedKeys = Array.take entriesToDelete (Array.sort (extractKeys allEntries))
      -- Delete each old entry
      deletedCounts <- traverse (deleteEntry bridgeClient) sortedKeys
      pure (Array.length (Array.filter identity deletedCounts))
    else pure 0
  where
    -- Extract keys from JSON entries (assumes id field contains key)
    extractKeys :: Array String -> Array String
    extractKeys entries = Array.mapMaybe extractId entries
    
    extractId :: String -> Maybe String
    extractId jsonStr = case decodeJson =<< parseJsonString jsonStr of
      Right (obj :: { id :: Maybe String }) -> obj.id
      Left _ -> Nothing
    
    parseJsonString :: String -> Either JsonDecodeError Json
    parseJsonString str = case jsonParser str of
      Left err -> Left (TypeMismatch err)
      Right json -> Right json
    
    deleteEntry :: Bridge.BridgeClient -> String -> Aff Boolean
    deleteEntry client key = Bridge.storageDelete client storeName key
