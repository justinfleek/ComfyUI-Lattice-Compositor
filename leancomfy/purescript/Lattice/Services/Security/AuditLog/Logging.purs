-- | Lattice.Services.Security.AuditLog.Logging - Logging functions
-- |
-- | @module Lattice.Services.Security.AuditLog.Logging
-- | @description Functions for writing audit log entries.
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
import Effect (Effect)
import Effect.Aff (Aff, attempt, launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log, warn, error)
import Data.Argonaut.Core (Json, stringify)
import Data.Argonaut.Encode (encodeJson)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
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
import Lattice.Services.Security.AuditLog.FFI
  ( getSessionId
  , getCurrentISOTimestamp
  , addEntryImpl
  , countEntriesImpl
  , deleteOldEntriesImpl
  )
import Lattice.Services.Security.AuditLog.Encode (encodeEntry)

--------------------------------------------------------------------------------
-- Core Logging
--------------------------------------------------------------------------------

-- | Log an audit entry
-- |
-- | @param entry Entry to log
-- | @postcondition Entry is written to IndexedDB and console
logAuditEntry :: { category :: AuditCategory
                 , severity :: AuditSeverity
                 , toolName :: Maybe String
                 , toolArguments :: Maybe (Object Json)
                 , message :: String
                 , success :: Maybe Boolean
                 , userAction :: Maybe String
                 , metadata :: Maybe AuditLogMetadata
                 } -> Aff Unit
logAuditEntry entry = do
  sessionId <- liftEffect getSessionId
  timestamp <- liftEffect getCurrentISOTimestamp

  let fullEntry =
        { id: Nothing
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

  result <- attempt $ addEntryImpl storeName (encodeEntry fullEntry)
  case result of
    Left err -> liftEffect $ warn ("[SECURITY AUDIT] Failed to log: " <> show err)
    Right _ -> pure unit

  launchAff_ pruneOldEntries

--------------------------------------------------------------------------------
-- Specialized Logging
--------------------------------------------------------------------------------

-- | Log tool call
logToolCall :: String -> Object Json -> Maybe String -> Aff Unit
logToolCall toolName args userAction =
  logAuditEntry
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
logToolResult :: String -> Boolean -> String -> Maybe AuditLogMetadata -> Aff Unit
logToolResult toolName success message metadata =
  logAuditEntry
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
logRateLimit :: String -> Int -> Int -> Aff Unit
logRateLimit toolName current maxCount =
  logAuditEntry
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
logVRAMCheck :: String -> Boolean -> Int -> Int -> Aff Unit
logVRAMCheck toolName passed required available =
  logAuditEntry
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
logUserConfirmation :: String -> Boolean -> Aff Unit
logUserConfirmation toolName confirmed =
  logAuditEntry
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
logSecurityWarning :: String -> Maybe AuditLogMetadata -> Aff Unit
logSecurityWarning message metadata =
  logAuditEntry
    { category: CatSecurityWarning
    , severity: SevCritical
    , toolName: Nothing
    , toolArguments: Nothing
    , message: "SECURITY: " <> message
    , success: Nothing
    , userAction: Nothing
    , metadata
    }

--------------------------------------------------------------------------------
-- Internal
--------------------------------------------------------------------------------

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
    isSensitive k = anyMatch (\s -> contains (Pattern s) (toLower k)) sensitiveKeys
    sanitizeArg key val
      | isSensitive key = encodeJson "[REDACTED]"
      | otherwise = val
    anyMatch _ [] = false
    anyMatch p (x : xs) = if p x then true else anyMatch p xs

pruneOldEntries :: Aff Int
pruneOldEntries = do
  count <- countEntriesImpl storeName
  if count > maxEntries
    then deleteOldEntriesImpl storeName storeName (count - maxEntries)
    else pure 0
