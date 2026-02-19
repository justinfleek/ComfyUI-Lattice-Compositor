-- | Lattice.Services.Security.AuditLog.Types - Audit log type definitions
-- |
-- | @module Lattice.Services.Security.AuditLog.Types
-- | @description Core types for security audit logging.
-- |
-- | Source: ui/src/services/security/auditLog.ts

module Lattice.Services.Security.AuditLog.Types
  ( -- * Event Categories
    AuditCategory(..)
  , categoryToString
  , categoryFromString
    -- * Severity Levels
  , AuditSeverity(..)
  , severityToString
  , severityFromString
    -- * Entry Types
  , AuditLogEntry
  , AuditLogMetadata
  , AuditLogQuery
  , AuditLogStats
  , defaultQuery
    -- * Constants
  , maxEntries
  , maxAgeDays
  , dbName
  , storeName
  ) where

import Prelude
import Data.Argonaut.Core (Json)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Foreign.Object (Object)

-- ────────────────────────────────────────────────────────────────────────────
-- Event Categories
-- ────────────────────────────────────────────────────────────────────────────

-- | Event category for audit log entries
-- |
-- | @constructor CatToolCall AI agent called a tool
-- | @constructor CatToolResult Tool execution completed
-- | @constructor CatRateLimit Rate limit was triggered
-- | @constructor CatVRAMCheck GPU memory check performed
-- | @constructor CatUserConfirmation User approved/declined action
-- | @constructor CatSecurityWarning Security-critical event
-- | @constructor CatError System error occurred
data AuditCategory
  = CatToolCall
  | CatToolResult
  | CatRateLimit
  | CatVRAMCheck
  | CatUserConfirmation
  | CatSecurityWarning
  | CatError

derive instance Eq AuditCategory
derive instance Generic AuditCategory _
instance Show AuditCategory where show = genericShow

-- | Convert category to string identifier
categoryToString :: AuditCategory -> String
categoryToString cat = case cat of
  CatToolCall -> "tool_call"
  CatToolResult -> "tool_result"
  CatRateLimit -> "rate_limit"
  CatVRAMCheck -> "vram_check"
  CatUserConfirmation -> "user_confirmation"
  CatSecurityWarning -> "security_warning"
  CatError -> "error"

-- | Parse category from string identifier
categoryFromString :: String -> Maybe AuditCategory
categoryFromString str = case str of
  "tool_call" -> Just CatToolCall
  "tool_result" -> Just CatToolResult
  "rate_limit" -> Just CatRateLimit
  "vram_check" -> Just CatVRAMCheck
  "user_confirmation" -> Just CatUserConfirmation
  "security_warning" -> Just CatSecurityWarning
  "error" -> Just CatError
  _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Severity Levels
-- ────────────────────────────────────────────────────────────────────────────

-- | Event severity level
-- |
-- | @constructor SevInfo Normal operation
-- | @constructor SevWarning Potential issue
-- | @constructor SevError Error occurred
-- | @constructor SevCritical Security threat
data AuditSeverity = SevInfo | SevWarning | SevError | SevCritical

derive instance Eq AuditSeverity
derive instance Ord AuditSeverity
derive instance Generic AuditSeverity _
instance Show AuditSeverity where show = genericShow

-- | Convert severity to string identifier
severityToString :: AuditSeverity -> String
severityToString sev = case sev of
  SevInfo -> "info"
  SevWarning -> "warning"
  SevError -> "error"
  SevCritical -> "critical"

-- | Parse severity from string identifier
severityFromString :: String -> Maybe AuditSeverity
severityFromString str = case str of
  "info" -> Just SevInfo
  "warning" -> Just SevWarning
  "error" -> Just SevError
  "critical" -> Just SevCritical
  _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Entry Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Audit log metadata (arbitrary JSON key-value pairs)
type AuditLogMetadata = Object Json

-- | Audit log entry
-- |
-- | @field id Auto-incremented database ID (set by IndexedDB)
-- | @field timestamp ISO 8601 timestamp of event
-- | @field category Event category
-- | @field severity Event severity
-- | @field toolName Name of tool (for tool-related events)
-- | @field toolArguments Sanitized tool arguments
-- | @field message Human-readable event description
-- | @field success Whether operation succeeded
-- | @field sessionId Browser session ID
-- | @field userAction User action that triggered event
-- | @field metadata Additional structured data
type AuditLogEntry =
  { id :: Maybe String
  , timestamp :: String
  , category :: AuditCategory
  , severity :: AuditSeverity
  , toolName :: Maybe String
  , toolArguments :: Maybe (Object Json)
  , message :: String
  , success :: Maybe Boolean
  , sessionId :: String
  , userAction :: Maybe String
  , metadata :: Maybe AuditLogMetadata
  }

-- | Query parameters for filtering audit log
type AuditLogQuery =
  { category :: Maybe AuditCategory
  , severity :: Maybe AuditSeverity
  , toolName :: Maybe String
  , sessionId :: Maybe String
  , startTime :: Maybe String
  , endTime :: Maybe String
  , limit :: Maybe Int
  , offset :: Maybe Int
  }

-- | Default query (last 100 entries)
defaultQuery :: AuditLogQuery
defaultQuery =
  { category: Nothing
  , severity: Nothing
  , toolName: Nothing
  , sessionId: Nothing
  , startTime: Nothing
  , endTime: Nothing
  , limit: Just 100
  , offset: Just 0
  }

-- | Audit log statistics
type AuditLogStats =
  { totalEntries :: Int
  , byCategory :: Map String Int
  , bySeverity :: Map String Int
  , byToolName :: Map String Int
  , oldestEntry :: Maybe String
  , newestEntry :: Maybe String
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Maximum entries to keep (10,000)
maxEntries :: Int
maxEntries = 10000

-- | Maximum age in days (30)
maxAgeDays :: Int
maxAgeDays = 30

-- | IndexedDB database name
dbName :: String
dbName = "LatticeSecurityAudit"

-- | IndexedDB object store name
storeName :: String
storeName = "auditLog"
