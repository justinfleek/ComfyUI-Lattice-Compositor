-- | Lattice.Services.Security.AuditLog.Context - Audit logging context
-- |
-- | @module Lattice.Services.Security.AuditLog.Context
-- | @description Context type for audit logging operations.
-- |
-- | The LoggingContext is created once at application startup and threaded
-- | through all components that need audit logging capabilities.
-- |
-- | Source: ui/src/services/security/auditLog.ts

module Lattice.Services.Security.AuditLog.Context
  ( -- * Context Type
    LoggingContext
    -- * Context Creation
  , createLoggingContext
    -- * Accessors
  , getSessionId
  , getBridgeClient
    -- * Timestamp Generation
  , getCurrentISOTimestamp
  ) where

import Prelude
import Effect (Effect)
import Effect.Now as Now
import Data.DateTime (DateTime(..))
import Data.DateTime.Instant (toDateTime, unInstant)
import Data.Time.Duration (Milliseconds(..))
import Data.Date as Date
import Data.Time as Time
import Data.Enum (fromEnum)
import Data.Int (round)
import Data.String as String
import Data.Array ((..))

import Lattice.Utils.Uuid5.Core (uuid5Default)
import Lattice.Services.Bridge.Client (BridgeClient)

-- ────────────────────────────────────────────────────────────────────────────
-- Context Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Audit logging context
-- |
-- | Contains all dependencies needed for audit logging:
-- | - Session ID: Deterministic UUID5 generated at application start
-- | - Bridge client: For persisting logs to IndexedDB via Haskell backend
-- |
-- | Created once at application initialization via `createLoggingContext`.
type LoggingContext =
  { sessionId :: String
  , bridgeClient :: BridgeClient
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Context Creation
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a new logging context
-- |
-- | @param bridgeClient Connected Bridge client for storage operations
-- | @returns LoggingContext with unique session ID
-- |
-- | The session ID is a deterministic UUID5 generated from the current
-- | timestamp at the moment of creation. This ensures each application
-- | session has a unique, reproducible identifier.
-- |
-- | @example
-- | ```purescript
-- | -- In Main.purs initialization:
-- | bridgeClient <- Bridge.connect "ws://localhost:8080"
-- | loggingCtx <- liftEffect $ createLoggingContext bridgeClient
-- | -- Pass loggingCtx through component hierarchy
-- | ```
createLoggingContext :: BridgeClient -> Effect LoggingContext
createLoggingContext bridgeClient = do
  instant <- Now.now
  let (Milliseconds ms) = unInstant instant
      -- Create deterministic session ID using timestamp
      sessionName = "session:" <> show (round ms :: Int)
      sessionId = uuid5Default sessionName
  pure { sessionId, bridgeClient }

-- ────────────────────────────────────────────────────────────────────────────
-- Accessors
-- ────────────────────────────────────────────────────────────────────────────

-- | Get the session ID from context
getSessionId :: LoggingContext -> String
getSessionId ctx = ctx.sessionId

-- | Get the Bridge client from context
getBridgeClient :: LoggingContext -> BridgeClient
getBridgeClient ctx = ctx.bridgeClient

-- ────────────────────────────────────────────────────────────────────────────
-- Timestamp Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Pad a number to specified width with leading zeros
padZero :: Int -> Int -> String
padZero width n =
  let s = show n
      len = String.length s
      padCount = width - len
      padding = if padCount > 0 
                then String.joinWith "" (map (const "0") (1 .. padCount))
                else ""
  in padding <> s

-- | Format DateTime as ISO 8601 string
-- |
-- | @param dt DateTime to format
-- | @returns ISO 8601 formatted string (e.g., "2026-02-19T14:30:00.000Z")
formatISO8601 :: DateTime -> String
formatISO8601 (DateTime date time) =
  let year = fromEnum (Date.year date)
      month = fromEnum (Date.month date)
      day = fromEnum (Date.day date)
      hour = fromEnum (Time.hour time)
      minute = fromEnum (Time.minute time)
      second = fromEnum (Time.second time)
      millis = fromEnum (Time.millisecond time)
  in padZero 4 year <> "-" <>
     padZero 2 month <> "-" <>
     padZero 2 day <> "T" <>
     padZero 2 hour <> ":" <>
     padZero 2 minute <> ":" <>
     padZero 2 second <> "." <>
     padZero 3 millis <> "Z"

-- | Get current ISO 8601 timestamp
-- |
-- | Pure computation using Effect.Now - reads system time and formats as ISO 8601.
-- | This is a read-only operation allowed under Zero FFI rules.
getCurrentISOTimestamp :: Effect String
getCurrentISOTimestamp = do
  instant <- Now.now
  let dt = toDateTime instant
  pure (formatISO8601 dt)
