-- | Lattice.Services.Security.AuditLog.Decode - JSON decoding
-- |
-- | @module Lattice.Services.Security.AuditLog.Decode
-- | @description JSON decoding for audit log entries.
-- |
-- | Source: ui/src/services/security/auditLog.ts

module Lattice.Services.Security.AuditLog.Decode
  ( decodeEntry
  ) where

import Prelude
import Data.Argonaut.Core (Json, toObject, toString)
import Data.Argonaut.Decode (decodeJson)
import Data.Either (hush)
import Data.Maybe (Maybe(..))
import Foreign.Object as Obj

import Lattice.Services.Security.AuditLog.Types
  ( AuditLogEntry
  , categoryFromString
  , severityFromString
  )

-- | Decode entry from JSON
-- |
-- | Parses JSON object from IndexedDB into AuditLogEntry.
-- | Returns Nothing if malformed or missing required fields.
decodeEntry :: Json -> Maybe AuditLogEntry
decodeEntry json = do
  obj <- toObject json

  -- Required fields
  timestamp <- Obj.lookup "timestamp" obj >>= toString
  categoryStr <- Obj.lookup "category" obj >>= toString
  category <- categoryFromString categoryStr
  severityStr <- Obj.lookup "severity" obj >>= toString
  severity <- severityFromString severityStr
  message <- Obj.lookup "message" obj >>= toString
  sessionId <- Obj.lookup "sessionId" obj >>= toString

  -- Optional fields
  let id = Nothing
  let toolName = Obj.lookup "toolName" obj >>= toString
  let toolArguments = Obj.lookup "toolArguments" obj >>= toObject
  let success = Obj.lookup "success" obj >>= decodeBoolean
  let userAction = Obj.lookup "userAction" obj >>= toString
  let metadata = Obj.lookup "metadata" obj >>= toObject

  pure
    { id
    , timestamp
    , category
    , severity
    , toolName
    , toolArguments
    , message
    , success
    , sessionId
    , userAction
    , metadata
    }

-- | Decode boolean from JSON
decodeBoolean :: Json -> Maybe Boolean
decodeBoolean json = hush (decodeJson json)
