-- | Lattice.Services.Security.AuditLog.Encode - JSON encoding
-- |
-- | @module Lattice.Services.Security.AuditLog.Encode
-- | @description JSON encoding for audit log entries and queries.
-- |
-- | Source: ui/src/services/security/auditLog.ts

module Lattice.Services.Security.AuditLog.Encode
  ( encodeEntry
  , encodeQuery
  ) where

import Prelude
import Data.Argonaut.Core (Json)
import Data.Argonaut.Encode (encodeJson)
import Data.Maybe (fromMaybe)
import Data.Tuple (Tuple(..))
import Foreign.Object as Obj

import Lattice.Services.Security.AuditLog.Types
  ( AuditLogEntry
  , AuditLogQuery
  , categoryToString
  , severityToString
  )

-- | Encode entry to JSON for storage
encodeEntry :: AuditLogEntry -> Json
encodeEntry entry = encodeJson $ Obj.fromFoldable
  [ Tuple "timestamp" (encodeJson entry.timestamp)
  , Tuple "category" (encodeJson (categoryToString entry.category))
  , Tuple "severity" (encodeJson (severityToString entry.severity))
  , Tuple "toolName" (encodeJson entry.toolName)
  , Tuple "toolArguments" (encodeJson entry.toolArguments)
  , Tuple "message" (encodeJson entry.message)
  , Tuple "success" (encodeJson entry.success)
  , Tuple "sessionId" (encodeJson entry.sessionId)
  , Tuple "userAction" (encodeJson entry.userAction)
  , Tuple "metadata" (encodeJson entry.metadata)
  ]

-- | Encode query to JSON for FFI
encodeQuery :: AuditLogQuery -> Json
encodeQuery query = encodeJson $ Obj.fromFoldable
  [ Tuple "category" (encodeJson (map categoryToString query.category))
  , Tuple "severity" (encodeJson (map severityToString query.severity))
  , Tuple "toolName" (encodeJson query.toolName)
  , Tuple "sessionId" (encodeJson query.sessionId)
  , Tuple "startTime" (encodeJson query.startTime)
  , Tuple "endTime" (encodeJson query.endTime)
  , Tuple "limit" (encodeJson (fromMaybe 100 query.limit))
  , Tuple "offset" (encodeJson (fromMaybe 0 query.offset))
  ]
