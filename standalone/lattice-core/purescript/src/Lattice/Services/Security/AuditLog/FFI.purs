-- | Lattice.Services.Security.AuditLog.FFI - Audit log request types
-- |
-- | @module Lattice.Services.Security.AuditLog.FFI
-- | @description Pure request/response types for audit log persistence.
-- |
-- | All database operations are delegated to the Haskell backend via Bridge.
-- | This module provides pure types representing the operations.
-- |
-- | Source: ui/src/services/security/auditLog.ts

module Lattice.Services.Security.AuditLog.FFI
  ( -- * Request Types
    OpenDatabaseRequest(..)
  , AddEntryRequest(..)
  , QueryEntriesRequest(..)
  , CountEntriesRequest(..)
  , ClearStoreRequest(..)
  , DeleteOldEntriesRequest(..)
  , DownloadBlobRequest(..)
    -- * Response Types
  , QueryEntriesResponse
  , CountEntriesResponse
  , DeleteOldEntriesResponse
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- | Request to open a database
data OpenDatabaseRequest = OpenDatabaseRequest
  { dbName :: String
  , version :: Int
  , storeName :: String
  }

derive instance Eq OpenDatabaseRequest
derive instance Generic OpenDatabaseRequest _
instance Show OpenDatabaseRequest where show = genericShow

-- | Request to add an entry (entry is JSON-encoded as String for serialization)
data AddEntryRequest = AddEntryRequest
  { storeName :: String
  , entryJson :: String  -- JSON-encoded entry
  }

derive instance Eq AddEntryRequest
derive instance Generic AddEntryRequest _
instance Show AddEntryRequest where show = genericShow

-- | Request to query entries (query is JSON-encoded as String)
data QueryEntriesRequest = QueryEntriesRequest
  { storeName :: String
  , queryJson :: String  -- JSON-encoded query parameters
  }

derive instance Eq QueryEntriesRequest
derive instance Generic QueryEntriesRequest _
instance Show QueryEntriesRequest where show = genericShow

-- | Response containing queried entries (as JSON strings)
type QueryEntriesResponse = Array String

-- | Request to count entries
data CountEntriesRequest = CountEntriesRequest
  { storeName :: String
  }

derive instance Eq CountEntriesRequest
derive instance Generic CountEntriesRequest _
instance Show CountEntriesRequest where show = genericShow

-- | Response containing entry count
type CountEntriesResponse = Int

-- | Request to clear a store
data ClearStoreRequest = ClearStoreRequest
  { storeName :: String
  }

derive instance Eq ClearStoreRequest
derive instance Generic ClearStoreRequest _
instance Show ClearStoreRequest where show = genericShow

-- | Request to delete old entries
data DeleteOldEntriesRequest = DeleteOldEntriesRequest
  { storeName :: String
  , cutoffTimestamp :: String
  , maxToDelete :: Int
  }

derive instance Eq DeleteOldEntriesRequest
derive instance Generic DeleteOldEntriesRequest _
instance Show DeleteOldEntriesRequest where show = genericShow

-- | Response containing count of deleted entries
type DeleteOldEntriesResponse = Int

-- | Request to download content as a file
data DownloadBlobRequest = DownloadBlobRequest
  { content :: String
  , filename :: String
  }

derive instance Eq DownloadBlobRequest
derive instance Generic DownloadBlobRequest _
instance Show DownloadBlobRequest where show = genericShow
