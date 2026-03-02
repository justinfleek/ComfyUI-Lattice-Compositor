-- | Lattice.Services.Security.AuditLog.FFI - FFI declarations
-- |
-- | @module Lattice.Services.Security.AuditLog.FFI
-- | @description Foreign function interface for IndexedDB operations.
-- |
-- | Source: ui/src/services/security/auditLog.ts

module Lattice.Services.Security.AuditLog.FFI
  ( -- * Session
    getSessionId
  , getCurrentISOTimestamp
    -- * Database Operations
  , openDatabaseImpl
  , addEntryImpl
  , queryEntriesImpl
  , countEntriesImpl
  , clearStoreImpl
  , deleteOldEntriesImpl
    -- * File Operations
  , downloadBlobImpl
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Argonaut.Core (Json)

-- ────────────────────────────────────────────────────────────────────────────
-- Session FFI
-- ────────────────────────────────────────────────────────────────────────────

-- | @ffi Get session ID (from sessionStorage or generate new UUID)
foreign import getSessionId :: Effect String

-- | @ffi Get current ISO 8601 timestamp
foreign import getCurrentISOTimestamp :: Effect String

-- ────────────────────────────────────────────────────────────────────────────
-- Database FFI
-- ────────────────────────────────────────────────────────────────────────────

-- | @ffi Open IndexedDB database
-- | @param dbName Database name
-- | @param version Schema version
-- | @param storeName Object store to create
foreign import openDatabaseImpl :: String -> Int -> String -> Aff Unit

-- | @ffi Add entry to IndexedDB
-- | @param storeName Object store name
-- | @param entry JSON-encoded entry
foreign import addEntryImpl :: String -> Json -> Aff Unit

-- | @ffi Query entries from IndexedDB
-- | @param storeName Object store name
-- | @param query JSON-encoded query parameters
-- | @returns Array of JSON entries
foreign import queryEntriesImpl :: String -> Json -> Aff (Array Json)

-- | @ffi Count entries in IndexedDB
-- | @param storeName Object store name
-- | @returns Total entry count
foreign import countEntriesImpl :: String -> Aff Int

-- | @ffi Clear IndexedDB store
-- | @param storeName Object store name
foreign import clearStoreImpl :: String -> Aff Unit

-- | @ffi Delete old entries from IndexedDB
-- | @param storeName Object store name
-- | @param cutoffTimestamp Entries before this are deleted
-- | @param maxToDelete Maximum entries to delete
-- | @returns Number of entries deleted
foreign import deleteOldEntriesImpl :: String -> String -> Int -> Aff Int

-- ────────────────────────────────────────────────────────────────────────────
-- File FFI
-- ────────────────────────────────────────────────────────────────────────────

-- | @ffi Download blob as file
-- | @param content File content
-- | @param filename Download filename
foreign import downloadBlobImpl :: String -> String -> Effect Unit
