{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Lattice.Services.Bridge.Handlers.Storage
Description : DuckDB-backed storage handler replacing IndexedDB/localStorage
Copyright   : (c) Lattice, 2026
License     : MIT

Replaces browser storage APIs with DuckDB:
- IndexedDB -> DuckDB tables with JSON columns
- localStorage -> DuckDB key-value table (persistent)
- sessionStorage -> In-memory DuckDB (per-connection)

DuckDB provides:
- Columnar storage for analytics
- Full SQL support
- ACID transactions
- Zero-copy reads
- Vectorized execution
-}

module Lattice.Services.Bridge.Handlers.Storage
  ( handleStorageOp
  , storageHandler
  , StorageContext(..)
  , initStorage
  , closeStorage
  ) where

import Control.Exception (bracket, try, SomeException)
import Control.Concurrent.MVar
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import Data.Int (Int64)
import Data.IORef
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Database.DuckDB

import Lattice.Services.Bridge.Protocol

-- ────────────────────────────────────────────────────────────────────────────
-- Storage Context
-- ────────────────────────────────────────────────────────────────────────────

data StorageContext = StorageContext
  { scDatabase :: !Database
  , scConnection :: !Connection
  , scSessionData :: !(MVar (Map Text Text))  -- in-memory session storage
  }

-- | Initialize storage with DuckDB
initStorage :: FilePath -> IO StorageContext
initStorage dbPath = do
  db <- duckdbOpen dbPath
  conn <- duckdbConnect db
  
  -- Create tables for localStorage emulation
  _ <- duckdbQuery conn 
    "CREATE TABLE IF NOT EXISTS local_storage (\
    \  key TEXT PRIMARY KEY,\
    \  value TEXT NOT NULL,\
    \  updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP\
    \)"
  
  -- Create tables for IndexedDB emulation (generic object stores)
  _ <- duckdbQuery conn
    "CREATE TABLE IF NOT EXISTS object_stores (\
    \  store_name TEXT NOT NULL,\
    \  key TEXT NOT NULL,\
    \  value JSON NOT NULL,\
    \  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,\
    \  PRIMARY KEY (store_name, key)\
    \)"
  
  -- Create audit log table (was in IndexedDB)
  _ <- duckdbQuery conn
    "CREATE TABLE IF NOT EXISTS audit_log (\
    \  id INTEGER PRIMARY KEY,\
    \  session_id TEXT NOT NULL,\
    \  timestamp TIMESTAMP NOT NULL,\
    \  event_type TEXT NOT NULL,\
    \  payload JSON,\
    \  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP\
    \)"
  
  -- Create render queue table (was in IndexedDB)
  _ <- duckdbQuery conn
    "CREATE TABLE IF NOT EXISTS render_queue (\
    \  job_id TEXT PRIMARY KEY,\
    \  status TEXT NOT NULL,\
    \  config JSON NOT NULL,\
    \  progress DOUBLE DEFAULT 0,\
    \  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,\
    \  updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP\
    \)"
  
  -- Create rendered frames table
  _ <- duckdbQuery conn
    "CREATE TABLE IF NOT EXISTS rendered_frames (\
    \  job_id TEXT NOT NULL,\
    \  frame_number INTEGER NOT NULL,\
    \  data BLOB NOT NULL,\
    \  PRIMARY KEY (job_id, frame_number)\
    \)"
  
  sessionData <- newMVar Map.empty
  
  pure StorageContext
    { scDatabase = db
    , scConnection = conn
    , scSessionData = sessionData
    }

-- | Close storage
closeStorage :: StorageContext -> IO ()
closeStorage ctx = do
  duckdbDisconnect (scConnection ctx)
  duckdbClose (scDatabase ctx)

-- ────────────────────────────────────────────────────────────────────────────
-- Handler
-- ────────────────────────────────────────────────────────────────────────────

storageHandler :: StorageContext -> Handler StorageOp
storageHandler ctx = handleStorageOp ctx

handleStorageOp :: StorageContext -> StorageOp -> IO Response
handleStorageOp ctx = \case
  -- IndexedDB operations
  StorageOpen name version store -> do
    -- Tables are pre-created, just acknowledge
    pure $ RespOk 0
  
  StorageClose name -> do
    -- No-op for DuckDB (connection pooled)
    pure $ RespOk 0
  
  StoragePut store key value -> do
    result <- try $ duckdbQuery (scConnection ctx)
      ("INSERT OR REPLACE INTO object_stores (store_name, key, value) VALUES (?, ?, ?)")
      -- Note: actual parameterized query would use prepared statements
    case result of
      Left (e :: SomeException) -> pure $ RespError 0 (T.pack $ show e)
      Right _ -> pure $ RespOk 0
  
  StorageGet store key -> do
    result <- try $ duckdbQueryText (scConnection ctx)
      ("SELECT value FROM object_stores WHERE store_name = '" <> store <> "' AND key = '" <> key <> "'")
    case result of
      Left (e :: SomeException) -> pure $ RespError 0 (T.pack $ show e)
      Right rows -> case rows of
        [] -> pure $ RespText 0 ""
        (row:_) -> pure $ RespText 0 row
  
  StorageDelete store key -> do
    result <- try $ duckdbQuery (scConnection ctx)
      ("DELETE FROM object_stores WHERE store_name = '" <> store <> "' AND key = '" <> key <> "'")
    case result of
      Left (e :: SomeException) -> pure $ RespError 0 (T.pack $ show e)
      Right _ -> pure $ RespOk 0
  
  StorageGetAll store -> do
    result <- try $ duckdbQueryJson (scConnection ctx)
      ("SELECT key, value FROM object_stores WHERE store_name = '" <> store <> "'")
    case result of
      Left (e :: SomeException) -> pure $ RespError 0 (T.pack $ show e)
      Right json -> pure $ RespData 0 (TE.encodeUtf8 json)
  
  StorageClear store -> do
    result <- try $ duckdbQuery (scConnection ctx)
      ("DELETE FROM object_stores WHERE store_name = '" <> store <> "'")
    case result of
      Left (e :: SomeException) -> pure $ RespError 0 (T.pack $ show e)
      Right _ -> pure $ RespOk 0
  
  StorageCount store -> do
    result <- try $ duckdbQueryInt (scConnection ctx)
      ("SELECT COUNT(*) FROM object_stores WHERE store_name = '" <> store <> "'")
    case result of
      Left (e :: SomeException) -> pure $ RespError 0 (T.pack $ show e)
      Right count -> pure $ RespNumber 0 (fromIntegral count)
  
  -- localStorage operations
  StorageLocalGet key -> do
    result <- try $ duckdbQueryText (scConnection ctx)
      ("SELECT value FROM local_storage WHERE key = '" <> key <> "'")
    case result of
      Left (e :: SomeException) -> pure $ RespError 0 (T.pack $ show e)
      Right rows -> case rows of
        [] -> pure $ RespText 0 ""
        (row:_) -> pure $ RespText 0 row
  
  StorageLocalSet key value -> do
    result <- try $ duckdbQuery (scConnection ctx)
      ("INSERT OR REPLACE INTO local_storage (key, value) VALUES ('" <> key <> "', '" <> value <> "')")
    case result of
      Left (e :: SomeException) -> pure $ RespError 0 (T.pack $ show e)
      Right _ -> pure $ RespOk 0
  
  -- sessionStorage operations (in-memory)
  StorageSessionGet key -> do
    sessionMap <- readMVar (scSessionData ctx)
    let value = Map.findWithDefault "" key sessionMap
    pure $ RespText 0 value
  
  StorageSessionSet key value -> do
    modifyMVar_ (scSessionData ctx) $ \m ->
      pure $ Map.insert key value m
    pure $ RespOk 0

-- ────────────────────────────────────────────────────────────────────────────
-- DuckDB Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Execute a query with no result
duckdbQuery :: Connection -> Text -> IO ()
duckdbQuery conn sql = do
  result <- duckdbExecute conn (T.unpack sql)
  case result of
    Left err -> error $ "DuckDB error: " <> err
    Right _ -> pure ()

-- | Query returning a single text column
duckdbQueryText :: Connection -> Text -> IO [Text]
duckdbQueryText conn sql = do
  result <- duckdbFetch conn (T.unpack sql)
  case result of
    Left err -> error $ "DuckDB error: " <> err
    Right rows -> pure $ map (T.pack . head) rows

-- | Query returning a single integer
duckdbQueryInt :: Connection -> Text -> IO Int64
duckdbQueryInt conn sql = do
  result <- duckdbFetch conn (T.unpack sql)
  case result of
    Left err -> error $ "DuckDB error: " <> err
    Right rows -> case rows of
      [] -> pure 0
      (row:_) -> pure $ read (head row)

-- | Query returning JSON array
duckdbQueryJson :: Connection -> Text -> IO Text
duckdbQueryJson conn sql = do
  result <- duckdbFetch conn (T.unpack sql)
  case result of
    Left err -> error $ "DuckDB error: " <> err
    Right rows -> pure $ T.pack $ show rows  -- TODO: proper JSON encoding
