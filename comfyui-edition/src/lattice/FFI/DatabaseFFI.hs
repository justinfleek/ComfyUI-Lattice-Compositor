-- |
-- Module      : Lattice.FFI.DatabaseFFI
-- Description : C FFI exports for Database operations
-- 
-- Exports DuckDB database functions as C-compatible functions for TypeScript/Python interop
-- All functions use JSON for input/output
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.DatabaseFFI where

import Foreign.C.Types (CInt(..))
import Foreign.C.String (CString, peekCString, newCString)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString.Lazy as BSL
import Data.Aeson
  ( Value(..)
  , object
  , (.=)
  , decode
  , encode
  , ToJSON(..)
  , FromJSON(..)
  )

import Lattice.Database.DuckDB
  ( DuckDBConnection(..)
  , connect
  , disconnect
  , query
  , execute
  )
import Lattice.Database.ChatMessages
  ( ChatMessage(..)
  , saveChatMessage
  , getChatHistory
  , searchChatHistory
  )
import Lattice.Database.Schema
  ( initializeSchema
  , initializeFeatureFlags
  )
import Lattice.Database.ModuleRegistry
  ( FeatureFlagName(..)
  , ModuleId(..)
  , defaultRegistry
  , registerPluginModule
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                 // json // r
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert JSON Value to CString
jsonToCString :: Value -> IO CString
jsonToCString resultJSON = do
  let resultBS = BSL.toStrict (encode resultJSON)
  let resultText = TE.decodeUtf8 resultBS
  newCString (T.unpack resultText)

-- | Create error response JSON
errorResponse :: T.Text -> Value
errorResponse msg = object ["status" .= ("error" :: T.Text), "message" .= msg]

-- | Create success response JSON with result
successResponse :: ToJSON a => a -> Value
successResponse result = object ["status" .= ("success" :: T.Text), "result" .= result]

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // database // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Export database query as C function
-- C signature: char* database_query(char* db_path, char* sql_query)
-- Returns: JSON array of results
foreign export ccall "database_query"
  c_database_query :: CString -> CString -> IO CString

c_database_query :: CString -> CString -> IO CString
c_database_query dbPathPtr sqlPtr = do
  dbPathStr <- peekCString dbPathPtr
  sqlStr <- peekCString sqlPtr
  
  -- Connect to database
  conn <- connect dbPathStr
  
  -- Execute query
  result <- query conn (T.pack sqlStr)
  
  case result of
    Left err -> jsonToCString (errorResponse (T.pack (show err)))
    Right rows -> jsonToCString (successResponse rows)

-- | Export initialize schema as C function
-- C signature: char* initialize_schema(char* db_path, char* enabled_flags_json)
-- Returns: JSON success/error response
foreign export ccall "initialize_schema"
  c_initialize_schema :: CString -> CString -> IO CString

c_initialize_schema :: CString -> CString -> IO CString
c_initialize_schema dbPathPtr flagsJsonPtr =
  ( do
      dbPathStr <- peekCString dbPathPtr
      flagsStr <- peekCString flagsJsonPtr
      let flagsBS = TE.encodeUtf8 (T.pack flagsStr)
      let enabledFlags = case decode (BSL.fromStrict flagsBS) :: Maybe [String] of
            Just flags -> map FeatureFlagName (map T.pack flags)
            Nothing -> []
      let dbDir = takeWhile (/= '/') dbPathStr
      conn <- connect dbPathStr
      result <- initializeSchema conn dbDir enabledFlags
      case result of
        Left err -> jsonToCString (errorResponse err)
        Right () -> jsonToCString (successResponse ("initialized" :: T.Text))
  )

-- | Export save chat message as C function
-- C signature: char* save_chat_message(char* db_path, char* message_json)
-- Returns: JSON success/error response
foreign export ccall "save_chat_message"
  c_save_chat_message :: CString -> CString -> IO CString

c_save_chat_message :: CString -> CString -> IO CString
c_save_chat_message dbPathPtr messageJsonPtr = do
  dbPathStr <- peekCString dbPathPtr
  messageStr <- peekCString messageJsonPtr
  
  let messageBS = TE.encodeUtf8 (T.pack messageStr)
  
  case decode (BSL.fromStrict messageBS) :: Maybe ChatMessage of
    Nothing -> jsonToCString (errorResponse "Invalid chat message JSON")
    Just msg -> do
      conn <- connect dbPathStr
      result <- saveChatMessage conn msg
      case result of
        Left err -> jsonToCString (errorResponse err)
        Right () -> jsonToCString (successResponse ("saved" :: T.Text))

-- | Export get chat history as C function
-- C signature: char* get_chat_history(char* db_path, char* project_id_json, int limit)
-- Returns: JSON array of chat messages
foreign export ccall "get_chat_history"
  c_get_chat_history :: CString -> CString -> CInt -> IO CString

c_get_chat_history :: CString -> CString -> CInt -> IO CString
c_get_chat_history dbPathPtr projectIdJsonPtr limit =
  do dbPathStr <- peekCString dbPathPtr
     projectIdStr <- peekCString projectIdJsonPtr
     let projectIdBS = TE.encodeUtf8 (T.pack projectIdStr)
     let mProjectId = case decode (BSL.fromStrict projectIdBS) :: Maybe (Maybe T.Text) of
           Just pid -> pid
           Nothing -> Nothing
     conn <- connect dbPathStr
     result <- getChatHistory conn mProjectId (fromIntegral limit)
     case result of
       Left err -> jsonToCString (errorResponse err)
       Right messages -> jsonToCString (successResponse messages)
