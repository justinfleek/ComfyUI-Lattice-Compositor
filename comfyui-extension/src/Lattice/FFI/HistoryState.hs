-- |
-- Module      : Lattice.FFI.HistoryState
-- Description : C FFI bindings for history store pure functions
-- 
-- Exports pure functions from Lattice.State.History as C functions
-- for Python/TypeScript interop via JSON serialization
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.HistoryState where

import Data.Aeson
  ( decode
  , encode
  , ToJSON(..)
  , Value(..)
  , object
  , (.=)
  )
import qualified Data.ByteString.Lazy as BSL
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String
  ( CString
  , peekCString
  , newCString
  )
import Lattice.State.History
  ( canUndo
  , canRedo
  , currentIndex
  , stackSize
  , HistoryState(..)
  )

-- ============================================================================
-- JSON Response Helpers
-- ============================================================================

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

-- ============================================================================
-- PURE QUERIES (GETTERS)
-- ============================================================================

-- | Check if undo is possible
foreign export ccall "can_undo"
  c_can_undo :: CString -> IO CString

c_can_undo :: CString -> IO CString
c_can_undo historyStateJson = do
  historyStateStr <- peekCString historyStateJson
  
  let historyStateBS = TE.encodeUtf8 (T.pack historyStateStr)
  
  case decode (BSL.fromStrict historyStateBS) :: Maybe HistoryState of
    Just state -> do
      let result = canUndo state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected HistoryState")

-- | Check if redo is possible
foreign export ccall "can_redo"
  c_can_redo :: CString -> IO CString

c_can_redo :: CString -> IO CString
c_can_redo historyStateJson = do
  historyStateStr <- peekCString historyStateJson
  
  let historyStateBS = TE.encodeUtf8 (T.pack historyStateStr)
  
  case decode (BSL.fromStrict historyStateBS) :: Maybe HistoryState of
    Just state -> do
      let result = canRedo state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected HistoryState")

-- | Get current index
foreign export ccall "current_index"
  c_current_index :: CString -> IO CString

c_current_index :: CString -> IO CString
c_current_index historyStateJson = do
  historyStateStr <- peekCString historyStateJson
  
  let historyStateBS = TE.encodeUtf8 (T.pack historyStateStr)
  
  case decode (BSL.fromStrict historyStateBS) :: Maybe HistoryState of
    Just state -> do
      let result = currentIndex state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected HistoryState")

-- | Get stack size
foreign export ccall "stack_size"
  c_stack_size :: CString -> IO CString

c_stack_size :: CString -> IO CString
c_stack_size historyStateJson = do
  historyStateStr <- peekCString historyStateJson
  
  let historyStateBS = TE.encodeUtf8 (T.pack historyStateStr)
  
  case decode (BSL.fromStrict historyStateBS) :: Maybe HistoryState of
    Just state -> do
      let result = stackSize state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected HistoryState")
