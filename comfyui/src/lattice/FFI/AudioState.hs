-- |
-- Module      : Lattice.FFI.AudioState
-- Description : C FFI bindings for audio store pure functions
-- 
-- Exports pure functions from Lattice.State.Audio as C functions
-- for Python/TypeScript interop via JSON serialization
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.AudioState where

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
import Lattice.State.Audio
  ( isLoaded
  , isLoading
  , hasError
  , duration
  , bpm
  , frameCount
  , hasAudioBuffer
  , getBPM
  , availableStems
  , hasStems
  , getActiveStemName
  , activeAnalysis
  , activeBuffer
  , AudioState(..)
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

-- | Check if audio is loaded
foreign export ccall "is_loaded"
  c_is_loaded :: CString -> IO CString

c_is_loaded :: CString -> IO CString
c_is_loaded audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = isLoaded state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")

-- | Check if audio is loading
foreign export ccall "is_loading"
  c_is_loading :: CString -> IO CString

c_is_loading :: CString -> IO CString
c_is_loading audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = isLoading state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")

-- | Check if there's an error
foreign export ccall "has_error"
  c_has_error :: CString -> IO CString

c_has_error :: CString -> IO CString
c_has_error audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = hasError state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")

-- | Get audio duration
foreign export ccall "duration"
  c_duration :: CString -> IO CString

c_duration :: CString -> IO CString
c_duration audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = duration state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")

-- | Get BPM
foreign export ccall "bpm"
  c_bpm :: CString -> IO CString

c_bpm :: CString -> IO CString
c_bpm audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = bpm state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")

-- | Get frame count
foreign export ccall "frame_count"
  c_frame_count :: CString -> IO CString

c_frame_count :: CString -> IO CString
c_frame_count audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = frameCount state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")

-- | Check if audio buffer is loaded
foreign export ccall "has_audio_buffer"
  c_has_audio_buffer :: CString -> IO CString

c_has_audio_buffer :: CString -> IO CString
c_has_audio_buffer audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = hasAudioBuffer state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")

-- | Get BPM (Maybe)
foreign export ccall "get_bpm"
  c_get_bpm :: CString -> IO CString

c_get_bpm :: CString -> IO CString
c_get_bpm audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = getBPM state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")

-- | Get available stem names
foreign export ccall "available_stems"
  c_available_stems :: CString -> IO CString

c_available_stems :: CString -> IO CString
c_available_stems audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = availableStems state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")

-- | Check if any stems are loaded
foreign export ccall "has_stems"
  c_has_stems :: CString -> IO CString

c_has_stems :: CString -> IO CString
c_has_stems audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = hasStems state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")

-- | Get active stem name
foreign export ccall "get_active_stem_name"
  c_get_active_stem_name :: CString -> IO CString

c_get_active_stem_name :: CString -> IO CString
c_get_active_stem_name audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = getActiveStemName state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")

-- | Get active analysis
foreign export ccall "active_analysis"
  c_active_analysis :: CString -> IO CString

c_active_analysis :: CString -> IO CString
c_active_analysis audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = activeAnalysis state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")

-- | Get active buffer
foreign export ccall "active_buffer"
  c_active_buffer :: CString -> IO CString

c_active_buffer :: CString -> IO CString
c_active_buffer audioStateJson = do
  audioStateStr <- peekCString audioStateJson
  
  let audioStateBS = TE.encodeUtf8 (T.pack audioStateStr)
  
  case decode (BSL.fromStrict audioStateBS) :: Maybe AudioState of
    Just state -> do
      let result = activeBuffer state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AudioState")
