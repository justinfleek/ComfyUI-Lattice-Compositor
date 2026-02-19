-- |
-- Module      : Lattice.FFI.PlaybackState
-- Description : C FFI bindings for playback store pure functions
-- 
-- Exports pure functions from Lattice.State.Playback as C functions
-- for Python/TypeScript interop via JSON serialization
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.PlaybackState where

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
import Lattice.State.Playback
  ( playing
  , hasWorkArea
  , effectiveStartFrame
  , effectiveEndFrame
  , clampFrame
  , stepForwardFrame
  , stepBackwardFrame
  , PlaybackState(..)
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
--                                                           // pure // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if playback is currently playing
foreign export ccall "playing"
  c_playing :: CString -> IO CString

c_playing :: CString -> IO CString
c_playing playbackStateJson = do
  playbackStateStr <- peekCString playbackStateJson
  
  let playbackStateBS = TE.encodeUtf8 (T.pack playbackStateStr)
  
  case decode (BSL.fromStrict playbackStateBS) :: Maybe PlaybackState of
    Just state -> do
      let result = playing state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected PlaybackState")

-- | Check if work area is set
foreign export ccall "has_work_area"
  c_has_work_area :: CString -> IO CString

c_has_work_area :: CString -> IO CString
c_has_work_area playbackStateJson = do
  playbackStateStr <- peekCString playbackStateJson
  
  let playbackStateBS = TE.encodeUtf8 (T.pack playbackStateStr)
  
  case decode (BSL.fromStrict playbackStateBS) :: Maybe PlaybackState of
    Just state -> do
      let result = hasWorkArea state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected PlaybackState")

-- | Get effective start frame
foreign export ccall "effective_start_frame"
  c_effective_start_frame :: CString -> IO CString

c_effective_start_frame :: CString -> IO CString
c_effective_start_frame playbackStateJson = do
  playbackStateStr <- peekCString playbackStateJson
  
  let playbackStateBS = TE.encodeUtf8 (T.pack playbackStateStr)
  
  case decode (BSL.fromStrict playbackStateBS) :: Maybe PlaybackState of
    Just state -> do
      let result = effectiveStartFrame state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected PlaybackState")

-- | Get effective end frame
foreign export ccall "effective_end_frame"
  c_effective_end_frame :: CString -> CString -> IO CString

c_effective_end_frame :: CString -> CString -> IO CString
c_effective_end_frame playbackStateJson frameCountJson = do
  playbackStateStr <- peekCString playbackStateJson
  frameCountStr <- peekCString frameCountJson
  
  let playbackStateBS = TE.encodeUtf8 (T.pack playbackStateStr)
  let frameCountBS = TE.encodeUtf8 (T.pack frameCountStr)
  
  case (decode (BSL.fromStrict playbackStateBS) :: Maybe PlaybackState,
        decode (BSL.fromStrict frameCountBS) :: Maybe Double) of
    (Just state, Just frameCount) -> do
      let result = effectiveEndFrame state frameCount
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected PlaybackState and Double")

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // pure // calculations
-- ════════════════════════════════════════════════════════════════════════════

-- | Clamp frame to valid range
foreign export ccall "clamp_frame"
  c_clamp_frame :: CString -> CString -> IO CString

c_clamp_frame :: CString -> CString -> IO CString
c_clamp_frame frameJson frameCountJson = do
  frameStr <- peekCString frameJson
  frameCountStr <- peekCString frameCountJson
  
  let frameBS = TE.encodeUtf8 (T.pack frameStr)
  let frameCountBS = TE.encodeUtf8 (T.pack frameCountStr)
  
  case (decode (BSL.fromStrict frameBS) :: Maybe Double,
        decode (BSL.fromStrict frameCountBS) :: Maybe Double) of
    (Just frame, Just frameCount) -> do
      let result = clampFrame frame frameCount
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected Double and Double")

-- | Step forward one frame
foreign export ccall "step_forward_frame"
  c_step_forward_frame :: CString -> CString -> IO CString

c_step_forward_frame :: CString -> CString -> IO CString
c_step_forward_frame currentFrameJson frameCountJson = do
  currentFrameStr <- peekCString currentFrameJson
  frameCountStr <- peekCString frameCountJson
  
  let currentFrameBS = TE.encodeUtf8 (T.pack currentFrameStr)
  let frameCountBS = TE.encodeUtf8 (T.pack frameCountStr)
  
  case (decode (BSL.fromStrict currentFrameBS) :: Maybe Double,
        decode (BSL.fromStrict frameCountBS) :: Maybe Double) of
    (Just currentFrame, Just frameCount) -> do
      let result = stepForwardFrame currentFrame frameCount
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected Double and Double")

-- | Step backward one frame
foreign export ccall "step_backward_frame"
  c_step_backward_frame :: CString -> IO CString

c_step_backward_frame :: CString -> IO CString
c_step_backward_frame currentFrameJson = do
  currentFrameStr <- peekCString currentFrameJson
  
  let currentFrameBS = TE.encodeUtf8 (T.pack currentFrameStr)
  
  case decode (BSL.fromStrict currentFrameBS) :: Maybe Double of
    Just currentFrame -> do
      let result = stepBackwardFrame currentFrame
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected Double")
