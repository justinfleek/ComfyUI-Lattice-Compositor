-- |
-- Module      : Lattice.FFI.TimelineSnapState
-- Description : FFI bindings for timeline snap service
-- 
-- Foreign function interface for Lattice.Services.TimelineSnap
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.TimelineSnapState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.Services.TimelineSnap
  ( getBeatFrames
  , getPeakFrames
  , isNearBeat
  , getSnapColor
  , AudioAnalysis(..)
  , PeakData(..)
  , SnapType(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // json // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Create success response JSON
successResponse :: ToJSON a => a -> BSL.ByteString
successResponse result = encode $ object ["status" .= ("success" :: T.Text), "result" .= result]

-- | Create error response JSON
errorResponse :: T.Text -> BSL.ByteString
errorResponse msg = encode $ object ["status" .= ("error" :: T.Text), "message" .= msg]

-- | Convert ByteString to CString
jsonToCString :: BSL.ByteString -> IO CString
jsonToCString = newCString . T.unpack . TE.decodeUtf8 . BSL.toStrict

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // query // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Get beat frames
foreign export ccall get_beat_frames_ffi :: CString -> IO CString
get_beat_frames_ffi :: CString -> IO CString
get_beat_frames_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe AudioAnalysis) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right mAnalysis -> do
      let result = getBeatFrames mAnalysis
      jsonToCString (successResponse result)

-- | FFI: Get peak frames
foreign export ccall get_peak_frames_ffi :: CString -> IO CString
get_peak_frames_ffi :: CString -> IO CString
get_peak_frames_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe PeakData) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right mPeakData -> do
      let result = getPeakFrames mPeakData
      jsonToCString (successResponse result)

-- | FFI: Check if near beat
foreign export ccall is_near_beat_ffi :: CString -> IO CString
is_near_beat_ffi :: CString -> IO CString
is_near_beat_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Double, Maybe AudioAnalysis, Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (frame, mAnalysis, thresholdFrames) -> do
      let result = isNearBeat frame mAnalysis thresholdFrames
      jsonToCString (successResponse result)

-- | FFI: Get snap color
foreign export ccall get_snap_color_ffi :: CString -> IO CString
get_snap_color_ffi :: CString -> IO CString
get_snap_color_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String SnapType of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right snapType -> do
      let result = getSnapColor snapType
      jsonToCString (successResponse result)
