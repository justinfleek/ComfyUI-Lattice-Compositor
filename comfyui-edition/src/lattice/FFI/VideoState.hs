-- |
-- Module      : Lattice.FFI.VideoState
-- Description : FFI bindings for video state management
-- 
-- Foreign function interface for Lattice.State.Video
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.VideoState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Foreign.C.Types (CDouble(..), CInt(..))
import Lattice.State.Video
  ( calculateTimeStretch
  , calculateVideoFrameCount
  , calculateStretchedDuration
  , checkFpsMismatch
  , calculateVideoOutPoint
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
--                                                  // calculation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Calculate time stretch percentage
foreign export ccall calculate_time_stretch_ffi :: CDouble -> CDouble -> IO CString
calculate_time_stretch_ffi :: CDouble -> CDouble -> IO CString
calculate_time_stretch_ffi videoFps compFps = do
  let result = calculateTimeStretch (realToFrac videoFps) (realToFrac compFps)
  jsonToCString (successResponse result)

-- | FFI: Calculate video frame count
foreign export ccall calculate_video_frame_count_ffi :: CDouble -> CDouble -> IO CString
calculate_video_frame_count_ffi :: CDouble -> CDouble -> IO CString
calculate_video_frame_count_ffi duration fps = do
  let result = calculateVideoFrameCount (realToFrac duration) (realToFrac fps)
  jsonToCString (successResponse result)

-- | FFI: Calculate stretched duration
foreign export ccall calculate_stretched_duration_ffi :: CDouble -> CDouble -> CDouble -> IO CString
calculate_stretched_duration_ffi :: CDouble -> CDouble -> CDouble -> IO CString
calculate_stretched_duration_ffi duration videoFps compFps = do
  let result = calculateStretchedDuration (realToFrac duration) (realToFrac videoFps) (realToFrac compFps)
  jsonToCString (successResponse result)

-- | FFI: Check fps mismatch
foreign export ccall check_fps_mismatch_ffi :: CDouble -> CDouble -> CDouble -> IO CString
check_fps_mismatch_ffi :: CDouble -> CDouble -> CDouble -> IO CString
check_fps_mismatch_ffi videoFps compFps threshold = do
  let result = checkFpsMismatch (realToFrac videoFps) (realToFrac compFps) (realToFrac threshold)
  jsonToCString (successResponse result)

-- | FFI: Calculate video out point
foreign export ccall calculate_video_out_point_ffi :: CInt -> CInt -> IO CString
calculate_video_out_point_ffi :: CInt -> CInt -> IO CString
calculate_video_out_point_ffi videoFrameCount compFrameCount = do
  let result = calculateVideoOutPoint (fromIntegral videoFrameCount) (fromIntegral compFrameCount)
  jsonToCString (successResponse result)
