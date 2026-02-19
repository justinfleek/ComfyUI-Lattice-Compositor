-- |
-- Module      : Lattice.FFI.CameraState
-- Description : FFI bindings for camera state management
-- 
-- Foreign function interface for Lattice.State.Camera
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.CameraState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Foreign.C.Types (CDouble(..))
import Lattice.State.Camera
  ( framesEqual
  , safeFrame
  , allCameras
  , getCamera
  , getCameraKeyframes
  , activeCamera
  , CameraKeyframe(..)
  )
import Lattice.Types.LayerData3D (Camera3D(..))
import qualified Data.HashMap.Strict as HM

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
--                                                       // helper // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Compare two frame numbers safely
foreign export ccall frames_equal_ffi :: CDouble -> CDouble -> IO CString
frames_equal_ffi :: CDouble -> CDouble -> IO CString
frames_equal_ffi a b = do
  let result = framesEqual (realToFrac a) (realToFrac b)
  jsonToCString (successResponse result)

-- | FFI: Validate and sanitize frame number
foreign export ccall safe_frame_ffi :: CString -> CDouble -> IO CString
safe_frame_ffi :: CString -> CDouble -> IO CString
safe_frame_ffi inputCStr fallback = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right mFrame -> do
      let result = safeFrame mFrame (realToFrac fallback)
      jsonToCString (successResponse result)

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // query // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Get all cameras as list
foreign export ccall all_cameras_ffi :: CString -> IO CString
all_cameras_ffi :: CString -> IO CString
all_cameras_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (HM.HashMap T.Text Camera3D) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right cameras -> do
      let result = allCameras cameras
      jsonToCString (successResponse result)

-- | FFI: Get camera by ID
foreign export ccall get_camera_ffi :: CString -> IO CString
get_camera_ffi :: CString -> IO CString
get_camera_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (T.Text, HM.HashMap T.Text Camera3D) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (cameraId, cameras) -> do
      let result = getCamera cameraId cameras
      jsonToCString (successResponse result)

-- | FFI: Get camera keyframes
foreign export ccall get_camera_keyframes_ffi :: CString -> IO CString
get_camera_keyframes_ffi :: CString -> IO CString
get_camera_keyframes_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (T.Text, HM.HashMap T.Text [CameraKeyframe]) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (cameraId, keyframes) -> do
      let result = getCameraKeyframes cameraId keyframes
      jsonToCString (successResponse result)

-- | FFI: Get active camera
foreign export ccall active_camera_ffi :: CString -> IO CString
active_camera_ffi :: CString -> IO CString
active_camera_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe T.Text, HM.HashMap T.Text Camera3D) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (mActiveId, cameras) -> do
      let result = activeCamera mActiveId cameras
      jsonToCString (successResponse result)
