-- |
-- Module      : Lattice.FFI.KeyframeState
-- Description : FFI bindings for keyframe state management
-- 
-- Foreign function interface for Lattice.State.Keyframe
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.KeyframeState where

import Data.Aeson (encode, eitherDecode, object, (.=), Value, ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.State.Keyframe
  ( safeFrame
  , findPropertyByPath
  , findSurroundingKeyframes
  , hasKeyframesInClipboard
  , hasPositionSeparated
  , hasScaleSeparated
  , Layer(..)
  , AnimatableProperty(..)
  , ClipboardKeyframe(..)
  )
import Lattice.State.Keyframe.Evaluation (getPropertyValueAtFrame)

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

-- | FFI: Safe frame validation
foreign export ccall safe_frame_ffi :: CString -> IO CString
safe_frame_ffi :: CString -> IO CString
safe_frame_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe Double, Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (mFrame, fallback) -> do
      let result = safeFrame mFrame fallback
      jsonToCString (successResponse result)

-- | FFI: Find property by path
foreign export ccall find_property_by_path_ffi :: CString -> IO CString
find_property_by_path_ffi :: CString -> IO CString
find_property_by_path_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Layer, T.Text) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (layer, propertyPath) -> do
      let result = findPropertyByPath layer propertyPath
      jsonToCString (successResponse result)

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // query // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Find surrounding keyframes
foreign export ccall find_surrounding_keyframes_ffi :: CString -> IO CString
find_surrounding_keyframes_ffi :: CString -> IO CString
find_surrounding_keyframes_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (AnimatableProperty Value, Int) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (property, frame) -> do
      let result = findSurroundingKeyframes property frame
      jsonToCString (successResponse result)

-- | FFI: Check if clipboard has keyframes
foreign export ccall has_keyframes_in_clipboard_ffi :: CString -> IO CString
has_keyframes_in_clipboard_ffi :: CString -> IO CString
has_keyframes_in_clipboard_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String [ClipboardKeyframe] of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right clipboard -> do
      let result = hasKeyframesInClipboard clipboard
      jsonToCString (successResponse result)

-- | FFI: Check if position dimensions are separated
foreign export ccall has_position_separated_ffi :: CString -> IO CString
has_position_separated_ffi :: CString -> IO CString
has_position_separated_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String Layer of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right layer -> do
      let result = hasPositionSeparated layer
      jsonToCString (successResponse result)

-- | FFI: Check if scale dimensions are separated
foreign export ccall has_scale_separated_ffi :: CString -> IO CString
has_scale_separated_ffi :: CString -> IO CString
has_scale_separated_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String Layer of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right layer -> do
      let result = hasScaleSeparated layer
      jsonToCString (successResponse result)

-- | FFI: Get property value at frame (main evaluation function)
foreign export ccall get_property_value_at_frame_ffi :: CString -> IO CString
get_property_value_at_frame_ffi :: CString -> IO CString
get_property_value_at_frame_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (T.Text, T.Text, Double, [Layer]) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (layerId, propertyPath, frame, layers) -> do
      case getPropertyValueAtFrame layerId propertyPath frame layers of
        Left errMsg -> jsonToCString (errorResponse errMsg)
        Right value -> jsonToCString (successResponse value)
