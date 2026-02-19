-- |
-- Module      : Lattice.FFI.TextAnimatorState
-- Description : FFI bindings for text animator state management
-- 
-- Foreign function interface for Lattice.State.TextAnimator
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.TextAnimatorState where

import Data.Aeson (Value(..), encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.State.TextAnimator
  ( getTextContent
  , hasTextAnimators
  , getTextAnimators
  , getTextAnimator
  , getTextPathConfig
  , hasTextPath
  , rgbaObjectToHex
  , hexToRgbaObject
  , isRgbaObject
  , Layer(..)
  , RGBA(..)
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

-- | FFI: Get text content
foreign export ccall get_text_content_ffi :: CString -> IO CString
get_text_content_ffi :: CString -> IO CString
get_text_content_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String Layer of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right layer -> do
      let result = getTextContent layer
      jsonToCString (successResponse result)

-- | FFI: Check if layer has text animators
foreign export ccall has_text_animators_ffi :: CString -> IO CString
has_text_animators_ffi :: CString -> IO CString
has_text_animators_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String Layer of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right layer -> do
      let result = hasTextAnimators layer
      jsonToCString (successResponse result)

-- | FFI: Get all text animators
foreign export ccall get_text_animators_ffi :: CString -> IO CString
get_text_animators_ffi :: CString -> IO CString
get_text_animators_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String Layer of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right layer -> do
      let result = getTextAnimators layer
      jsonToCString (successResponse result)

-- | FFI: Get text animator by ID
foreign export ccall get_text_animator_ffi :: CString -> IO CString
get_text_animator_ffi :: CString -> IO CString
get_text_animator_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (T.Text, Layer) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (animatorId, layer) -> do
      let result = getTextAnimator animatorId layer
      jsonToCString (successResponse result)

-- | FFI: Get text path config
foreign export ccall get_text_path_config_ffi :: CString -> IO CString
get_text_path_config_ffi :: CString -> IO CString
get_text_path_config_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String Layer of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right layer -> do
      let result = getTextPathConfig layer
      jsonToCString (successResponse result)

-- | FFI: Check if layer has text path
foreign export ccall has_text_path_ffi :: CString -> IO CString
has_text_path_ffi :: CString -> IO CString
has_text_path_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String Layer of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right layer -> do
      let result = hasTextPath layer
      jsonToCString (successResponse result)

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // helper // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Convert RGBA object to hex
foreign export ccall rgba_object_to_hex_ffi :: CString -> IO CString
rgba_object_to_hex_ffi :: CString -> IO CString
rgba_object_to_hex_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String RGBA of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right rgba -> do
      let result = rgbaObjectToHex rgba
      jsonToCString (successResponse result)

-- | FFI: Convert hex to RGBA object
foreign export ccall hex_to_rgba_object_ffi :: CString -> IO CString
hex_to_rgba_object_ffi :: CString -> IO CString
hex_to_rgba_object_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String T.Text of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right hex -> do
      let result = hexToRgbaObject hex
      jsonToCString (successResponse result)

-- | FFI: Check if value is RGBA object
foreign export ccall is_rgba_object_ffi :: CString -> IO CString
is_rgba_object_ffi :: CString -> IO CString
is_rgba_object_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String Value of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right value -> do
      let result = isRgbaObject value
      jsonToCString (successResponse result)
