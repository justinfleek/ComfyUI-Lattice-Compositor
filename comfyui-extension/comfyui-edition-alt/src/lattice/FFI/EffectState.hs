-- |
-- Module      : Lattice.FFI.EffectState
-- Description : FFI bindings for effect state management
-- 
-- Foreign function interface for Lattice.State.Effect
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.EffectState where

import Data.Aeson (encode, eitherDecode, object, (.=), Value, ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.State.Effect
  ( hasStylesInClipboard
  , getStylesFromClipboard
  , getStylePresetNames
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

-- | FFI: Check if styles clipboard has content
foreign export ccall has_styles_in_clipboard_ffi :: CString -> IO CString
has_styles_in_clipboard_ffi :: CString -> IO CString
has_styles_in_clipboard_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe Value) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right mClipboard -> do
      let result = hasStylesInClipboard mClipboard
      jsonToCString (successResponse result)

-- | FFI: Get styles from clipboard
foreign export ccall get_styles_from_clipboard_ffi :: CString -> IO CString
get_styles_from_clipboard_ffi :: CString -> IO CString
get_styles_from_clipboard_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe Value) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right mClipboard -> do
      let result = getStylesFromClipboard mClipboard
      jsonToCString (successResponse result)

-- | FFI: Get style preset names
foreign export ccall get_style_preset_names_ffi :: CString -> IO CString
get_style_preset_names_ffi :: CString -> IO CString
get_style_preset_names_ffi _inputCStr = do
  let result = getStylePresetNames
  jsonToCString (successResponse result)
