-- |
-- Module      : Lattice.FFI.InterpolationState
-- Description : FFI bindings for interpolation service
-- 
-- Foreign function interface for Lattice.Utils.Interpolation
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.InterpolationState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.Utils.Interpolation
  ( normalizeHexColor
  , parseHexComponent
  , interpolateColor
  )

-- ============================================================================
-- JSON HELPERS
-- ============================================================================

-- | Create success response JSON
successResponse :: ToJSON a => a -> BSL.ByteString
successResponse result = encode $ object ["status" .= ("success" :: T.Text), "result" .= result]

-- | Create error response JSON
errorResponse :: T.Text -> BSL.ByteString
errorResponse msg = encode $ object ["status" .= ("error" :: T.Text), "message" .= msg]

-- | Convert ByteString to CString
jsonToCString :: BSL.ByteString -> IO CString
jsonToCString = newCString . T.unpack . TE.decodeUtf8 . BSL.toStrict

-- ============================================================================
-- COLOR INTERPOLATION FUNCTIONS
-- ============================================================================

-- | FFI: Normalize hex color
foreign export ccall normalize_hex_color_ffi :: CString -> IO CString
normalize_hex_color_ffi :: CString -> IO CString
normalize_hex_color_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String T.Text of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right hex -> do
      let result = normalizeHexColor hex
      jsonToCString (successResponse result)

-- | FFI: Parse hex color component
foreign export ccall parse_hex_component_ffi :: CString -> IO CString
parse_hex_component_ffi :: CString -> IO CString
parse_hex_component_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (T.Text, Int, Int) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (hex, start, end) -> do
      let result = parseHexComponent hex start end
      jsonToCString (successResponse result)

-- | FFI: Interpolate color
foreign export ccall interpolate_color_ffi :: CString -> IO CString
interpolate_color_ffi :: CString -> IO CString
interpolate_color_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (T.Text, T.Text, Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (c1, c2, t) -> do
      let result = interpolateColor c1 c2 t
      jsonToCString (successResponse result)
