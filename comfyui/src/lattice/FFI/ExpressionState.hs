-- |
-- Module      : Lattice.FFI.ExpressionState
-- Description : FFI bindings for expression state management
-- 
-- Foreign function interface for Lattice.State.Expression
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.ExpressionState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.State.Expression (getDriversForLayer, PropertyDriver(..))

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
-- QUERY FUNCTIONS
-- ============================================================================

-- | FFI: Get drivers for layer
foreign export ccall get_drivers_for_layer_ffi :: CString -> IO CString
get_drivers_for_layer_ffi :: CString -> IO CString
get_drivers_for_layer_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (T.Text, [PropertyDriver]) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (layerId, drivers) -> do
      let result = getDriversForLayer layerId drivers
      jsonToCString (successResponse result)
