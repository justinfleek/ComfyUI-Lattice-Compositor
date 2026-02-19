-- |
-- Module      : Lattice.FFI.DepthflowState
-- Description : FFI bindings for depthflow state management
-- 
-- Foreign function interface for Lattice.State.Depthflow
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.DepthflowState where

import Data.Aeson (encode, eitherDecode, object, (.=), Value, ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Foreign.C.Types (CDouble)
import Lattice.State.Depthflow (sanitizeNumber)

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

-- | FFI: Sanitize numeric config value
foreign export ccall sanitize_number_ffi :: CString -> IO CString
sanitize_number_ffi :: CString -> IO CString
sanitize_number_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Value, Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (value, defaultValue) -> do
      let result = sanitizeNumber value defaultValue
      jsonToCString (successResponse result)
