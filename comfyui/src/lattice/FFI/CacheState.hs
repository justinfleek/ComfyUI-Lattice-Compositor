-- |
-- Module      : Lattice.FFI.CacheState
-- Description : FFI bindings for cache state management
-- 
-- Foreign function interface for Lattice.State.Cache
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.CacheState where

import Data.Aeson (encode, eitherDecode, object, (.=), Value, ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.State.Cache (computeProjectHash)

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
-- HELPER FUNCTIONS
-- ============================================================================

-- | FFI: Compute project hash
foreign export ccall compute_project_hash_ffi :: CString -> IO CString
compute_project_hash_ffi :: CString -> IO CString
compute_project_hash_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (T.Text, T.Text, Int, [T.Text], Value) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (compId, modified, layerCount, layerIds, settings) -> do
      let result = computeProjectHash compId modified layerCount layerIds settings
      jsonToCString (successResponse result)
