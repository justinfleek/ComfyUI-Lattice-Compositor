-- |
-- Module      : Lattice.FFI.DecompositionState
-- Description : FFI bindings for decomposition state management
-- 
-- Foreign function interface for Lattice.State.Decomposition
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.DecompositionState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.State.Decomposition (sortLayersByDepth)

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

-- | FFI: Sort layers by depth
foreign export ccall sort_layers_by_depth_ffi :: CString -> IO CString
sort_layers_by_depth_ffi :: CString -> IO CString
sort_layers_by_depth_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  -- Note: Using Value for generic layer type, depth as Maybe Double
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String [(T.Text, Maybe Double)] of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right layers -> do
      let result = sortLayersByDepth layers
      jsonToCString (successResponse result)
