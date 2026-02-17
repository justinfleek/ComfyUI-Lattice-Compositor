-- |
-- Module      : Lattice.FFI.ParticleState
-- Description : FFI bindings for particle state management
-- 
-- Foreign function interface for Lattice.State.Particle
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.ParticleState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.State.Particle (exportTrajectoriesToJSON, ParticleBakeResult(..))

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
-- EXPORT FUNCTIONS
-- ============================================================================

-- | FFI: Export trajectories to JSON
foreign export ccall export_trajectories_to_json_ffi :: CString -> IO CString
export_trajectories_to_json_ffi :: CString -> IO CString
export_trajectories_to_json_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String ParticleBakeResult of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right result -> do
      let jsonStr = exportTrajectoriesToJSON result
      jsonToCString (successResponse jsonStr)
