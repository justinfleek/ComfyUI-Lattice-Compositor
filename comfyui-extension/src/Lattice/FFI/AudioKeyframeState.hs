-- |
-- Module      : Lattice.FFI.AudioKeyframeState
-- Description : FFI bindings for audio keyframe state management
-- 
-- Foreign function interface for Lattice.State.AudioKeyframe
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.AudioKeyframeState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Foreign.C.Types (CDouble, CInt)
import Lattice.State.AudioKeyframe
  ( applySmoothing
  , interpolateKeyframeValue
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
-- HELPER FUNCTIONS
-- ============================================================================

-- | FFI: Apply exponential smoothing
foreign export ccall apply_smoothing_ffi :: CString -> IO CString
apply_smoothing_ffi :: CString -> IO CString
apply_smoothing_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String ([Double], Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (values, factor) -> do
      let result = applySmoothing values factor
      jsonToCString (successResponse result)

-- | FFI: Interpolate keyframe value
foreign export ccall interpolate_keyframe_value_ffi :: CString -> IO CString
interpolate_keyframe_value_ffi :: CString -> IO CString
interpolate_keyframe_value_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Int, [(Int, Double)], Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (targetFrame, keyframes, defaultValue) -> do
      let result = interpolateKeyframeValue targetFrame keyframes defaultValue
      jsonToCString (successResponse result)
