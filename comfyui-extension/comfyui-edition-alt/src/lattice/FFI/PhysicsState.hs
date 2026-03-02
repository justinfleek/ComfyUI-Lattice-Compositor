-- |
-- Module      : Lattice.FFI.PhysicsState
-- Description : FFI bindings for physics state management
-- 
-- Foreign function interface for Lattice.State.Physics
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.PhysicsState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Foreign.C.Types (CDouble(..), CInt(..))
import Lattice.State.Physics
  ( radiansToDegrees
  , degreesToRadians
  , calculateBakeFrameRange
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
--                                                       // helper // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Convert radians to degrees
foreign export ccall radians_to_degrees_ffi :: CDouble -> IO CString
radians_to_degrees_ffi :: CDouble -> IO CString
radians_to_degrees_ffi radians = do
  let result = radiansToDegrees (realToFrac radians)
  jsonToCString (successResponse result)

-- | FFI: Convert degrees to radians
foreign export ccall degrees_to_radians_ffi :: CDouble -> IO CString
degrees_to_radians_ffi :: CDouble -> IO CString
degrees_to_radians_ffi degrees = do
  let result = degreesToRadians (realToFrac degrees)
  jsonToCString (successResponse result)

-- | FFI: Calculate bake frame range
foreign export ccall calculate_bake_frame_range_ffi :: CString -> IO CString
calculate_bake_frame_range_ffi :: CString -> IO CString
calculate_bake_frame_range_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe Int, Maybe Int, Int) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (mStartFrame, mEndFrame, compFrameCount) -> do
      let result = calculateBakeFrameRange mStartFrame mEndFrame compFrameCount
      jsonToCString (successResponse result)
