-- |
-- Module      : Lattice.FFI.ValidationLimitsState
-- Description : C FFI bindings for validation limits pure functions
-- 
-- Exports pure functions from Lattice.State.ValidationLimits as C functions
-- for Python/TypeScript interop via JSON serialization
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.ValidationLimitsState where

import Data.Aeson
  ( decode
  , encode
  , ToJSON(..)
  , Value(..)
  , object
  , (.=)
  )
import qualified Data.ByteString.Lazy as BSL
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String
  ( CString
  , peekCString
  , newCString
  )
import Lattice.State.ValidationLimits
  ( getDefaultLimits
  , validateLimit
  , clampLimit
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                 // json // r
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert JSON Value to CString
jsonToCString :: Value -> IO CString
jsonToCString resultJSON = do
  let resultBS = BSL.toStrict (encode resultJSON)
  let resultText = TE.decodeUtf8 resultBS
  newCString (T.unpack resultText)

-- | Create error response JSON
errorResponse :: T.Text -> Value
errorResponse msg = object ["status" .= ("error" :: T.Text), "message" .= msg]

-- | Create success response JSON with result
successResponse :: ToJSON a => a -> Value
successResponse result = object ["status" .= ("success" :: T.Text), "result" .= result]

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // pure // constants
-- ════════════════════════════════════════════════════════════════════════════

-- | Get default validation limits
foreign export ccall "get_default_limits"
  c_get_default_limits :: IO CString

c_get_default_limits :: IO CString
c_get_default_limits = do
  let result = getDefaultLimits
  jsonToCString (successResponse result)

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // pure // validation
-- ════════════════════════════════════════════════════════════════════════════

-- | Validate a limit value
foreign export ccall "validate_limit"
  c_validate_limit :: CString -> CString -> IO CString

c_validate_limit :: CString -> CString -> IO CString
c_validate_limit limitJson absoluteMaxJson = do
  limitStr <- peekCString limitJson
  absoluteMaxStr <- peekCString absoluteMaxJson
  
  let limitBS = TE.encodeUtf8 (T.pack limitStr)
  let absoluteMaxBS = TE.encodeUtf8 (T.pack absoluteMaxStr)
  
  case (decode (BSL.fromStrict limitBS) :: Maybe Double,
        decode (BSL.fromStrict absoluteMaxBS) :: Maybe Double) of
    (Just limit, Just absoluteMax) -> do
      let result = validateLimit limit absoluteMax
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected Double and Double")

-- | Clamp a limit value
foreign export ccall "clamp_limit"
  c_clamp_limit :: CString -> CString -> IO CString

c_clamp_limit :: CString -> CString -> IO CString
c_clamp_limit limitJson absoluteMaxJson = do
  limitStr <- peekCString limitJson
  absoluteMaxStr <- peekCString absoluteMaxJson
  
  let limitBS = TE.encodeUtf8 (T.pack limitStr)
  let absoluteMaxBS = TE.encodeUtf8 (T.pack absoluteMaxStr)
  
  case (decode (BSL.fromStrict limitBS) :: Maybe Double,
        decode (BSL.fromStrict absoluteMaxBS) :: Maybe Double) of
    (Just limit, Just absoluteMax) -> do
      let result = clampLimit limit absoluteMax
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected Double and Double")
