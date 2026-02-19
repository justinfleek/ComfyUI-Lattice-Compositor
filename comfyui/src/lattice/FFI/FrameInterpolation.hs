-- |
-- Module      : Lattice.FFI.FrameInterpolation
-- Description : C FFI exports for FrameInterpolation service
-- 
-- Exports Haskell functions as C-compatible functions for Python interop
-- This is a prototype implementation establishing the FFI pattern.
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.FrameInterpolation where

import Foreign.C.Types (CDouble(..), CInt(..))
import Foreign.C.String (CString, withCString, peekCString, newCString)
import Foreign.Ptr (Ptr)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Aeson (Value(..), object, (.=), (.:), (.:?), decode, encode, withObject, FromJSON(..), ToJSON(..))
import Data.Aeson.Key (fromString)

import Lattice.Services.FrameInterpolation
  ( slowdownToFactor
  , validateInterpolationParams
  , FrameInterpolationParams(..)
  )
import Lattice.Utils.NumericSafety (validateFinite)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // simple // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Export slowdownToFactor as C function
-- C signature: int slowdown_to_factor(double slowdown)
-- Pure function: no IO, direct type conversion
foreign export ccall "slowdown_to_factor"
  c_slowdown_to_factor :: CDouble -> CInt

c_slowdown_to_factor :: CDouble -> CInt
c_slowdown_to_factor (CDouble slowdown) = CInt (fromIntegral (slowdownToFactor slowdown))

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // complex // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Export validateInterpolationParams as C function
-- C signature: char* validate_interpolation_params(char* json_input)
-- Returns: JSON string with either error or validated params
-- Memory: Caller must free the returned CString using free()
-- 
-- Input JSON: {"modelName": "rife-v4.6", "factor": 2, "ensemble": false, "slowdown": null}
-- Output JSON: {"status": "success", "params": {...}} or {"status": "error", "message": "..."}
foreign export ccall "validate_interpolation_params"
  c_validate_interpolation_params :: CString -> IO CString

-- | Input JSON structure for validateInterpolationParams
-- Expected format: {"modelName": "rife-v4.6", "factor": 2, "ensemble": false, "slowdown": null}
data InterpolationParamsInput = InterpolationParamsInput
  { inputModelName :: Text
  , inputFactor :: Int
  , inputEnsemble :: Bool
  , inputSlowdown :: Maybe Double
  } deriving (Eq, Show)

instance FromJSON InterpolationParamsInput where
  parseJSON = withObject "InterpolationParamsInput" $ \o -> do
    modelName <- o .: fromString "modelName"
    factor <- o .: fromString "factor"
    ensemble <- o .: fromString "ensemble"
    mSlowdown <- o .:? fromString "slowdown"
    return $ InterpolationParamsInput modelName factor ensemble mSlowdown

-- | Output JSON structure (either error or success)
-- Error format: {"status": "error", "message": "..."}
-- Success format: {"status": "success", "params": {...}}
encodeResult :: Either Text FrameInterpolationParams -> Value
encodeResult (Left err) = object
  [ fromString "status" .= ("error" :: Text)
  , fromString "message" .= err
  ]
encodeResult (Right params) = object
  [ fromString "status" .= ("success" :: Text)
  , fromString "params" .= object
      [ fromString "modelName" .= paramsModelName params
      , fromString "factor" .= paramsFactor params
      , fromString "ensemble" .= paramsEnsemble params
      , fromString "slowdown" .= paramsSlowdown params
      ]
  ]

c_validate_interpolation_params :: CString -> IO CString
c_validate_interpolation_params jsonInput = do
  inputStr <- peekCString jsonInput
  -- Convert String to ByteString via UTF-8 encoding
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  
  -- Parse JSON input
  case decode (BSL.fromStrict inputBS) :: Maybe InterpolationParamsInput of
    Nothing -> do
      --                                                                      // json
      let errorResult = encodeResult (Left (T.pack "Invalid JSON input"))
      let resultJSON = BSL.toStrict (encode errorResult)
      -- Convert ByteString to CString (UTF-8 decode then CString)
      let resultText = TE.decodeUtf8 resultJSON
      newCString (T.unpack resultText)
    Just input -> do
      -- Call validation function
      let result = validateInterpolationParams
            (inputModelName input)
            (inputFactor input)
            (inputEnsemble input)
            (inputSlowdown input)
      
      -- Encode result to JSON
      let resultJSON = encodeResult result
      let resultBS = BSL.toStrict (encode resultJSON)
      -- Convert ByteString to CString (UTF-8 decode then CString)
      let resultText = TE.decodeUtf8 resultBS
      newCString (T.unpack resultText)
