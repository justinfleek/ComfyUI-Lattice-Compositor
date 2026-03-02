-- |
-- Module      : Lattice.FFI.SchemaValidation
-- Description : FFI bindings for schema validation functions
--
-- Exports Haskell validation functions to C for Python/TypeScript interop
-- All functions use JSON strings for complex data, direct types for simple data

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Lattice.FFI.SchemaValidation where

import Foreign.C.String (CString, peekCString, newCString)
import Foreign.C.Types (CInt(..))
import Data.Aeson (encode, decode, Value(..), object, (.=))
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Vector as V
import Lattice.Schema.SharedValidation
  ( validateNonEmptyString
  , validateIso8601DateTime
  , validateBase64OrDataUrl
  , validateMimeType
  , validateHexColor
  , validateEntityId
  , validatePropertyPath
  , validateFilename
  , validateUrl
  , validateShaderCode
  , validateBoundedArray
  , validateNonEmptyArray
  , validateJsonSerializable
  , maxNameLength
  , maxIdLength
  , maxPathLength
  , maxFilenameLength
  , maxUrlLength
  , maxShaderLength
  , updateLimits
  , getMaxDimensionPure
  , getMaxFrameCountPure
  , getMaxArrayLengthPure
  , defaultValidationLimits
  , getMaxParticles
  , getMaxLayers
  , getMaxKeyframesPerProperty
  , getMaxStringLength
  , getMaxFPS
  , ValidationLimits(..)
  )

-- ============================================================================
-- JSON Response Helpers
-- ============================================================================

-- | Convert validation result to JSON CString
validationResultToCString :: Either T.Text T.Text -> IO CString
validationResultToCString (Left err) = do
  let resultJSON = object ["status" .= ("error" :: T.Text), "message" .= err]
  jsonToCString resultJSON
validationResultToCString (Right val) = do
  let resultJSON = object ["status" .= ("success" :: T.Text), "value" .= val]
  jsonToCString resultJSON

-- | Helper to convert JSON Value to CString
jsonToCString :: Value -> IO CString
jsonToCString resultJSON = do
  let resultBS = BSL.toStrict (encode resultJSON)
  let resultText = TE.decodeUtf8 resultBS
  newCString (T.unpack resultText)

-- ============================================================================
-- String Validation Functions
-- ============================================================================

foreign export ccall "validate_non_empty_string"
  c_validate_non_empty_string :: CString -> CInt -> IO CString

c_validate_non_empty_string :: CString -> CInt -> IO CString
c_validate_non_empty_string strPtr maxLen = do
  str <- peekCString strPtr
  let maxLenInt = fromIntegral maxLen
  validationResultToCString (validateNonEmptyString maxLenInt (T.pack str))

foreign export ccall "validate_iso8601_datetime"
  c_validate_iso8601_datetime :: CString -> IO CString

c_validate_iso8601_datetime :: CString -> IO CString
c_validate_iso8601_datetime strPtr = do
  str <- peekCString strPtr
  validationResultToCString (validateIso8601DateTime (T.pack str))

foreign export ccall "validate_base64_or_data_url"
  c_validate_base64_or_data_url :: CString -> IO CString

c_validate_base64_or_data_url :: CString -> IO CString
c_validate_base64_or_data_url strPtr = do
  str <- peekCString strPtr
  validationResultToCString (validateBase64OrDataUrl (T.pack str))

foreign export ccall "validate_mime_type"
  c_validate_mime_type :: CString -> IO CString

c_validate_mime_type :: CString -> IO CString
c_validate_mime_type strPtr = do
  str <- peekCString strPtr
  validationResultToCString (validateMimeType (T.pack str))

foreign export ccall "validate_hex_color"
  c_validate_hex_color :: CString -> IO CString

c_validate_hex_color :: CString -> IO CString
c_validate_hex_color strPtr = do
  str <- peekCString strPtr
  validationResultToCString (validateHexColor (T.pack str))

foreign export ccall "validate_entity_id"
  c_validate_entity_id :: CString -> IO CString

c_validate_entity_id :: CString -> IO CString
c_validate_entity_id strPtr = do
  str <- peekCString strPtr
  validationResultToCString (validateEntityId (T.pack str))

foreign export ccall "validate_property_path"
  c_validate_property_path :: CString -> IO CString

c_validate_property_path :: CString -> IO CString
c_validate_property_path strPtr = do
  str <- peekCString strPtr
  validationResultToCString (validatePropertyPath (T.pack str))

foreign export ccall "validate_filename"
  c_validate_filename :: CString -> IO CString

c_validate_filename :: CString -> IO CString
c_validate_filename strPtr = do
  str <- peekCString strPtr
  validationResultToCString (validateFilename (T.pack str))

foreign export ccall "validate_url"
  c_validate_url :: CString -> IO CString

c_validate_url :: CString -> IO CString
c_validate_url strPtr = do
  str <- peekCString strPtr
  validationResultToCString (validateUrl (T.pack str))

foreign export ccall "validate_shader_code"
  c_validate_shader_code :: CString -> IO CString

c_validate_shader_code :: CString -> IO CString
c_validate_shader_code strPtr = do
  str <- peekCString strPtr
  validationResultToCString (validateShaderCode (T.pack str))

-- ============================================================================
-- Array Validation Functions (JSON-based)
-- ============================================================================

foreign export ccall "validate_bounded_array"
  c_validate_bounded_array :: CString -> CInt -> IO CString

c_validate_bounded_array :: CString -> CInt -> IO CString
c_validate_bounded_array jsonPtr maxLen = do
  jsonStr <- peekCString jsonPtr
  case decode (BSL.fromStrict (TE.encodeUtf8 (T.pack jsonStr))) of
    Nothing -> do
      let resultJSON = object ["status" .= ("error" :: T.Text), "message" .= ("Invalid JSON" :: T.Text)]
      jsonToCString resultJSON
    Just (Array arr) -> do
      let maxLenInt = fromIntegral maxLen
      case validateBoundedArray maxLenInt (V.toList arr) of
        Left err -> do
          let resultJSON = object ["status" .= ("error" :: T.Text), "message" .= err]
          jsonToCString resultJSON
        Right _ -> do
          let resultJSON = object ["status" .= ("success" :: T.Text)]
          jsonToCString resultJSON
    Just _ -> do
      let resultJSON = object ["status" .= ("error" :: T.Text), "message" .= ("Expected array" :: T.Text)]
      jsonToCString resultJSON

foreign export ccall "validate_non_empty_array"
  c_validate_non_empty_array :: CString -> IO CString

c_validate_non_empty_array :: CString -> IO CString
c_validate_non_empty_array jsonPtr = do
  jsonStr <- peekCString jsonPtr
  case decode (BSL.fromStrict (TE.encodeUtf8 (T.pack jsonStr))) of
    Nothing -> do
      let resultJSON = object ["status" .= ("error" :: T.Text), "message" .= ("Invalid JSON" :: T.Text)]
      jsonToCString resultJSON
    Just (Array arr) -> do
      case validateNonEmptyArray (V.toList arr) of
        Left err -> do
          let resultJSON = object ["status" .= ("error" :: T.Text), "message" .= err]
          jsonToCString resultJSON
        Right _ -> do
          let resultJSON = object ["status" .= ("success" :: T.Text)]
          jsonToCString resultJSON
    Just _ -> do
      let resultJSON = object ["status" .= ("error" :: T.Text), "message" .= ("Expected array" :: T.Text)]
      jsonToCString resultJSON

foreign export ccall "validate_json_serializable"
  c_validate_json_serializable :: CString -> IO CString

c_validate_json_serializable :: CString -> IO CString
c_validate_json_serializable jsonPtr = do
  jsonStr <- peekCString jsonPtr
  case decode (BSL.fromStrict (TE.encodeUtf8 (T.pack jsonStr))) of
    Nothing -> do
      let resultJSON = object ["status" .= ("error" :: T.Text), "message" .= ("Invalid JSON" :: T.Text)]
      jsonToCString resultJSON
    Just val -> do
      case validateJsonSerializable val of
        Left err -> do
          let resultJSON = object ["status" .= ("error" :: T.Text), "message" .= err]
          jsonToCString resultJSON
        Right _ -> do
          let resultJSON = object ["status" .= ("success" :: T.Text)]
          jsonToCString resultJSON

-- ============================================================================
-- Limits Management Functions
-- ============================================================================

foreign export ccall "update_validation_limits"
  c_update_validation_limits :: CString -> IO CInt

c_update_validation_limits :: CString -> IO CInt
c_update_validation_limits jsonPtr = do
  jsonStr <- peekCString jsonPtr
  case decode @Value (BL.fromStrict (TE.encodeUtf8 (T.pack jsonStr))) of
    Nothing -> return (CInt 0)  -- Error
    Just val -> do
      -- TODO: Parse ValidationLimits from JSON
      -- For now, return success
      return (CInt 1)

foreign export ccall "get_max_dimension"
  c_get_max_dimension :: IO CInt

c_get_max_dimension :: IO CInt
c_get_max_dimension = return (CInt (fromIntegral (getMaxDimensionPure defaultValidationLimits)))

foreign export ccall "get_max_frame_count"
  c_get_max_frame_count :: IO CInt

c_get_max_frame_count :: IO CInt
c_get_max_frame_count = return (CInt (fromIntegral (getMaxFrameCountPure defaultValidationLimits)))

foreign export ccall "get_max_array_length"
  c_get_max_array_length :: IO CInt

c_get_max_array_length :: IO CInt
c_get_max_array_length = return (CInt (fromIntegral (getMaxArrayLengthPure defaultValidationLimits)))
