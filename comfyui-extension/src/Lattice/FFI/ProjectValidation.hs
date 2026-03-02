-- |
-- Module      : Lattice.FFI.ProjectValidation
-- Description : C FFI exports for ProjectValidation service
-- 
-- Exports Haskell functions as C-compatible functions for Python interop
-- All functions use JSON for input/output since they work with Value types
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.ProjectValidation where

import Foreign.C.Types (CInt(..))
import Foreign.C.String (CString, peekCString, newCString)
import Foreign.Ptr (Ptr)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Aeson (Value(..), object, (.=), (.:), decode, encode, ToJSON(..))
import Data.Aeson.Key (fromString)
import Data.List (map)

import Lattice.Services.ProjectValidation
  ( calculateMaxDepth
  , validateExpressions
  , validateSingleExpression
  , validateNumericBounds
  , validatePaths
  , countLayers
  , validateStringLengths
  , validateArrayLengths
  , validateProjectId
  , ValidationError(..)
  , NumericBounds
  , defaultNumericBounds
  )

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | Convert ValidationError list to JSON
encodeValidationErrors :: [ValidationError] -> Value
encodeValidationErrors errors = object
  [ fromString "status" .= ("success" :: Text)
  , fromString "errors" .= map (\e -> object
        [ fromString "path" .= validationErrorPath e
        , fromString "message" .= validationErrorMessage e
        ]) errors
  ]

-- | Convert Int result to JSON
encodeIntResult :: Int -> Value
encodeIntResult n = object
  [ fromString "status" .= ("success" :: Text)
  , fromString "result" .= n
  ]

-- | Convert Bool result to JSON
encodeBoolResult :: Bool -> Value
encodeBoolResult b = object
  [ fromString "status" .= ("success" :: Text)
  , fromString "result" .= b
  ]

-- | Helper to parse JSON and return result as CString
jsonToCString :: Value -> IO CString
jsonToCString resultJSON = do
  let resultBS = BSL.toStrict (encode resultJSON)
  let resultText = TE.decodeUtf8 resultBS
  newCString (T.unpack resultText)

-- ============================================================================
-- VALIDATION FUNCTIONS (JSON-based)
-- ============================================================================

-- | Export calculateMaxDepth as C function
-- C signature: char* calculate_max_depth(char* json_input, int current_depth)
-- Returns: JSON with max depth
foreign export ccall "calculate_max_depth"
  c_calculate_max_depth :: CString -> CInt -> IO CString

c_calculate_max_depth :: CString -> CInt -> IO CString
c_calculate_max_depth jsonInput (CInt currentDepth) = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  
  case decode (BSL.fromStrict inputBS) :: Maybe Value of
    Nothing -> do
      let errorResult = object [fromString "status" .= ("error" :: Text), fromString "message" .= ("Invalid JSON input" :: Text)]
      jsonToCString errorResult
    Just val -> do
      let maxDepth = calculateMaxDepth val (fromIntegral currentDepth)
      jsonToCString (encodeIntResult maxDepth)

-- | Export validateExpressions as C function
-- C signature: char* validate_expressions(char* json_input, char* path)
-- Returns: JSON array of validation errors
foreign export ccall "validate_expressions"
  c_validate_expressions :: CString -> CString -> IO CString

c_validate_expressions :: CString -> CString -> IO CString
c_validate_expressions jsonInput pathPtr = do
  inputStr <- peekCString jsonInput
  pathStr <- peekCString pathPtr
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  
  case decode (BSL.fromStrict inputBS) :: Maybe Value of
    Nothing -> do
      let errorResult = object [fromString "status" .= ("error" :: Text), fromString "message" .= ("Invalid JSON input" :: Text)]
      jsonToCString errorResult
    Just val -> do
      let errors = validateExpressions val (T.pack pathStr)
      jsonToCString (encodeValidationErrors errors)

-- | Export validateSingleExpression as C function
-- C signature: char* validate_single_expression(char* expression, char* path)
-- Returns: JSON array of validation errors
foreign export ccall "validate_single_expression"
  c_validate_single_expression :: CString -> CString -> IO CString

c_validate_single_expression :: CString -> CString -> IO CString
c_validate_single_expression exprPtr pathPtr = do
  exprStr <- peekCString exprPtr
  pathStr <- peekCString pathPtr
  let errors = validateSingleExpression (T.pack exprStr) (T.pack pathStr)
  jsonToCString (encodeValidationErrors errors)

-- | Export validateNumericBounds as C function
-- C signature: char* validate_numeric_bounds(char* json_input, char* path)
-- Returns: JSON array of validation errors (uses default bounds)
foreign export ccall "validate_numeric_bounds"
  c_validate_numeric_bounds :: CString -> CString -> IO CString

c_validate_numeric_bounds :: CString -> CString -> IO CString
c_validate_numeric_bounds jsonInput pathPtr = do
  inputStr <- peekCString jsonInput
  pathStr <- peekCString pathPtr
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  
  case decode (BSL.fromStrict inputBS) :: Maybe Value of
    Nothing -> do
      let errorResult = object [fromString "status" .= ("error" :: Text), fromString "message" .= ("Invalid JSON input" :: Text)]
      jsonToCString errorResult
    Just val -> do
      let errors = validateNumericBounds val (T.pack pathStr) defaultNumericBounds
      jsonToCString (encodeValidationErrors errors)

-- | Export validatePaths as C function
-- C signature: char* validate_paths(char* json_input, char* path)
-- Returns: JSON array of validation errors
foreign export ccall "validate_paths"
  c_validate_paths :: CString -> CString -> IO CString

c_validate_paths :: CString -> CString -> IO CString
c_validate_paths jsonInput pathPtr = do
  inputStr <- peekCString jsonInput
  pathStr <- peekCString pathPtr
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  
  case decode (BSL.fromStrict inputBS) :: Maybe Value of
    Nothing -> do
      let errorResult = object [fromString "status" .= ("error" :: Text), fromString "message" .= ("Invalid JSON input" :: Text)]
      jsonToCString errorResult
    Just val -> do
      let errors = validatePaths val (T.pack pathStr)
      jsonToCString (encodeValidationErrors errors)

-- | Export countLayers as C function
-- C signature: char* count_layers(char* json_input)
-- Returns: JSON with layer count
foreign export ccall "count_layers"
  c_count_layers :: CString -> IO CString

c_count_layers :: CString -> IO CString
c_count_layers jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  
  case decode (BSL.fromStrict inputBS) :: Maybe Value of
    Nothing -> do
      let errorResult = object [fromString "status" .= ("error" :: Text), fromString "message" .= ("Invalid JSON input" :: Text)]
      jsonToCString errorResult
    Just val -> do
      let count = countLayers val
      jsonToCString (encodeIntResult count)

-- | Export validateStringLengths as C function
-- C signature: char* validate_string_lengths(char* json_input, char* path)
-- Returns: JSON array of validation errors
foreign export ccall "validate_string_lengths"
  c_validate_string_lengths :: CString -> CString -> IO CString

c_validate_string_lengths :: CString -> CString -> IO CString
c_validate_string_lengths jsonInput pathPtr = do
  inputStr <- peekCString jsonInput
  pathStr <- peekCString pathPtr
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  
  case decode (BSL.fromStrict inputBS) :: Maybe Value of
    Nothing -> do
      let errorResult = object [fromString "status" .= ("error" :: Text), fromString "message" .= ("Invalid JSON input" :: Text)]
      jsonToCString errorResult
    Just val -> do
      let errors = validateStringLengths val (T.pack pathStr)
      jsonToCString (encodeValidationErrors errors)

-- | Export validateArrayLengths as C function
-- C signature: char* validate_array_lengths(char* json_input, char* path)
-- Returns: JSON array of validation errors
foreign export ccall "validate_array_lengths"
  c_validate_array_lengths :: CString -> CString -> IO CString

c_validate_array_lengths :: CString -> CString -> IO CString
c_validate_array_lengths jsonInput pathPtr = do
  inputStr <- peekCString jsonInput
  pathStr <- peekCString pathPtr
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  
  case decode (BSL.fromStrict inputBS) :: Maybe Value of
    Nothing -> do
      let errorResult = object [fromString "status" .= ("error" :: Text), fromString "message" .= ("Invalid JSON input" :: Text)]
      jsonToCString errorResult
    Just val -> do
      let errors = validateArrayLengths val (T.pack pathStr)
      jsonToCString (encodeValidationErrors errors)

-- | Export validateProjectId as C function
-- C signature: int validate_project_id(char* project_id)
-- Returns: 1 if valid, 0 otherwise
foreign export ccall "validate_project_id"
  c_validate_project_id :: CString -> IO CInt

c_validate_project_id :: CString -> IO CInt
c_validate_project_id projectIdPtr = do
  projectIdStr <- peekCString projectIdPtr
  if validateProjectId (T.pack projectIdStr)
    then return (CInt 1)
    else return (CInt 0)
