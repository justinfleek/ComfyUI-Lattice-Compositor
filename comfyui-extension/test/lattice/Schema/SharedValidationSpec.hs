-- |
-- Test suite for Lattice.Schema.SharedValidation
--
-- Comprehensive tests for all validation functions matching Zod schema patterns

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Schema.SharedValidationSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
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
  , ValidationLimits(..)
  , defaultValidationLimits
  , updateLimits
  , getMaxDimension
  , getMaxFrameCount
  , getMaxArrayLength
  )
import Data.Text (Text)
import qualified Data.Text as T
import Data.Aeson (Value(..), object, (.=), Array)
import qualified Data.Vector as V

spec :: TestTree
spec = testGroup "Lattice.Schema.SharedValidation"
  [ testGroup "validateNonEmptyString"
    [ testCase "valid string" $
        validateNonEmptyString 100 "hello" @?= Right "hello"
    , testCase "empty string" $
        case validateNonEmptyString 100 "" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for empty string"
    , testCase "whitespace only" $
        case validateNonEmptyString 100 "   " of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for whitespace only"
    , testCase "trims whitespace" $
        validateNonEmptyString 100 "  hello  " @?= Right "hello"
    , testCase "exceeds max length" $
        case validateNonEmptyString 5 "hello world" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for string exceeding max length"
    , testCase "at max length" $
        let str = T.replicate 5 "a"
        in validateNonEmptyString 5 str @?= Right str
    ]
  , testGroup "validateIso8601DateTime"
    [ testCase "valid ISO 8601 datetime" $
        validateIso8601DateTime "2024-01-15T10:30:00Z" @?= Right "2024-01-15T10:30:00Z"
    , testCase "valid ISO 8601 with milliseconds" $
        validateIso8601DateTime "2024-01-15T10:30:00.123Z" @?= Right "2024-01-15T10:30:00.123Z"
    , testCase "invalid format" $
        case validateIso8601DateTime "2024-01-15" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for invalid format"
    , testCase "invalid date" $
        case validateIso8601DateTime "2024-13-45T99:99:99Z" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for invalid date"
    ]
  , testGroup "validateBase64OrDataUrl"
    [ testCase "valid base64" $
        validateBase64OrDataUrl "SGVsbG8gV29ybGQ=" @?= Right "SGVsbG8gV29ybGQ="
    , testCase "valid data URL" $
        validateBase64OrDataUrl "data:image/png;base64,iVBORw0KGgo=" @?= Right "data:image/png;base64,iVBORw0KGgo="
    , testCase "invalid base64 characters" $
        case validateBase64OrDataUrl "Hello World!" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for invalid base64 characters"
    , testCase "data URL without comma" $
        case validateBase64OrDataUrl "data:image/png" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for data URL without comma"
    ]
  , testGroup "validateMimeType"
    [ testCase "valid MIME type" $
        validateMimeType "image/png" @?= Right "image/png"
    , testCase "valid MIME type with subtype" $
        validateMimeType "application/json" @?= Right "application/json"
    , testCase "invalid format" $
        case validateMimeType "invalid" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for invalid MIME type format"
    , testCase "exceeds max length" $
        let longMime = T.replicate 101 "a"
        in case validateMimeType longMime of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for MIME type exceeding max length"
    ]
  , testGroup "validateHexColor"
    [ testCase "valid hex color 6 digits" $
        validateHexColor "#FF0000" @?= Right "#FF0000"
    , testCase "valid hex color 8 digits" $
        validateHexColor "#FF0000FF" @?= Right "#FF0000FF"
    , testCase "invalid format" $
        case validateHexColor "FF0000" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for hex color without #"
    , testCase "invalid characters" $
        case validateHexColor "#GG0000" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for invalid hex characters"
    ]
  , testGroup "validateEntityId"
    [ testCase "valid entity ID" $
        validateEntityId "my-entity_123" @?= Right "my-entity_123"
    , testCase "empty string" $
        case validateEntityId "" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for empty string"
    , testCase "exceeds max length" $
        let longId = T.replicate 201 "a"
        in case validateEntityId longId of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for ID exceeding max length"
    , testCase "invalid characters" $
        case validateEntityId "my entity" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for invalid characters"
    ]
  , testGroup "validatePropertyPath"
    [ testCase "valid property path" $
        validatePropertyPath "data.text" @?= Right "data.text"
    , testCase "valid nested path" $
        validatePropertyPath "transform.position.x" @?= Right "transform.position.x"
    , testCase "valid single property" $
        validatePropertyPath "name" @?= Right "name"
    , testCase "invalid format" $
        case validatePropertyPath "123invalid" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for property path starting with number"
    , testCase "exceeds max length" $
        let longPath = T.replicate 501 "a."
        in case validatePropertyPath longPath of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for path exceeding max length"
    ]
  , testGroup "validateFilename"
    [ testCase "valid filename" $
        validateFilename "myfile.txt" @?= Right "myfile.txt"
    , testCase "invalid characters" $
        case validateFilename "my<file>.txt" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for filename with invalid characters"
    , testCase "ends with dot" $
        case validateFilename "myfile." of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for filename ending with dot"
    , testCase "ends with space" $
        case validateFilename "myfile " of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for filename ending with space"
    , testCase "exceeds max length" $
        let longName = T.replicate 256 "a"
        in case validateFilename longName of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for filename exceeding max length"
    ]
  , testGroup "validateUrl"
    [ testCase "valid HTTP URL" $
        validateUrl "http://example.com" @?= Right "http://example.com"
    , testCase "valid HTTPS URL" $
        validateUrl "https://example.com" @?= Right "https://example.com"
    , testCase "invalid format" $
        case validateUrl "not-a-url" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for invalid URL format"
    , testCase "exceeds max length" $
        let longUrl = "https://example.com/" <> T.replicate 2100 "a"
        in case validateUrl longUrl of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for URL exceeding max length"
    ]
  , testGroup "validateShaderCode"
    [ testCase "valid shader code" $
        validateShaderCode "void main() { gl_FragColor = vec4(1.0); }" @?= Right "void main() { gl_FragColor = vec4(1.0); }"
    , testCase "contains eval" $
        case validateShaderCode "eval('bad')" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for shader code containing eval"
    , testCase "contains document" $
        case validateShaderCode "document.write('bad')" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for shader code containing document"
    , testCase "exceeds max length" $
        let longShader = T.replicate 100001 "a"
        in case validateShaderCode longShader of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for shader code exceeding max length"
    ]
  , testGroup "validateBoundedArray"
    [ testCase "valid array within bounds" $
        validateBoundedArray 10 [1, 2, 3] @?= Right [1, 2, 3]
    , testCase "array at max length" $
        validateBoundedArray 3 [1, 2, 3] @?= Right [1, 2, 3]
    , testCase "array exceeds max length" $
        case validateBoundedArray 2 [1, 2, 3] of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for array exceeding max length"
    , testCase "empty array" $
        validateBoundedArray 10 [] @?= Right []
    ]
  , testGroup "validateNonEmptyArray"
    [ testCase "valid non-empty array" $
        validateNonEmptyArray [1, 2, 3] @?= Right [1, 2, 3]
    , testCase "empty array" $
        case validateNonEmptyArray [] of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for empty array"
    ]
  , testGroup "validateJsonSerializable"
    [ testCase "valid JSON string" $
        validateJsonSerializable (String "hello") @?= Right (String "hello")
    , testCase "valid JSON number" $
        validateJsonSerializable (Number 42) @?= Right (Number 42)
    , testCase "valid JSON boolean" $
        validateJsonSerializable (Bool True) @?= Right (Bool True)
    , testCase "valid JSON null" $
        validateJsonSerializable Null @?= Right Null
    , testCase "valid JSON array" $
        validateJsonSerializable (Array (V.fromList [String "a", Number 1])) @?= Right (Array (V.fromList [String "a", Number 1]))
    , testCase "valid JSON object" $
        validateJsonSerializable (object ["key" .= ("value" :: Text)]) @?= Right (object ["key" .= ("value" :: Text)])
    ]
  , testGroup "ValidationLimits"
    [ testCase "default limits" $
        defaultValidationLimits @?= ValidationLimits
          { limitsMaxDimension = 8192
          , limitsMaxFrameCount = 10000
          , limitsMaxArrayLength = 100000
          , limitsMaxParticles = 1000000
          , limitsMaxLayers = 1000
          , limitsMaxKeyframesPerProperty = 10000
          , limitsMaxStringLength = 100000
          , limitsMaxFPS = 120
          }
    ]
  ]
