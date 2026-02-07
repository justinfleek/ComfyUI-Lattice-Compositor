-- | Lattice.Schemas.SharedValidation - Shared validation constants and helpers
-- |
-- | Common validation constraints used across all schemas.
-- | Ensures consistency and prevents security issues.
-- |
-- | Source: leancomfy/lean/Lattice/Schemas/SharedValidation.lean

module Lattice.Schemas.SharedValidation
  ( -- Fixed Constants
    maxNameLength
  , maxDescriptionLength
  , maxCommentLength
  , maxTagLength
  , maxTagsCount
  , maxPathLength
  , maxIdLength
  , maxMimeTypeLength
  , maxFontFamilyLength
  , maxFontStyleLength
  , maxUrlLength
  , maxBase64Length
  , maxShaderLength
  , maxFilenameLength
  , maxAnimationNameLength
  , maxWarningLength
    -- Configurable Limits
  , ValidationLimitsConfig
  , defaultLimits
    -- Validation Error
  , ValidationError
  , mkError
    -- String Validation
  , validateNonEmptyString
  , validateString
  , validateHexColor
  , validateEntityId
  , validateFilename
    -- Number Validation
  , validatePositiveInt
  , validateNonNegativeInt
  , validatePositiveFloat
  , validateNonNegativeFloat
    -- Array Validation
  , validateArrayLength
  , validateNonEmptyArray
    -- Date/Time Validation
  , validateDateTime
  , validateDate
  ) where

import Prelude
import Data.Array as Array
import Data.Either (Either(..))
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodeUnits as SCU
import Data.String.Pattern (Pattern(..))
import Data.Number as Number

--------------------------------------------------------------------------------
-- Fixed Constants (Security Critical)
--------------------------------------------------------------------------------

maxNameLength :: Int
maxNameLength = 200

maxDescriptionLength :: Int
maxDescriptionLength = 2000

maxCommentLength :: Int
maxCommentLength = 5000

maxTagLength :: Int
maxTagLength = 50

maxTagsCount :: Int
maxTagsCount = 50

maxPathLength :: Int
maxPathLength = 500

maxIdLength :: Int
maxIdLength = 200

maxMimeTypeLength :: Int
maxMimeTypeLength = 100

maxFontFamilyLength :: Int
maxFontFamilyLength = 200

maxFontStyleLength :: Int
maxFontStyleLength = 100

maxUrlLength :: Int
maxUrlLength = 2048

maxBase64Length :: Int
maxBase64Length = 50 * 1024 * 1024  -- 50MB

maxShaderLength :: Int
maxShaderLength = 100000

maxFilenameLength :: Int
maxFilenameLength = 255

maxAnimationNameLength :: Int
maxAnimationNameLength = 100

maxWarningLength :: Int
maxWarningLength = 500

--------------------------------------------------------------------------------
-- Configurable Limits
--------------------------------------------------------------------------------

-- | Configurable validation limits
type ValidationLimitsConfig =
  { maxDimension :: Int
  , maxFrameCount :: Int
  , maxArrayLength :: Int
  , maxParticles :: Int
  , maxLayers :: Int
  , maxKeyframesPerProperty :: Int
  , maxStringLength :: Int
  , maxFPS :: Int
  }

-- | Default limits
defaultLimits :: ValidationLimitsConfig
defaultLimits =
  { maxDimension: 8192
  , maxFrameCount: 10000
  , maxArrayLength: 100000
  , maxParticles: 1000000
  , maxLayers: 1000
  , maxKeyframesPerProperty: 10000
  , maxStringLength: 100000
  , maxFPS: 120
  }

--------------------------------------------------------------------------------
-- Validation Error
--------------------------------------------------------------------------------

-- | Validation error with field and message
type ValidationError =
  { field :: String
  , message :: String
  }

-- | Create a validation error
mkError :: String -> String -> ValidationError
mkError field message = { field, message }

--------------------------------------------------------------------------------
-- String Validation
--------------------------------------------------------------------------------

-- | Validate non-empty string with max length
validateNonEmptyString :: String -> Int -> String -> Either ValidationError String
validateNonEmptyString field maxLen value
  | String.null value = Left $ mkError field "must not be empty"
  | String.length value > maxLen = Left $ mkError field $
      "must be at most " <> show maxLen <> " characters"
  | otherwise = Right $ String.trim value

-- | Validate string with max length (can be empty)
validateString :: String -> Int -> String -> Either ValidationError String
validateString field maxLen value
  | String.length value > maxLen = Left $ mkError field $
      "must be at most " <> show maxLen <> " characters"
  | otherwise = Right $ String.trim value

-- | Check if character is hex digit
isHexDigit :: Char -> Boolean
isHexDigit c =
  (c >= '0' && c <= '9') ||
  (c >= 'a' && c <= 'f') ||
  (c >= 'A' && c <= 'F')

-- | Validate hex color format
validateHexColor :: String -> String -> Either ValidationError String
validateHexColor field value =
  let len = String.length value
      chars = SCU.toCharArray (String.drop 1 value)
      allHex = Array.all isHexDigit chars
  in if len == 7 && String.take 1 value == "#" && allHex
     then Right value
     else if len == 9 && String.take 1 value == "#" && allHex
     then Right value
     else Left $ mkError field "must be valid hex color (#RRGGBB or #RRGGBBAA)"

-- | Check if character is valid ID char
isIdChar :: Char -> Boolean
isIdChar c =
  (c >= 'a' && c <= 'z') ||
  (c >= 'A' && c <= 'Z') ||
  (c >= '0' && c <= '9') ||
  c == '_' || c == '-'

-- | Validate entity ID format
validateEntityId :: String -> String -> Either ValidationError String
validateEntityId field value
  | String.null value = Left $ mkError field "must not be empty"
  | String.length value > maxIdLength = Left $ mkError field $
      "must be at most " <> show maxIdLength <> " characters"
  | not (Array.all isIdChar (SCU.toCharArray value)) = Left $ mkError field
      "must contain only alphanumeric, underscores, and hyphens"
  | otherwise = Right value

-- | Invalid filename characters
invalidFilenameChars :: Array String
invalidFilenameChars = ["<", ">", ":", "\"", "|", "?", "*"]

-- | Validate filename
validateFilename :: String -> String -> Either ValidationError String
validateFilename field value
  | String.length value > maxFilenameLength = Left $ mkError field $
      "must be at most " <> show maxFilenameLength <> " characters"
  | Array.any (\c -> String.contains (Pattern c) value) invalidFilenameChars =
      Left $ mkError field "contains invalid characters"
  | String.take 1 (String.takeEnd 1 value) == "." ||
    String.take 1 (String.takeEnd 1 value) == " " =
      Left $ mkError field "must not end with dot or space"
  | otherwise = Right value

--------------------------------------------------------------------------------
-- Number Validation
--------------------------------------------------------------------------------

-- | Validate positive integer with max
validatePositiveInt :: String -> Int -> Int -> Either ValidationError Int
validatePositiveInt field maxVal value
  | value <= 0 = Left $ mkError field "must be positive"
  | value > maxVal = Left $ mkError field $ "must be at most " <> show maxVal
  | otherwise = Right value

-- | Validate non-negative integer with max
validateNonNegativeInt :: String -> Int -> Int -> Either ValidationError Int
validateNonNegativeInt field maxVal value
  | value < 0 = Left $ mkError field "must be non-negative"
  | value > maxVal = Left $ mkError field $ "must be at most " <> show maxVal
  | otherwise = Right value

-- | Validate positive float with max
validatePositiveFloat :: String -> Number -> Number -> Either ValidationError Number
validatePositiveFloat field maxVal value
  | value <= 0.0 = Left $ mkError field "must be positive"
  | Number.isNaN value || not (Number.isFinite value) =
      Left $ mkError field "must be finite"
  | value > maxVal = Left $ mkError field $ "must be at most " <> show maxVal
  | otherwise = Right value

-- | Validate non-negative float with max
validateNonNegativeFloat :: String -> Number -> Number -> Either ValidationError Number
validateNonNegativeFloat field maxVal value
  | value < 0.0 = Left $ mkError field "must be non-negative"
  | Number.isNaN value || not (Number.isFinite value) =
      Left $ mkError field "must be finite"
  | value > maxVal = Left $ mkError field $ "must be at most " <> show maxVal
  | otherwise = Right value

--------------------------------------------------------------------------------
-- Array Validation
--------------------------------------------------------------------------------

-- | Validate array length
validateArrayLength :: forall a. String -> Int -> Array a -> Either ValidationError (Array a)
validateArrayLength field maxLen arr
  | Array.length arr > maxLen = Left $ mkError field $
      "must have at most " <> show maxLen <> " elements"
  | otherwise = Right arr

-- | Validate non-empty array
validateNonEmptyArray :: forall a. String -> Array a -> Either ValidationError (Array a)
validateNonEmptyArray field arr
  | Array.null arr = Left $ mkError field "must not be empty"
  | otherwise = Right arr

--------------------------------------------------------------------------------
-- Date/Time Validation
--------------------------------------------------------------------------------

-- | Validate ISO 8601 datetime format (simplified)
validateDateTime :: String -> String -> Either ValidationError String
validateDateTime field value
  | String.length value < 19 = Left $ mkError field "must be valid ISO 8601 datetime"
  | hasValidStructure = Right value
  | otherwise = Left $ mkError field "must be valid ISO 8601 datetime"
  where
    dateTimePart = String.take 19 value
    hasValidStructure =
      String.take 1 (String.drop 4 dateTimePart) == "-" &&
      String.take 1 (String.drop 7 dateTimePart) == "-" &&
      String.take 1 (String.drop 10 dateTimePart) == "T" &&
      String.take 1 (String.drop 13 dateTimePart) == ":" &&
      String.take 1 (String.drop 16 dateTimePart) == ":"

-- | Validate date format YYYY-MM-DD
validateDate :: String -> String -> Either ValidationError String
validateDate field value
  | String.length value /= 10 = Left $ mkError field "must be YYYY-MM-DD format"
  | String.take 1 (String.drop 4 value) == "-" &&
    String.take 1 (String.drop 7 value) == "-" = Right value
  | otherwise = Left $ mkError field "must be YYYY-MM-DD format"
