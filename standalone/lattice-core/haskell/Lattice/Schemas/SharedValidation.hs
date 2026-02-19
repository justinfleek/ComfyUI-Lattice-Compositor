{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.SharedValidation
Description : Shared validation constants and helpers
Copyright   : (c) Lattice, 2026
License     : MIT

Common validation constraints used across all schemas.
Ensures consistency and prevents security issues.

Source: lattice-core/lean/Lattice/Schemas/SharedValidation.lean
-}

module Lattice.Schemas.SharedValidation
  ( -- * Fixed Constants
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
    -- * Configurable Limits
  , ValidationLimitsConfig(..)
  , defaultLimits
    -- * Validation Error
  , ValidationError(..)
  , mkError
    -- * String Validation
  , validateNonEmptyString
  , validateString
  , validateHexColor
  , validateEntityId
  , validateFilename
    -- * Number Validation
  , validatePositiveInt
  , validateNonNegativeInt
  , validatePositiveFloat
  , validateNonNegativeFloat
    -- * Array Validation
  , validateArrayLength
  , validateNonEmptyArray
    -- * Date/Time Validation
  , validateDateTime
  , validateDate
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Char (isAlphaNum, isHexDigit)

-- ────────────────────────────────────────────────────────────────────────────
-- Fixed Constants (Security Critical)
-- ────────────────────────────────────────────────────────────────────────────

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

-- ────────────────────────────────────────────────────────────────────────────
-- Configurable Limits
-- ────────────────────────────────────────────────────────────────────────────

-- | Configurable validation limits
data ValidationLimitsConfig = ValidationLimitsConfig
  { limitsMaxDimension :: !Int
  , limitsMaxFrameCount :: !Int
  , limitsMaxArrayLength :: !Int
  , limitsMaxParticles :: !Int
  , limitsMaxLayers :: !Int
  , limitsMaxKeyframesPerProperty :: !Int
  , limitsMaxStringLength :: !Int
  , limitsMaxFPS :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | Default limits
defaultLimits :: ValidationLimitsConfig
defaultLimits = ValidationLimitsConfig
  { limitsMaxDimension = 8192
  , limitsMaxFrameCount = 10000
  , limitsMaxArrayLength = 100000
  , limitsMaxParticles = 1000000
  , limitsMaxLayers = 1000
  , limitsMaxKeyframesPerProperty = 10000
  , limitsMaxStringLength = 100000
  , limitsMaxFPS = 120
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Validation Error
-- ────────────────────────────────────────────────────────────────────────────

-- | Validation error with field and message
data ValidationError = ValidationError
  { errorField :: !Text
  , errorMessage :: !Text
  }
  deriving stock (Eq, Show, Generic)

-- | Create a validation error
mkError :: Text -> Text -> ValidationError
mkError field message = ValidationError
  { errorField = field
  , errorMessage = message
  }

-- ────────────────────────────────────────────────────────────────────────────
-- String Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate non-empty string with max length
validateNonEmptyString :: Text -> Int -> Text -> Either ValidationError Text
validateNonEmptyString field maxLen value
  | T.null value = Left $ mkError field "must not be empty"
  | T.length value > maxLen = Left $ mkError field $
      "must be at most " <> T.pack (show maxLen) <> " characters"
  | otherwise = Right $ T.strip value

-- | Validate string with max length (can be empty)
validateString :: Text -> Int -> Text -> Either ValidationError Text
validateString field maxLen value
  | T.length value > maxLen = Left $ mkError field $
      "must be at most " <> T.pack (show maxLen) <> " characters"
  | otherwise = Right $ T.strip value

-- | Validate hex color format
validateHexColor :: Text -> Text -> Either ValidationError Text
validateHexColor field value
  | T.length value == 7 && T.head value == '#' && T.all isHexDigit (T.tail value) = Right value
  | T.length value == 9 && T.head value == '#' && T.all isHexDigit (T.tail value) = Right value
  | otherwise = Left $ mkError field "must be valid hex color (#RRGGBB or #RRGGBBAA)"

-- | Validate entity ID format
validateEntityId :: Text -> Text -> Either ValidationError Text
validateEntityId field value
  | T.null value = Left $ mkError field "must not be empty"
  | T.length value > maxIdLength = Left $ mkError field $
      "must be at most " <> T.pack (show maxIdLength) <> " characters"
  | not (T.all isIdChar value) = Left $ mkError field
      "must contain only alphanumeric, underscores, and hyphens"
  | otherwise = Right value
  where
    isIdChar c = isAlphaNum c || c == '_' || c == '-'

-- | Validate filename
validateFilename :: Text -> Text -> Either ValidationError Text
validateFilename field value
  | T.length value > maxFilenameLength = Left $ mkError field $
      "must be at most " <> T.pack (show maxFilenameLength) <> " characters"
  | T.any (`elem` invalidChars) value = Left $ mkError field "contains invalid characters"
  | T.isSuffixOf "." value || T.isSuffixOf " " value = Left $ mkError field
      "must not end with dot or space"
  | otherwise = Right value
  where
    invalidChars :: [Char]
    invalidChars = ['<', '>', ':', '"', '|', '?', '*']

-- ────────────────────────────────────────────────────────────────────────────
-- Number Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate positive integer with max
validatePositiveInt :: Text -> Int -> Int -> Either ValidationError Int
validatePositiveInt field maxVal value
  | value <= 0 = Left $ mkError field "must be positive"
  | value > maxVal = Left $ mkError field $ "must be at most " <> T.pack (show maxVal)
  | otherwise = Right value

-- | Validate non-negative integer with max
validateNonNegativeInt :: Text -> Int -> Int -> Either ValidationError Int
validateNonNegativeInt field maxVal value
  | value < 0 = Left $ mkError field "must be non-negative"
  | value > maxVal = Left $ mkError field $ "must be at most " <> T.pack (show maxVal)
  | otherwise = Right value

-- | Validate positive float with max
validatePositiveFloat :: Text -> Double -> Double -> Either ValidationError Double
validatePositiveFloat field maxVal value
  | value <= 0 = Left $ mkError field "must be positive"
  | isNaN value || isInfinite value = Left $ mkError field "must be finite"
  | value > maxVal = Left $ mkError field $ "must be at most " <> T.pack (show maxVal)
  | otherwise = Right value

-- | Validate non-negative float with max
validateNonNegativeFloat :: Text -> Double -> Double -> Either ValidationError Double
validateNonNegativeFloat field maxVal value
  | value < 0 = Left $ mkError field "must be non-negative"
  | isNaN value || isInfinite value = Left $ mkError field "must be finite"
  | value > maxVal = Left $ mkError field $ "must be at most " <> T.pack (show maxVal)
  | otherwise = Right value

-- ────────────────────────────────────────────────────────────────────────────
-- Array Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate array length
validateArrayLength :: Text -> Int -> [a] -> Either ValidationError [a]
validateArrayLength field maxLen arr
  | length arr > maxLen = Left $ mkError field $
      "must have at most " <> T.pack (show maxLen) <> " elements"
  | otherwise = Right arr

-- | Validate non-empty array
validateNonEmptyArray :: Text -> [a] -> Either ValidationError [a]
validateNonEmptyArray field arr
  | null arr = Left $ mkError field "must not be empty"
  | otherwise = Right arr

-- ────────────────────────────────────────────────────────────────────────────
-- Date/Time Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate ISO 8601 datetime format (simplified)
validateDateTime :: Text -> Text -> Either ValidationError Text
validateDateTime field value
  | T.length value < 19 = Left $ mkError field "must be valid ISO 8601 datetime"
  | hasValidStructure = Right value
  | otherwise = Left $ mkError field "must be valid ISO 8601 datetime"
  where
    dateTimePart = T.take 19 value
    hasValidStructure =
      T.index dateTimePart 4 == '-' &&
      T.index dateTimePart 7 == '-' &&
      T.index dateTimePart 10 == 'T' &&
      T.index dateTimePart 13 == ':' &&
      T.index dateTimePart 16 == ':'

-- | Validate date format YYYY-MM-DD
validateDate :: Text -> Text -> Either ValidationError Text
validateDate field value
  | T.length value /= 10 = Left $ mkError field "must be YYYY-MM-DD format"
  | T.index value 4 == '-' && T.index value 7 == '-' = Right value
  | otherwise = Left $ mkError field "must be YYYY-MM-DD format"
