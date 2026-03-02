-- |
-- Module      : Lattice.Services.JSONValidation
-- Description : Pure JSON validation and sanitization functions
-- 
-- Migrated from ui/src/services/jsonValidation.ts
-- Pure type guards, sanitization, and validation functions
-- Note: JSON parse/stringify deferred (use Aeson)
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.JSONValidation
  ( -- Type guards
    isObject
  , isString
  , isNumber
  , isArray
  , isBoolean
  -- Sanitization
  , sanitizeString
  , sanitizeFileName
  -- Validation
  , validateLatticeTemplate
  , validateTemplateConfig
  -- Types
  , ValidationError(..)
  , ValidationResult(..)
  , JSONObject
  ) where

import Data.Aeson (Value(..))
import qualified Data.Aeson.KeyMap as KeyMap
import Lattice.Utils.NumericSafety (isFinite)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector as V

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Validation error with path and message
data ValidationError = ValidationError
  { validationErrorPath :: Text
  , validationErrorMessage :: Text
  , validationErrorExpected :: Maybe Text
  , validationErrorReceived :: Maybe Text
  }
  deriving (Eq, Show)

-- | Validation result with errors and warnings
data ValidationResult = ValidationResult
  { validationResultValid :: Bool
  , validationResultErrors :: [ValidationError]
  , validationResultWarnings :: [Text]
  }
  deriving (Eq, Show)

-- | JSON object type (HashMap String Value)
type JSONObject = KeyMap.KeyMap Value

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // type // guards
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if value is a non-null object (not array)
isObject :: Value -> Bool
isObject (Object _) = True
isObject _ = False

-- | Check if value is a valid string
isString :: Value -> Bool
isString (String _) = True
isString _ = False

-- | Check if value is a valid number (finite)
isNumber :: Value -> Bool
isNumber (Number n) = isFinite (realToFrac n :: Double)
isNumber _ = False

-- | Check if value is a valid array
isArray :: Value -> Bool
isArray (Array _) = True
isArray _ = False

-- | Check if value is a valid boolean
isBoolean :: Value -> Bool
isBoolean (Bool _) = True
isBoolean _ = False

-- ════════════════════════════════════════════════════════════════════════════
--                                                 // sanitization // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Sanitize a string to prevent XSS
sanitizeString :: Text -> Text
sanitizeString str =
  T.replace "&" "&amp;" $
  T.replace "<" "&lt;" $
  T.replace ">" "&gt;" $
  T.replace "\"" "&quot;" $
  T.replace "'" "&#x27;" str

-- | Sanitize file name for safe storage
sanitizeFileName :: Text -> Text
sanitizeFileName name =
  let -- Replace invalid characters with underscore
      step1 = T.replace "<" "_" $
              T.replace ">" "_" $
              T.replace ":" "_" $
              T.replace "\"" "_" $
              T.replace "/" "_" $
              T.replace "\\" "_" $
              T.replace "|" "_" $
              T.replace "?" "_" $
              T.replace "*" "_" name
      -- Replace whitespace with underscore
      step2 = T.replace " " "_" $
              T.replace "\t" "_" $
              T.replace "\n" "_" $
              T.replace "\r" "_" step1
      -- Replace multiple underscores with single (iterative)
      collapseUnderscores str =
        let collapsed = T.replace "__" "_" str
        in if collapsed == str
           then str
           else collapseUnderscores collapsed
      step3 = collapseUnderscores step2
      -- Limit length to 200 characters
      result = T.take 200 step3
  in result

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // validation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Validate Lattice Template structure
validateLatticeTemplate :: Value -> ValidationResult
validateLatticeTemplate value =
  let errors = []
      warnings = []
  in case value of
    Object obj ->
      let -- Check required fields
          formatVersion = KeyMap.lookup "formatVersion" obj
          name = KeyMap.lookup "name" obj
          version = KeyMap.lookup "version" obj
          
          -- Validate formatVersion
          formatVersionErrors = case formatVersion of
            Just (String _) -> []
            Just _ -> [ValidationError "$.formatVersion" "formatVersion must be a string" (Just "string") Nothing]
            Nothing -> [ValidationError "$.formatVersion" "formatVersion is required" (Just "string") Nothing]
          
          -- Validate name
          nameErrors = case name of
            Just (String _) -> []
            Just _ -> [ValidationError "$.name" "name must be a string" (Just "string") Nothing]
            Nothing -> [ValidationError "$.name" "name is required" (Just "string") Nothing]
          
          -- Validate version
          versionErrors = case version of
            Just (String _) -> []
            Just _ -> [ValidationError "$.version" "version must be a string" (Just "string") Nothing]
            Nothing -> []
          
          allErrors = formatVersionErrors ++ nameErrors ++ versionErrors
          isValid = null allErrors
      in ValidationResult isValid allErrors warnings
    _ ->
      ValidationResult False [ValidationError "$" "LatticeTemplate must be an object" (Just "object") Nothing] warnings

-- | Validate template configuration
validateTemplateConfig :: Value -> ValidationResult
validateTemplateConfig value =
  let errors = []
      warnings = []
  in case value of
    Object obj ->
      let -- Check required fields
          templateName = KeyMap.lookup "templateName" obj
          
          -- Validate templateName
          templateNameErrors = case templateName of
            Just (String _) -> []
            Just _ -> [ValidationError "$.templateName" "templateName must be a string" (Just "string") Nothing]
            Nothing -> [ValidationError "$.templateName" "templateName is required" (Just "string") Nothing]
          
          allErrors = templateNameErrors
          isValid = null allErrors
      in ValidationResult isValid allErrors warnings
    _ ->
      ValidationResult False [ValidationError "$" "TemplateConfig must be an object" (Just "object") Nothing] warnings
