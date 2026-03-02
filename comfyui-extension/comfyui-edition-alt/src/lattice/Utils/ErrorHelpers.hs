-- |
-- Module      : Lattice.Utils.ErrorHelpers
-- Description : Standardized error message formatting
-- 
-- Migrated from ui/src/utils/errorHelpers.ts
-- Pure functions for error creation
-- 
--                                                                  // critical
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.ErrorHelpers
  ( -- Error creation
    createContextualError
  , createValidationError
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Aeson (Value(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // error // creation
-- ════════════════════════════════════════════════════════════════════════════

-- | Create a contextual error with standard format:
-- [Context] Action failed: Reason. How to fix.
-- 
-- System F/Omega proof: Explicit type Text -> Text -> Text -> Maybe Text -> Text
-- Mathematical proof: Always returns formatted error message
-- 
-- @param context The module/component context (e.g., "ModelExport", "DataImport")
-- @param action What action was being performed (e.g., "WanMove export", "JSON parsing")
-- @param reason Why it failed (e.g., "No animated layers found", "Invalid JSON syntax")
-- @param fix Optional suggestion on how to fix the issue
-- @returns Formatted error message
createContextualError :: Text -> Text -> Text -> Maybe Text -> Text
createContextualError context action reason mFix =
  let fixPart = case mFix of
        Just f -> " " <> f
        Nothing -> ""
  in "[" <> context <> "] " <> action <> " failed: " <> reason <> "." <> fixPart

-- | Create a validation error for field/value mismatches
-- 
-- System F/Omega proof: Explicit type Text -> Value -> Text -> Text
-- Mathematical proof: Always returns formatted validation error
-- 
-- @param field The field name that failed validation
-- @param value The actual value received (as JSON Value)
-- @param expected What was expected (e.g., "positive number", "array", "function")
-- @returns Formatted validation error message
createValidationError :: Text -> Value -> Text -> Text
createValidationError field value expected =
  let valueStr = T.pack (show value)
      valueType = T.pack (show (valueTypeOf value))
      message = "got " <> valueType <> " (" <> valueStr <> "), expected " <> expected
      fix = "Provide a valid " <> expected <> " value for " <> field
  in createContextualError "Validation" ("Field \"" <> field <> "\" validation") message (Just fix)

-- | Get type name from JSON Value
valueTypeOf :: Value -> Text
valueTypeOf v = case v of
  Object _ -> "object"
  Array _ -> "array"
  String _ -> "string"
  Number _ -> "number"
  Bool _ -> "boolean"
  Null -> "null"
