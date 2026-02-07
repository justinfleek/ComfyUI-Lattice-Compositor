{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Utils.ErrorHelpers
Description : Error helper utilities
Copyright   : (c) Lattice, 2026
License     : MIT

Standardized error message formatting across the codebase.
Provides consistent error context and helpful debugging information.

Source: leancomfy/lean/Lattice/Utils/ErrorHelpers.lean
-}

module Lattice.Utils.ErrorHelpers
  ( -- * Error Types
    ContextualError(..)
  , ValidationError(..)
    -- * Error Construction
  , mkContextualError
  , mkValidationError
    -- * Common Error Patterns
  , missingFieldError
  , invalidTypeError
  , outOfRangeError
  , emptyCollectionError
    -- * Formatting
  , formatContextualError
  , formatValidationError
  ) where

import Data.Text (Text)
import qualified Data.Text as T

--------------------------------------------------------------------------------
-- Error Types
--------------------------------------------------------------------------------

-- | Structured error with context
data ContextualError = ContextualError
  { ceContext :: !Text    -- Module/component context
  , ceAction  :: !Text    -- What action was being performed
  , ceReason  :: !Text    -- Why it failed
  , ceFix     :: !(Maybe Text) -- Optional suggestion
  } deriving (Eq, Show)

-- | Validation error with field details
data ValidationError = ValidationError
  { veField       :: !Text  -- Field name that failed
  , veActualType  :: !Text  -- Actual type received
  , veActualValue :: !Text  -- Actual value (stringified)
  , veExpected    :: !Text  -- What was expected
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Error Construction
--------------------------------------------------------------------------------

-- | Create a contextual error
mkContextualError :: Text -> Text -> Text -> Maybe Text -> ContextualError
mkContextualError = ContextualError

-- | Create a validation error
mkValidationError :: Text -> Text -> Text -> Text -> ValidationError
mkValidationError = ValidationError

--------------------------------------------------------------------------------
-- Formatting
--------------------------------------------------------------------------------

-- | Format contextual error as string
formatContextualError :: ContextualError -> Text
formatContextualError e =
  let base = "[" <> ceContext e <> "] " <> ceAction e <> " failed: " <> ceReason e <> "."
  in case ceFix e of
       Nothing -> base
       Just f -> base <> " " <> f

-- | Format validation error as string
formatValidationError :: ValidationError -> Text
formatValidationError e =
  let contextual = mkContextualError
        "Validation"
        ("Field \"" <> veField e <> "\" validation")
        ("got " <> veActualType e <> " (" <> veActualValue e <> "), expected " <> veExpected e)
        (Just $ "Provide a valid " <> veExpected e <> " value for " <> veField e)
  in formatContextualError contextual

--------------------------------------------------------------------------------
-- Common Error Patterns
--------------------------------------------------------------------------------

-- | Create error for missing required field
missingFieldError :: Text -> ContextualError
missingFieldError field = mkContextualError
  "Validation"
  ("Field \"" <> field <> "\" check")
  "value is missing or undefined"
  (Just $ "Provide a value for required field " <> field)

-- | Create error for invalid type
invalidTypeError :: Text -> Text -> Text -> ContextualError
invalidTypeError field expected actual = mkContextualError
  "Validation"
  ("Field \"" <> field <> "\" type check")
  ("expected " <> expected <> ", got " <> actual)
  (Just $ "Provide a " <> expected <> " value for " <> field)

-- | Create error for out of range value
outOfRangeError :: Text -> Double -> Double -> Double -> ContextualError
outOfRangeError field value minVal maxVal = mkContextualError
  "Validation"
  ("Field \"" <> field <> "\" range check")
  ("value " <> T.pack (show value) <> " is outside allowed range [" <> T.pack (show minVal) <> ", " <> T.pack (show maxVal) <> "]")
  (Just $ "Provide a value between " <> T.pack (show minVal) <> " and " <> T.pack (show maxVal) <> " for " <> field)

-- | Create error for empty collection
emptyCollectionError :: Text -> ContextualError
emptyCollectionError field = mkContextualError
  "Validation"
  ("Field \"" <> field <> "\" check")
  "collection is empty but at least one item is required"
  (Just $ "Provide at least one item for " <> field)
