-- | Lattice.Utils.ErrorHelpers - Error helper utilities
-- |
-- | Standardized error message formatting across the codebase.
-- | Provides consistent error context and helpful debugging information.
-- |
-- | Source: lattice-core/lean/Lattice/Utils/ErrorHelpers.lean

module Lattice.Utils.ErrorHelpers
  ( ContextualError
  , ValidationError
  , mkContextualError
  , mkValidationError
  , formatContextualError
  , formatValidationError
  , missingFieldError
  , invalidTypeError
  , outOfRangeError
  , emptyCollectionError
  ) where

import Prelude
import Data.Maybe (Maybe(..))

--------------------------------------------------------------------------------
-- Error Types
--------------------------------------------------------------------------------

-- | Structured error with context
type ContextualError =
  { context :: String    -- Module/component context
  , action  :: String    -- What action was being performed
  , reason  :: String    -- Why it failed
  , fix     :: Maybe String -- Optional suggestion
  }

-- | Validation error with field details
type ValidationError =
  { field       :: String  -- Field name that failed
  , actualType  :: String  -- Actual type received
  , actualValue :: String  -- Actual value (stringified)
  , expected    :: String  -- What was expected
  }

--------------------------------------------------------------------------------
-- Error Construction
--------------------------------------------------------------------------------

-- | Create a contextual error
mkContextualError :: String -> String -> String -> Maybe String -> ContextualError
mkContextualError context action reason fix =
  { context, action, reason, fix }

-- | Create a validation error
mkValidationError :: String -> String -> String -> String -> ValidationError
mkValidationError field actualType actualValue expected =
  { field, actualType, actualValue, expected }

--------------------------------------------------------------------------------
-- Formatting
--------------------------------------------------------------------------------

-- | Format contextual error as string
formatContextualError :: ContextualError -> String
formatContextualError e =
  let base = "[" <> e.context <> "] " <> e.action <> " failed: " <> e.reason <> "."
  in case e.fix of
       Nothing -> base
       Just f -> base <> " " <> f

-- | Format validation error as string
formatValidationError :: ValidationError -> String
formatValidationError e =
  let contextual = mkContextualError
        "Validation"
        ("Field \"" <> e.field <> "\" validation")
        ("got " <> e.actualType <> " (" <> e.actualValue <> "), expected " <> e.expected)
        (Just $ "Provide a valid " <> e.expected <> " value for " <> e.field)
  in formatContextualError contextual

--------------------------------------------------------------------------------
-- Common Error Patterns
--------------------------------------------------------------------------------

-- | Create error for missing required field
missingFieldError :: String -> ContextualError
missingFieldError field = mkContextualError
  "Validation"
  ("Field \"" <> field <> "\" check")
  "value is missing or undefined"
  (Just $ "Provide a value for required field " <> field)

-- | Create error for invalid type
invalidTypeError :: String -> String -> String -> ContextualError
invalidTypeError field expected actual = mkContextualError
  "Validation"
  ("Field \"" <> field <> "\" type check")
  ("expected " <> expected <> ", got " <> actual)
  (Just $ "Provide a " <> expected <> " value for " <> field)

-- | Create error for out of range value
outOfRangeError :: String -> Number -> Number -> Number -> ContextualError
outOfRangeError field value minVal maxVal = mkContextualError
  "Validation"
  ("Field \"" <> field <> "\" range check")
  ("value " <> show value <> " is outside allowed range [" <> show minVal <> ", " <> show maxVal <> "]")
  (Just $ "Provide a value between " <> show minVal <> " and " <> show maxVal <> " for " <> field)

-- | Create error for empty collection
emptyCollectionError :: String -> ContextualError
emptyCollectionError field = mkContextualError
  "Validation"
  ("Field \"" <> field <> "\" check")
  "collection is empty but at least one item is required"
  (Just $ "Provide at least one item for " <> field)
