-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // datepicker // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DatePicker Types — Core types for date picker components.
-- |
-- | This module contains type definitions shared across the DatePicker
-- | component family. Pure data types with no rendering logic.

module Hydrogen.Element.Compound.DatePicker.Types
  ( -- * Date Format
    DateFormat(ISO, USShort, USLong, EUShort, EULong, Custom)
  
  -- * Validation
  , ValidationError(InvalidFormat, DateOutOfRange, DateDisabled, EmptyValue)
  , validationErrorMessage
  ) where

import Prelude
  ( class Eq
  , class Show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // date format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Date format patterns for display and parsing.
-- |
-- | These determine how dates are shown in the input field and how
-- | user input is interpreted.
data DateFormat
  = ISO           -- ^ YYYY-MM-DD (ISO 8601)
  | USShort       -- ^ MM/DD/YYYY (US standard)
  | USLong        -- ^ MMMM D, YYYY (e.g., "January 15, 2024")
  | EUShort       -- ^ DD/MM/YYYY (European standard)
  | EULong        -- ^ D MMMM YYYY (e.g., "15 January 2024")
  | Custom String -- ^ Custom format string

derive instance eqDateFormat :: Eq DateFormat

instance showDateFormat :: Show DateFormat where
  show ISO = "ISO"
  show USShort = "USShort"
  show USLong = "USLong"
  show EUShort = "EUShort"
  show EULong = "EULong"
  show (Custom s) = "Custom(" <> s <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // validation error
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validation errors for date input.
-- |
-- | These represent all possible failure modes when parsing or validating
-- | user-entered dates.
data ValidationError
  = InvalidFormat    -- ^ Input string does not match expected format
  | DateOutOfRange   -- ^ Date is outside minDate/maxDate bounds
  | DateDisabled     -- ^ Date matches a disabled predicate
  | EmptyValue       -- ^ Required field is empty

derive instance eqValidationError :: Eq ValidationError

instance showValidationError :: Show ValidationError where
  show InvalidFormat = "InvalidFormat"
  show DateOutOfRange = "DateOutOfRange"
  show DateDisabled = "DateDisabled"
  show EmptyValue = "EmptyValue"

-- | Get user-facing error message for validation error.
-- |
-- | Pure PureScript lookup table. No JavaScript Intl API.
validationErrorMessage :: ValidationError -> String
validationErrorMessage InvalidFormat = "Invalid date format"
validationErrorMessage DateOutOfRange = "Date is out of allowed range"
validationErrorMessage DateDisabled = "This date is not available"
validationErrorMessage EmptyValue = "Please enter a date"
