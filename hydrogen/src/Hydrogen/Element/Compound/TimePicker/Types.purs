-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // timepicker // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TimePicker Types — Core types for time picker components.
-- |
-- | This module contains type definitions shared across the TimePicker
-- | component family. Pure data types with no rendering logic.

module Hydrogen.Element.Compound.TimePicker.Types
  ( -- * Hour Format
    HourFormat(Hour12, Hour24)
  , is12Hour
  , is24Hour
  
  -- * Period (AM/PM)
  , Period(AM, PM)
  , togglePeriod
  , periodToString
  
  -- * Validation
  , ValidationError(InvalidFormat, TimeOutOfRange, EmptyValue)
  , validationErrorMessage
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (==)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hour format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hour display format.
-- |
-- | Determines whether times are displayed in 12-hour (with AM/PM) or
-- | 24-hour format.
data HourFormat
  = Hour12  -- ^ 12-hour format with AM/PM indicator
  | Hour24  -- ^ 24-hour format (military time)

derive instance eqHourFormat :: Eq HourFormat
derive instance ordHourFormat :: Ord HourFormat

instance showHourFormat :: Show HourFormat where
  show Hour12 = "Hour12"
  show Hour24 = "Hour24"

-- | Check if format is 12-hour
is12Hour :: HourFormat -> Boolean
is12Hour Hour12 = true
is12Hour Hour24 = false

-- | Check if format is 24-hour
is24Hour :: HourFormat -> Boolean
is24Hour Hour24 = true
is24Hour Hour12 = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // period
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time period for 12-hour format.
-- |
-- | AM = ante meridiem (before noon, 00:00-11:59)
-- | PM = post meridiem (after noon, 12:00-23:59)
data Period
  = AM
  | PM

derive instance eqPeriod :: Eq Period
derive instance ordPeriod :: Ord Period

instance showPeriod :: Show Period where
  show AM = "AM"
  show PM = "PM"

-- | Toggle between AM and PM
togglePeriod :: Period -> Period
togglePeriod AM = PM
togglePeriod PM = AM

-- | Convert period to display string
-- |
-- | Pure lookup. No JavaScript Intl API.
periodToString :: Period -> String
periodToString AM = "AM"
periodToString PM = "PM"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // validation error
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validation errors for time input.
-- |
-- | These represent all possible failure modes when parsing or validating
-- | user-entered times.
data ValidationError
  = InvalidFormat    -- ^ Input string does not match expected format
  | TimeOutOfRange   -- ^ Time is outside minTime/maxTime bounds
  | EmptyValue       -- ^ Required field is empty

derive instance eqValidationError :: Eq ValidationError

instance showValidationError :: Show ValidationError where
  show InvalidFormat = "InvalidFormat"
  show TimeOutOfRange = "TimeOutOfRange"
  show EmptyValue = "EmptyValue"

-- | Get user-facing error message for validation error.
-- |
-- | Pure PureScript lookup table. No JavaScript Intl API.
validationErrorMessage :: ValidationError -> String
validationErrorMessage InvalidFormat = "Invalid time format"
validationErrorMessage TimeOutOfRange = "Time is out of allowed range"
validationErrorMessage EmptyValue = "Please enter a time"
