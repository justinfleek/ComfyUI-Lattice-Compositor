-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // daterangepicker // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DateRangePicker Types — Core types for date range picker components.
-- |
-- | This module contains type definitions shared across the DateRangePicker
-- | component family. Pure data types with no rendering logic.

module Hydrogen.Element.Compound.DateRangePicker.Types
  ( -- * Re-export from Calendar
    module ReExports
  
  -- * Date Range Operations
  , mkDateRange
  , rangeStart
  , rangeEnd
  , rangeDays
  , isValidRange
  
  -- * Comparison Mode
  , ComparisonMode(PreviousPeriod, PreviousYear, Custom)
  , comparisonModeLabel
  
  -- * Preset Range
  , PresetConfig
  , PresetId
  
  -- * Selection State
  , SelectionState(SelectingStart, SelectingEnd, Complete)
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (+)
  , (-)
  , (*)
  , (>)
  , not
  )

import Hydrogen.Element.Compound.Calendar 
  ( CalendarDate
  , DateRange
  , compareDates
  ) as ReExports

import Hydrogen.Element.Compound.Calendar (CalendarDate, DateRange, compareDates)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // date range operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a DateRange, swapping dates if start > end
mkDateRange :: CalendarDate -> CalendarDate -> DateRange
mkDateRange d1 d2 =
  -- compareDates returns Int: positive if d1 > d2, negative if d1 < d2, 0 if equal
  if compareDates d1 d2 > 0
    then { start: d2, end: d1 }  -- d1 > d2, so swap
    else { start: d1, end: d2 }

-- | Get range start date
rangeStart :: DateRange -> CalendarDate
rangeStart r = r.start

-- | Get range end date
rangeEnd :: DateRange -> CalendarDate
rangeEnd r = r.end

-- | Calculate approximate number of days in range
-- |
-- | Note: This is an approximation. For exact calculation,
-- | use the Calendar module's date arithmetic.
rangeDays :: DateRange -> Int
rangeDays r =
  let
    -- Simplified day count (doesn't account for varying month lengths)
    startDays = r.start.year * 365 + r.start.month * 30 + r.start.day
    endDays = r.end.year * 365 + r.end.month * 30 + r.end.day
  in
    endDays - startDays + 1

-- | Check if range is valid (start <= end)
isValidRange :: DateRange -> Boolean
isValidRange r = 
  -- compareDates returns positive if first > second
  -- Valid range: start <= end means compareDates returns 0 or negative
  not (compareDates r.start r.end > 0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // comparison mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Comparison mode for analytics use cases.
-- |
-- | Allows comparing the selected range to a previous time period.
data ComparisonMode
  = PreviousPeriod   -- ^ Same duration, immediately before selected range
  | PreviousYear     -- ^ Same dates in the previous year
  | Custom           -- ^ User-defined custom comparison range

derive instance eqComparisonMode :: Eq ComparisonMode
derive instance ordComparisonMode :: Ord ComparisonMode

instance showComparisonMode :: Show ComparisonMode where
  show PreviousPeriod = "PreviousPeriod"
  show PreviousYear = "PreviousYear"
  show Custom = "Custom"

-- | Get human-readable label for comparison mode
comparisonModeLabel :: ComparisonMode -> String
comparisonModeLabel PreviousPeriod = "Previous period"
comparisonModeLabel PreviousYear = "Previous year"
comparisonModeLabel Custom = "Custom"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // preset range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identifier for a preset (for event handling)
type PresetId = String

-- | Configuration for a preset range.
-- |
-- | Note: Unlike the Halogen version which uses Effect for `getRange`,
-- | this is a pure function that takes "today" as a parameter.
-- | This keeps presets deterministic and testable.
type PresetConfig =
  { id :: PresetId
  , label :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // selection state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of range selection interaction.
-- |
-- | Tracks whether user is selecting start date, end date, or has completed.
data SelectionState
  = SelectingStart  -- ^ Waiting for start date selection
  | SelectingEnd    -- ^ Start selected, waiting for end date
  | Complete        -- ^ Both dates selected

derive instance eqSelectionState :: Eq SelectionState
derive instance ordSelectionState :: Ord SelectionState

instance showSelectionState :: Show SelectionState where
  show SelectingStart = "SelectingStart"
  show SelectingEnd = "SelectingEnd"
  show Complete = "Complete"
