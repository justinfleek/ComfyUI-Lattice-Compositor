-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // daterangepicker // presets
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DateRangePicker Presets — Pure preset range generators.
-- |
-- | Unlike the Halogen version which uses Effect for "today", these are
-- | pure functions that take a reference date as a parameter. This makes
-- | them deterministic, testable, and suitable for SSR.
-- |
-- | ## Design Philosophy
-- |
-- | The caller provides "today" — this could come from:
-- | - The runtime (via Effect at the boundary)
-- | - A fixed date for testing
-- | - Server-side rendering context
-- |
-- | The preset functions are then pure transformations.

module Hydrogen.Element.Compound.DateRangePicker.Presets
  ( -- * Preset Definitions
    PresetDef
  , presetId
  , presetLabel
  , presetRange
  
  -- * Standard Presets
  , todayPreset
  , yesterdayPreset
  , last7DaysPreset
  , last30DaysPreset
  , thisWeekPreset
  , lastWeekPreset
  , thisMonthPreset
  , lastMonthPreset
  , thisYearPreset
  
  -- * Preset Collections
  , defaultPresets
  , analyticsPresets
  
  -- * Range Generators (Pure)
  , todayRange
  , yesterdayRange
  , last7DaysRange
  , last30DaysRange
  , thisWeekRange
  , lastWeekRange
  , thisMonthRange
  , lastMonthRange
  , thisYearRange
  ) where

import Prelude
  ( negate
  , (-)
  , (==)
  )

import Hydrogen.Element.Compound.Calendar 
  ( CalendarDate
  , DateRange
  , WeekStart(Sunday, Monday)
  , addDays
  , addMonths
  , getDaysInMonth
  , dayOfWeek
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // preset definition
-- ═════════════════════════════════════════════════════════════════════════════

-- | A preset definition with id, label, and range generator.
-- |
-- | The range generator is a pure function from "today" to a DateRange.
type PresetDef =
  { id :: String
  , label :: String
  , getRange :: CalendarDate -> DateRange
  }

-- | Get preset id
presetId :: PresetDef -> String
presetId p = p.id

-- | Get preset label
presetLabel :: PresetDef -> String
presetLabel p = p.label

-- | Get range for a preset given today's date
presetRange :: PresetDef -> CalendarDate -> DateRange
presetRange p today = p.getRange today

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // standard presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Today preset
todayPreset :: PresetDef
todayPreset =
  { id: "today"
  , label: "Today"
  , getRange: todayRange
  }

-- | Yesterday preset
yesterdayPreset :: PresetDef
yesterdayPreset =
  { id: "yesterday"
  , label: "Yesterday"
  , getRange: yesterdayRange
  }

-- | Last 7 days preset
last7DaysPreset :: PresetDef
last7DaysPreset =
  { id: "last7days"
  , label: "Last 7 days"
  , getRange: last7DaysRange
  }

-- | Last 30 days preset
last30DaysPreset :: PresetDef
last30DaysPreset =
  { id: "last30days"
  , label: "Last 30 days"
  , getRange: last30DaysRange
  }

-- | This week preset (Sunday start)
thisWeekPreset :: PresetDef
thisWeekPreset =
  { id: "thisweek"
  , label: "This week"
  , getRange: thisWeekRange Sunday
  }

-- | Last week preset (Sunday start)
lastWeekPreset :: PresetDef
lastWeekPreset =
  { id: "lastweek"
  , label: "Last week"
  , getRange: lastWeekRange Sunday
  }

-- | This month preset
thisMonthPreset :: PresetDef
thisMonthPreset =
  { id: "thismonth"
  , label: "This month"
  , getRange: thisMonthRange
  }

-- | Last month preset
lastMonthPreset :: PresetDef
lastMonthPreset =
  { id: "lastmonth"
  , label: "Last month"
  , getRange: lastMonthRange
  }

-- | This year preset
thisYearPreset :: PresetDef
thisYearPreset =
  { id: "thisyear"
  , label: "This year"
  , getRange: thisYearRange
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // preset collections
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default presets for general use
defaultPresets :: Array PresetDef
defaultPresets =
  [ todayPreset
  , yesterdayPreset
  , last7DaysPreset
  , last30DaysPreset
  , thisMonthPreset
  , lastMonthPreset
  ]

-- | Extended presets for analytics dashboards
analyticsPresets :: Array PresetDef
analyticsPresets =
  [ todayPreset
  , yesterdayPreset
  , last7DaysPreset
  , last30DaysPreset
  , thisWeekPreset
  , lastWeekPreset
  , thisMonthPreset
  , lastMonthPreset
  , thisYearPreset
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // range generators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Today as a single-day range
todayRange :: CalendarDate -> DateRange
todayRange today = { start: today, end: today }

-- | Yesterday as a single-day range
yesterdayRange :: CalendarDate -> DateRange
yesterdayRange today =
  let yesterday = addDays today (-1)
  in { start: yesterday, end: yesterday }

-- | Last 7 days (including today)
last7DaysRange :: CalendarDate -> DateRange
last7DaysRange today =
  let start = addDays today (-6)
  in { start: start, end: today }

-- | Last 30 days (including today)
last30DaysRange :: CalendarDate -> DateRange
last30DaysRange today =
  let start = addDays today (-29)
  in { start: start, end: today }

-- | This week (from week start to today)
thisWeekRange :: WeekStart -> CalendarDate -> DateRange
thisWeekRange weekStart today =
  let
    todayDow = dayOfWeek today
    -- Calculate days to go back to reach week start
    daysBack = case weekStart of
      Sunday -> todayDow
      Monday -> if todayDow == 0 then 6 else todayDow - 1
    start = addDays today (-daysBack)
  in
    { start: start, end: today }

-- | Last week (full 7-day week before current week)
lastWeekRange :: WeekStart -> CalendarDate -> DateRange
lastWeekRange weekStart today =
  let
    todayDow = dayOfWeek today
    daysBack = case weekStart of
      Sunday -> todayDow
      Monday -> if todayDow == 0 then 6 else todayDow - 1
    -- Go to start of this week, then back 7 days
    thisWeekStart = addDays today (-daysBack)
    lastWeekStart = addDays thisWeekStart (-7)
    lastWeekEnd = addDays thisWeekStart (-1)
  in
    { start: lastWeekStart, end: lastWeekEnd }

-- | This month (1st to today)
thisMonthRange :: CalendarDate -> DateRange
thisMonthRange today =
  let start = { year: today.year, month: today.month, day: 1 }
  in { start: start, end: today }

-- | Last month (full month before current month)
lastMonthRange :: CalendarDate -> DateRange
lastMonthRange today =
  let
    lastMonth = addMonths today (-1)
    start = { year: lastMonth.year, month: lastMonth.month, day: 1 }
    lastDay = getDaysInMonth lastMonth.year lastMonth.month
    end = { year: lastMonth.year, month: lastMonth.month, day: lastDay }
  in
    { start: start, end: end }

-- | This year (Jan 1 to today)
thisYearRange :: CalendarDate -> DateRange
thisYearRange today =
  let start = { year: today.year, month: 1, day: 1 }
  in { start: start, end: today }
