-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // temporal // dayofweek
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DayOfWeek — The seven days of the week.
-- |
-- | An enumeration of the seven days, with:
-- | - Full names (Monday, Tuesday, ...)
-- | - Abbreviated names (Mon, Tue, ...)
-- | - Single letter abbreviations (M, T, W, ...)
-- | - ISO 8601 numbering (Monday = 1, Sunday = 7)
-- | - US numbering (Sunday = 0, Saturday = 6)
-- |
-- | ## Design Philosophy
-- |
-- | Days of the week are a bounded enumeration. There are exactly seven,
-- | no more, no less. The type makes this explicit — you cannot construct
-- | an eighth day.

module Hydrogen.Schema.Temporal.DayOfWeek
  ( DayOfWeek
      ( Monday
      , Tuesday
      , Wednesday
      , Thursday
      , Friday
      , Saturday
      , Sunday
      )
  -- * Constructors
  , fromISO
  , fromUS
  -- * Accessors
  , toISO
  , toUS
  -- * Names
  , name
  , nameShort
  , nameLetter
  , nameNarrow
  -- * Predicates
  , isWeekday
  , isWeekend
  -- * Navigation
  , next
  , prev
  , addDays
  -- * Enumeration
  , allDays
  , weekdays
  , weekend
  , allDaysFromMonday
  , allDaysFromSunday
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , mod
  , (+)
  , (-)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // dayofweek
-- ═════════════════════════════════════════════════════════════════════════════

-- | The seven days of the week.
-- |
-- | Ordered Monday through Sunday (ISO 8601 convention).
data DayOfWeek
  = Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday

derive instance eqDayOfWeek :: Eq DayOfWeek
derive instance ordDayOfWeek :: Ord DayOfWeek

instance showDayOfWeek :: Show DayOfWeek where
  show = name

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create from ISO 8601 day number (1 = Monday, 7 = Sunday)
fromISO :: Int -> Maybe DayOfWeek
fromISO 1 = Just Monday
fromISO 2 = Just Tuesday
fromISO 3 = Just Wednesday
fromISO 4 = Just Thursday
fromISO 5 = Just Friday
fromISO 6 = Just Saturday
fromISO 7 = Just Sunday
fromISO _ = Nothing

-- | Create from US day number (0 = Sunday, 6 = Saturday)
fromUS :: Int -> Maybe DayOfWeek
fromUS 0 = Just Sunday
fromUS 1 = Just Monday
fromUS 2 = Just Tuesday
fromUS 3 = Just Wednesday
fromUS 4 = Just Thursday
fromUS 5 = Just Friday
fromUS 6 = Just Saturday
fromUS _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to ISO 8601 day number (1 = Monday, 7 = Sunday)
toISO :: DayOfWeek -> Int
toISO Monday    = 1
toISO Tuesday   = 2
toISO Wednesday = 3
toISO Thursday  = 4
toISO Friday    = 5
toISO Saturday  = 6
toISO Sunday    = 7

-- | Convert to US day number (0 = Sunday, 6 = Saturday)
toUS :: DayOfWeek -> Int
toUS Sunday    = 0
toUS Monday    = 1
toUS Tuesday   = 2
toUS Wednesday = 3
toUS Thursday  = 4
toUS Friday    = 5
toUS Saturday  = 6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Full name of the day
name :: DayOfWeek -> String
name Monday    = "Monday"
name Tuesday   = "Tuesday"
name Wednesday = "Wednesday"
name Thursday  = "Thursday"
name Friday    = "Friday"
name Saturday  = "Saturday"
name Sunday    = "Sunday"

-- | Three-letter abbreviation
nameShort :: DayOfWeek -> String
nameShort Monday    = "Mon"
nameShort Tuesday   = "Tue"
nameShort Wednesday = "Wed"
nameShort Thursday  = "Thu"
nameShort Friday    = "Fri"
nameShort Saturday  = "Sat"
nameShort Sunday    = "Sun"

-- | Single letter abbreviation (M, T, W, T, F, S, S)
-- |
-- | Note: Tuesday and Thursday both map to "T",
-- | Saturday and Sunday both map to "S".
-- | Use `nameNarrow` for unique two-letter codes.
nameLetter :: DayOfWeek -> String
nameLetter Monday    = "M"
nameLetter Tuesday   = "T"
nameLetter Wednesday = "W"
nameLetter Thursday  = "T"
nameLetter Friday    = "F"
nameLetter Saturday  = "S"
nameLetter Sunday    = "S"

-- | Two-letter unique abbreviation
nameNarrow :: DayOfWeek -> String
nameNarrow Monday    = "Mo"
nameNarrow Tuesday   = "Tu"
nameNarrow Wednesday = "We"
nameNarrow Thursday  = "Th"
nameNarrow Friday    = "Fr"
nameNarrow Saturday  = "Sa"
nameNarrow Sunday    = "Su"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this a weekday (Monday through Friday)?
isWeekday :: DayOfWeek -> Boolean
isWeekday Saturday = false
isWeekday Sunday   = false
isWeekday _        = true

-- | Is this a weekend day (Saturday or Sunday)?
isWeekend :: DayOfWeek -> Boolean
isWeekend Saturday = true
isWeekend Sunday   = true
isWeekend _        = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // navigation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Next day of the week (wraps Sunday -> Monday)
next :: DayOfWeek -> DayOfWeek
next Monday    = Tuesday
next Tuesday   = Wednesday
next Wednesday = Thursday
next Thursday  = Friday
next Friday    = Saturday
next Saturday  = Sunday
next Sunday    = Monday

-- | Previous day of the week (wraps Monday -> Sunday)
prev :: DayOfWeek -> DayOfWeek
prev Monday    = Sunday
prev Tuesday   = Monday
prev Wednesday = Tuesday
prev Thursday  = Wednesday
prev Friday    = Thursday
prev Saturday  = Friday
prev Sunday    = Saturday

-- | Add days to a day of week (can be negative, wraps)
addDays :: Int -> DayOfWeek -> DayOfWeek
addDays n day =
  let
    isoDay = toISO day
    -- Normalize to 0-6 range, then add, then mod 7, then back to 1-7
    zeroBased = isoDay - 1
    added = zeroBased + n
    normalized = ((added `mod` 7) + 7) `mod` 7  -- Handle negative mod
    newIso = normalized + 1
  in
    unsafeFromISO newIso

-- | Unsafe conversion (only for internal use where we know 1-7)
unsafeFromISO :: Int -> DayOfWeek
unsafeFromISO 1 = Monday
unsafeFromISO 2 = Tuesday
unsafeFromISO 3 = Wednesday
unsafeFromISO 4 = Thursday
unsafeFromISO 5 = Friday
unsafeFromISO 6 = Saturday
unsafeFromISO _ = Sunday  -- 7 or any other (shouldn't happen)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // enumeration
-- ═════════════════════════════════════════════════════════════════════════════

-- | All days of the week (Monday first, ISO 8601 order)
allDays :: Array DayOfWeek
allDays = [ Monday, Tuesday, Wednesday, Thursday, Friday, Saturday, Sunday ]

-- | All days starting from Monday (alias for allDays)
allDaysFromMonday :: Array DayOfWeek
allDaysFromMonday = allDays

-- | All days starting from Sunday (US convention)
allDaysFromSunday :: Array DayOfWeek
allDaysFromSunday = [ Sunday, Monday, Tuesday, Wednesday, Thursday, Friday, Saturday ]

-- | Weekdays only (Monday through Friday)
weekdays :: Array DayOfWeek
weekdays = [ Monday, Tuesday, Wednesday, Thursday, Friday ]

-- | Weekend days only (Saturday and Sunday)
weekend :: Array DayOfWeek
weekend = [ Saturday, Sunday ]
