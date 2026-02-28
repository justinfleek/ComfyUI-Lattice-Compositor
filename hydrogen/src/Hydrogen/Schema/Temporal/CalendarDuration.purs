-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // temporal // calendar-duration
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar-aware duration types.
-- |
-- | Unlike animation Duration (milliseconds/frames), CalendarDuration
-- | represents human calendar units: days, weeks, months, years.
-- |
-- | ## Why Separate From Animation Duration
-- | - "3 months" is not a fixed number of milliseconds
-- | - Month lengths vary (28-31 days)
-- | - Years vary (leap years)
-- | - Calendar arithmetic requires date context

module Hydrogen.Schema.Temporal.CalendarDuration
  ( -- * Calendar Duration
    CalendarDuration(..)
  , calendarDuration
  , durationYears
  , durationMonths
  , durationWeeks
  , durationDays
  
  -- * Constructors
  , days
  , weeks
  , months
  , years
  , yearsMonthsDays
  
  -- * Operations
  , addDurations
  , subtractDurations
  , negateDuration
  , isZeroDuration
  , isNonZeroDuration
  , isShorter
  , isLonger
  , normalizeDuration
  
  -- * Formatting
  , durationToISO8601
  , durationToHuman
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (&&)
  , (||)
  , (<)
  , (>)
  , (==)
  , (/=)
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , mod
  , max
  , negate
  )

import Data.Foldable (foldl)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // calendar duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | CalendarDuration - duration in calendar units.
-- | Stored as years, months, and days separately because they
-- | don't have fixed relationships.
data CalendarDuration = CalendarDuration
  { years :: Int
  , months :: Int
  , days :: Int
  }

derive instance eqCalendarDuration :: Eq CalendarDuration
derive instance ordCalendarDuration :: Ord CalendarDuration

instance showCalendarDuration :: Show CalendarDuration where
  show d = "(CalendarDuration " <> durationToHuman d <> ")"

-- | Construct a calendar duration.
calendarDuration :: Int -> Int -> Int -> CalendarDuration
calendarDuration y m d = CalendarDuration
  { years: max 0 y
  , months: max 0 m
  , days: max 0 d
  }

-- | Get years component.
durationYears :: CalendarDuration -> Int
durationYears (CalendarDuration d) = d.years

-- | Get months component.
durationMonths :: CalendarDuration -> Int
durationMonths (CalendarDuration d) = d.months

-- | Get days component.
durationDays :: CalendarDuration -> Int
durationDays (CalendarDuration d) = d.days

-- | Get weeks (days / 7).
durationWeeks :: CalendarDuration -> Int
durationWeeks (CalendarDuration d) = d.days / 7

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create duration from days.
days :: Int -> CalendarDuration
days n = CalendarDuration { years: 0, months: 0, days: max 0 n }

-- | Create duration from weeks.
weeks :: Int -> CalendarDuration
weeks n = CalendarDuration { years: 0, months: 0, days: max 0 n * 7 }

-- | Create duration from months.
months :: Int -> CalendarDuration
months n = CalendarDuration { years: 0, months: max 0 n, days: 0 }

-- | Create duration from years.
years :: Int -> CalendarDuration
years n = CalendarDuration { years: max 0 n, months: 0, days: 0 }

-- | Create duration from components.
yearsMonthsDays :: Int -> Int -> Int -> CalendarDuration
yearsMonthsDays = calendarDuration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two durations.
addDurations :: CalendarDuration -> CalendarDuration -> CalendarDuration
addDurations (CalendarDuration d1) (CalendarDuration d2) =
  CalendarDuration
    { years: d1.years + d2.years
    , months: d1.months + d2.months
    , days: d1.days + d2.days
    }

-- | Subtract second duration from first.
-- | Components can go negative; use normalizeDuration afterward if needed.
subtractDurations :: CalendarDuration -> CalendarDuration -> CalendarDuration
subtractDurations (CalendarDuration d1) (CalendarDuration d2) =
  CalendarDuration
    { years: d1.years - d2.years
    , months: d1.months - d2.months
    , days: d1.days - d2.days
    }

-- | Negate a duration (flip all signs).
negateDuration :: CalendarDuration -> CalendarDuration
negateDuration (CalendarDuration d) =
  CalendarDuration
    { years: negate d.years
    , months: negate d.months
    , days: negate d.days
    }

-- | Check if duration is zero.
isZeroDuration :: CalendarDuration -> Boolean
isZeroDuration (CalendarDuration d) =
  d.years == 0 && d.months == 0 && d.days == 0

-- | Check if duration is non-zero.
isNonZeroDuration :: CalendarDuration -> Boolean
isNonZeroDuration (CalendarDuration d) =
  d.years /= 0 || d.months /= 0 || d.days /= 0

-- | Check if first duration is shorter than second.
-- | Approximation: converts to rough day count for comparison.
isShorter :: CalendarDuration -> CalendarDuration -> Boolean
isShorter d1 d2 = toDaysApprox d1 < toDaysApprox d2
  where
    toDaysApprox :: CalendarDuration -> Int
    toDaysApprox (CalendarDuration d) = d.years * 365 + d.months * 30 + d.days

-- | Check if first duration is longer than second.
isLonger :: CalendarDuration -> CalendarDuration -> Boolean
isLonger d1 d2 = toDaysApprox d1 > toDaysApprox d2
  where
    toDaysApprox :: CalendarDuration -> Int
    toDaysApprox (CalendarDuration d) = d.years * 365 + d.months * 30 + d.days

-- | Normalize duration (12 months -> 1 year, etc.).
normalizeDuration :: CalendarDuration -> CalendarDuration
normalizeDuration (CalendarDuration d) =
  let totalMonths = d.months + (d.years * 12)
      normalizedYears = totalMonths / 12
      normalizedMonths = totalMonths `mod` 12
      -- Don't normalize days to months (variable month lengths)
  in CalendarDuration
       { years: normalizedYears
       , months: normalizedMonths
       , days: d.days
       }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format as ISO 8601 duration (P1Y2M3D).
durationToISO8601 :: CalendarDuration -> String
durationToISO8601 (CalendarDuration d)
  | d.years == 0 && d.months == 0 && d.days == 0 = "P0D"
  | otherwise = "P" <> yearPart <> monthPart <> dayPart
  where
    yearPart = if d.years > 0 then show d.years <> "Y" else ""
    monthPart = if d.months > 0 then show d.months <> "M" else ""
    dayPart = if d.days > 0 then show d.days <> "D" else ""

-- | Format as human-readable string.
durationToHuman :: CalendarDuration -> String
durationToHuman (CalendarDuration d)
  | d.years == 0 && d.months == 0 && d.days == 0 = "0 days"
  | otherwise = joinParts (yearPart <> monthPart <> dayPart)
  where
    yearPart = if d.years > 0 
               then [show d.years <> " " <> pluralize "year" d.years]
               else []
    monthPart = if d.months > 0 
                then [show d.months <> " " <> pluralize "month" d.months]
                else []
    dayPart = if d.days > 0 
              then [show d.days <> " " <> pluralize "day" d.days]
              else []
    
    pluralize :: String -> Int -> String
    pluralize word n = if n == 1 then word else word <> "s"
    
    joinParts :: Array String -> String
    joinParts parts = joinWithComma parts
    
    joinWithComma :: Array String -> String
    joinWithComma [] = ""
    joinWithComma arr = foldParts arr
    
    foldParts :: Array String -> String
    foldParts parts = foldlArray (\acc s -> if acc == "" then s else acc <> ", " <> s) "" parts

-- Simple array fold using Data.Foldable.
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray = foldl
