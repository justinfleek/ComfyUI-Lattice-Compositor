-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // scheduling // recurrence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Recurrence — Rules for repeating calendar events.
-- |
-- | Follows RFC 5545 (iCalendar) RRULE semantics for interoperability.
-- | Supports daily, weekly, monthly, and yearly recurrence patterns.

module Hydrogen.Schema.Scheduling.Recurrence
  ( -- * Types
    Recurrence
  , Frequency(Daily, Weekly, Monthly, Yearly)
  , Weekday(Mon, Tue, Wed, Thu, Fri, Sat, Sun)
  , EndCondition(Never, Until, Count)
  
  -- * Constructors
  , daily
  , weekly
  , weeklyOn
  , biweekly
  , monthly
  , monthlyOnDay
  , yearly
  , custom
  
  -- * Accessors
  , getFrequency
  , getInterval
  , getWeekdays
  , getMonthDay
  , getEndCondition
  
  -- * Queries
  , isInfinite
  , hasWeekdayFilter
  
  -- * Display
  , toDisplayString
  , toRRuleString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , not
  , otherwise
  , (<>)
  , (<)
  , (>)
  , (==)
  )

import Data.Array (intercalate, null)
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // frequency
-- ═════════════════════════════════════════════════════════════════════════════

-- | Recurrence frequency
data Frequency
  = Daily
  | Weekly
  | Monthly
  | Yearly

derive instance eqFrequency :: Eq Frequency
derive instance ordFrequency :: Ord Frequency

instance showFrequency :: Show Frequency where
  show Daily = "Daily"
  show Weekly = "Weekly"
  show Monthly = "Monthly"
  show Yearly = "Yearly"

-- | Convert to iCalendar FREQ value
frequencyToRRule :: Frequency -> String
frequencyToRRule Daily = "DAILY"
frequencyToRRule Weekly = "WEEKLY"
frequencyToRRule Monthly = "MONTHLY"
frequencyToRRule Yearly = "YEARLY"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // weekday
-- ═════════════════════════════════════════════════════════════════════════════

-- | Day of week for recurrence rules
data Weekday
  = Mon
  | Tue
  | Wed
  | Thu
  | Fri
  | Sat
  | Sun

derive instance eqWeekday :: Eq Weekday
derive instance ordWeekday :: Ord Weekday

instance showWeekday :: Show Weekday where
  show Mon = "Monday"
  show Tue = "Tuesday"
  show Wed = "Wednesday"
  show Thu = "Thursday"
  show Fri = "Friday"
  show Sat = "Saturday"
  show Sun = "Sunday"

-- | Convert to iCalendar BYDAY value
weekdayToRRule :: Weekday -> String
weekdayToRRule Mon = "MO"
weekdayToRRule Tue = "TU"
weekdayToRRule Wed = "WE"
weekdayToRRule Thu = "TH"
weekdayToRRule Fri = "FR"
weekdayToRRule Sat = "SA"
weekdayToRRule Sun = "SU"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // end condition
-- ═════════════════════════════════════════════════════════════════════════════

-- | When the recurrence ends
-- |
-- | - Never: Repeats indefinitely
-- | - Until: Repeats until a specific date (year, month, day)
-- | - Count: Repeats a specific number of times
data EndCondition
  = Never
  | Until { year :: Int, month :: Int, day :: Int }
  | Count Int

derive instance eqEndCondition :: Eq EndCondition

instance showEndCondition :: Show EndCondition where
  show Never = "Never"
  show (Until d) = "Until " <> show d.year <> "-" <> show d.month <> "-" <> show d.day
  show (Count n) = "Count " <> show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // recurrence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete recurrence rule
-- |
-- | Composed of:
-- | - Frequency: How often (daily, weekly, monthly, yearly)
-- | - Interval: Every N periods (1 = every, 2 = every other, etc.)
-- | - Weekdays: Which days of week (for weekly recurrence)
-- | - MonthDay: Which day of month (for monthly recurrence)
-- | - EndCondition: When to stop
newtype Recurrence = Recurrence
  { frequency :: Frequency
  , interval :: Int
  , weekdays :: Array Weekday
  , monthDay :: Maybe Int
  , endCondition :: EndCondition
  }

derive instance eqRecurrence :: Eq Recurrence

instance showRecurrence :: Show Recurrence where
  show r = toDisplayString r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Every day
daily :: Recurrence
daily = Recurrence
  { frequency: Daily
  , interval: 1
  , weekdays: []
  , monthDay: Nothing
  , endCondition: Never
  }

-- | Every week (on same day as original event)
weekly :: Recurrence
weekly = Recurrence
  { frequency: Weekly
  , interval: 1
  , weekdays: []
  , monthDay: Nothing
  , endCondition: Never
  }

-- | Every week on specific days
weeklyOn :: Array Weekday -> Recurrence
weeklyOn days = Recurrence
  { frequency: Weekly
  , interval: 1
  , weekdays: days
  , monthDay: Nothing
  , endCondition: Never
  }

-- | Every two weeks
biweekly :: Recurrence
biweekly = Recurrence
  { frequency: Weekly
  , interval: 2
  , weekdays: []
  , monthDay: Nothing
  , endCondition: Never
  }

-- | Every month (on same day of month as original event)
monthly :: Recurrence
monthly = Recurrence
  { frequency: Monthly
  , interval: 1
  , weekdays: []
  , monthDay: Nothing
  , endCondition: Never
  }

-- | Every month on a specific day (1-31)
monthlyOnDay :: Int -> Recurrence
monthlyOnDay day = Recurrence
  { frequency: Monthly
  , interval: 1
  , weekdays: []
  , monthDay: Just (clampDay day)
  , endCondition: Never
  }

-- | Every year (on same date as original event)
yearly :: Recurrence
yearly = Recurrence
  { frequency: Yearly
  , interval: 1
  , weekdays: []
  , monthDay: Nothing
  , endCondition: Never
  }

-- | Custom recurrence with full control
custom 
  :: Frequency 
  -> Int 
  -> Array Weekday 
  -> Maybe Int 
  -> EndCondition 
  -> Recurrence
custom freq interval days monthDay endCond = Recurrence
  { frequency: freq
  , interval: clampInterval interval
  , weekdays: days
  , monthDay: map clampDay monthDay
  , endCondition: endCond
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the recurrence frequency
getFrequency :: Recurrence -> Frequency
getFrequency (Recurrence r) = r.frequency

-- | Get the interval (every N periods)
getInterval :: Recurrence -> Int
getInterval (Recurrence r) = r.interval

-- | Get the weekday filter
getWeekdays :: Recurrence -> Array Weekday
getWeekdays (Recurrence r) = r.weekdays

-- | Get the month day (for monthly recurrence)
getMonthDay :: Recurrence -> Maybe Int
getMonthDay (Recurrence r) = r.monthDay

-- | Get the end condition
getEndCondition :: Recurrence -> EndCondition
getEndCondition (Recurrence r) = r.endCondition

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if recurrence is infinite
isInfinite :: Recurrence -> Boolean
isInfinite (Recurrence r) = r.endCondition == Never

-- | Check if recurrence has weekday filter
hasWeekdayFilter :: Recurrence -> Boolean
hasWeekdayFilter (Recurrence r) = not (null r.weekdays)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Human-readable display string
toDisplayString :: Recurrence -> String
toDisplayString (Recurrence r) =
  let
    freqStr = case r.interval of
      1 -> case r.frequency of
        Daily -> "Daily"
        Weekly -> "Weekly"
        Monthly -> "Monthly"
        Yearly -> "Yearly"
      2 -> case r.frequency of
        Daily -> "Every other day"
        Weekly -> "Biweekly"
        Monthly -> "Every other month"
        Yearly -> "Every other year"
      n -> "Every " <> show n <> " " <> pluralize r.frequency
    
    daysStr = if null r.weekdays
      then ""
      else " on " <> intercalate ", " (map weekdayShort r.weekdays)
    
    endStr = case r.endCondition of
      Never -> ""
      Until d -> " until " <> show d.month <> "/" <> show d.day <> "/" <> show d.year
      Count n -> " (" <> show n <> " times)"
  in
    freqStr <> daysStr <> endStr

-- | Convert to iCalendar RRULE string
toRRuleString :: Recurrence -> String
toRRuleString (Recurrence r) =
  let
    freq = "FREQ=" <> frequencyToRRule r.frequency
    
    interval = if r.interval == 1
      then ""
      else ";INTERVAL=" <> show r.interval
    
    byDay = if null r.weekdays
      then ""
      else ";BYDAY=" <> intercalate "," (map weekdayToRRule r.weekdays)
    
    byMonthDay = case r.monthDay of
      Nothing -> ""
      Just d -> ";BYMONTHDAY=" <> show d
    
    endPart = case r.endCondition of
      Never -> ""
      Until d -> ";UNTIL=" <> padZero4 d.year <> padZero d.month <> padZero d.day
      Count n -> ";COUNT=" <> show n
  in
    "RRULE:" <> freq <> interval <> byDay <> byMonthDay <> endPart

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp interval to valid range (1-999)
clampInterval :: Int -> Int
clampInterval n
  | n < 1 = 1
  | n > 999 = 999
  | otherwise = n

-- | Clamp day to valid range (1-31)
clampDay :: Int -> Int
clampDay n
  | n < 1 = 1
  | n > 31 = 31
  | otherwise = n

-- | Pluralize frequency name
pluralize :: Frequency -> String
pluralize Daily = "days"
pluralize Weekly = "weeks"
pluralize Monthly = "months"
pluralize Yearly = "years"

-- | Short weekday name
weekdayShort :: Weekday -> String
weekdayShort Mon = "Mon"
weekdayShort Tue = "Tue"
weekdayShort Wed = "Wed"
weekdayShort Thu = "Thu"
weekdayShort Fri = "Fri"
weekdayShort Sat = "Sat"
weekdayShort Sun = "Sun"

-- | Pad to 2 digits
padZero :: Int -> String
padZero n
  | n < 10 = "0" <> show n
  | otherwise = show n

-- | Pad to 4 digits
padZero4 :: Int -> String
padZero4 n
  | n < 10 = "000" <> show n
  | n < 100 = "00" <> show n
  | n < 1000 = "0" <> show n
  | otherwise = show n
