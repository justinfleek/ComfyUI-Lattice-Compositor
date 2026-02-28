-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // temporal // datetime
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DateTime molecule combining Date and TimeOfDay.
-- |
-- | ## DateTime
-- | Complete point in time with date, time, and optional timezone.
-- |
-- | ## DateRange
-- | A span between two dates.
-- |
-- | ## DateTimeRange
-- | A span between two datetimes.

module Hydrogen.Schema.Temporal.DateTime
  ( -- * DateTime
    DateTime
  , dateTime
  , dateTimeDate
  , dateTimeTime
  , dateTimeTimezone
  , showDateTime
  , sameDateTime
  
  -- * DateTime Operations
  , dateTimeToISO8601
  , compareDateTimes
  , isDateTimeBefore
  , isDateTimeAfter
  , isDateTimeSameOrBefore
  , isDateTimeSameOrAfter
  
  -- * Date Range
  , DateRange
  , dateRange
  , dateRangeStart
  , dateRangeEnd
  , dateRangeDays
  , dateRangeContains
  , dateRangeOverlaps
  , showDateRange
  , sameDateRange
  
  -- * DateTime Range
  , DateTimeRange
  , dateTimeRange
  , dateTimeRangeStart
  , dateTimeRangeEnd
  , dateTimeRangeDurationMs
  , showDateTimeRange
  , sameDateTimeRange
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , otherwise
  , Ordering(..)
  , (&&)
  , (||)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (<>)
  , (+)
  , (-)
  , (*)
  )

import Data.Int (toNumber) as Int
import Hydrogen.Schema.Temporal.Date as Date
import Hydrogen.Schema.Temporal.TimeOfDay as Time
import Hydrogen.Schema.Temporal.Timezone as TZ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // datetime
-- ═════════════════════════════════════════════════════════════════════════════

-- | DateTime - complete point in time.
type DateTime =
  { date :: Date.Date
  , time :: Time.TimeOfDay
  , timezone :: TZ.TimezoneId
  }

-- | Construct a datetime.
dateTime :: Date.Date -> Time.TimeOfDay -> TZ.TimezoneId -> DateTime
dateTime d t tz =
  { date: d
  , time: t
  , timezone: tz
  }

-- | Get date component.
dateTimeDate :: DateTime -> Date.Date
dateTimeDate dt = dt.date

-- | Get time component.
dateTimeTime :: DateTime -> Time.TimeOfDay
dateTimeTime dt = dt.time

-- | Get timezone.
dateTimeTimezone :: DateTime -> TZ.TimezoneId
dateTimeTimezone dt = dt.timezone

-- | Show datetime for debug output.
showDateTime :: DateTime -> String
showDateTime dt = "(DateTime " <> dateTimeToISO8601 dt <> ")"

-- | Check if two datetimes are equal.
sameDateTime :: DateTime -> DateTime -> Boolean
sameDateTime dt1 dt2 = compareDateTimes dt1 dt2 == EQ

-- | Format as ISO 8601 string.
dateTimeToISO8601 :: DateTime -> String
dateTimeToISO8601 dt =
  Date.dateToISO8601 dt.date <> "T" <> Time.formatISO dt.time <> TZ.formatOffsetISO (TZ.getStandardOffset dt.timezone)

-- | Compare two datetimes (assumes same timezone or UTC).
compareDateTimes :: DateTime -> DateTime -> Ordering
compareDateTimes dt1 dt2 =
  case Date.compareDates dt1.date dt2.date of
    EQ -> Time.compareTimes dt1.time dt2.time
    other -> other

-- | Is first datetime before second?
isDateTimeBefore :: DateTime -> DateTime -> Boolean
isDateTimeBefore dt1 dt2 = compareDateTimes dt1 dt2 == LT

-- | Is first datetime after second?
isDateTimeAfter :: DateTime -> DateTime -> Boolean
isDateTimeAfter dt1 dt2 = compareDateTimes dt1 dt2 == GT

-- | Is first datetime same as or before second?
isDateTimeSameOrBefore :: DateTime -> DateTime -> Boolean
isDateTimeSameOrBefore dt1 dt2 =
  let result = compareDateTimes dt1 dt2
  in result == LT || result == EQ

-- | Is first datetime same as or after second?
isDateTimeSameOrAfter :: DateTime -> DateTime -> Boolean
isDateTimeSameOrAfter dt1 dt2 =
  let result = compareDateTimes dt1 dt2
  in result == GT || result == EQ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // date range
-- ═════════════════════════════════════════════════════════════════════════════

-- | DateRange - span between two dates (inclusive).
type DateRange =
  { start :: Date.Date
  , end :: Date.Date
  }

-- | Construct a date range (ensures start <= end).
dateRange :: Date.Date -> Date.Date -> DateRange
dateRange s e =
  if Date.isBefore s e || Date.isSameDay s e
  then { start: s, end: e }
  else { start: e, end: s }

-- | Get range start.
dateRangeStart :: DateRange -> Date.Date
dateRangeStart r = r.start

-- | Get range end.
dateRangeEnd :: DateRange -> Date.Date
dateRangeEnd r = r.end

-- | Count days in range (inclusive).
dateRangeDays :: DateRange -> Int
dateRangeDays r =
  countDaysBetween r.start r.end + 1

-- | Check if date is within range (inclusive).
dateRangeContains :: DateRange -> Date.Date -> Boolean
dateRangeContains r d =
  (Date.isSameDay r.start d || Date.isBefore r.start d) &&
  (Date.isSameDay r.end d || Date.isAfter r.end d)

-- | Check if two ranges overlap.
dateRangeOverlaps :: DateRange -> DateRange -> Boolean
dateRangeOverlaps r1 r2 =
  (Date.isBefore r1.start r2.end || Date.isSameDay r1.start r2.end) &&
  (Date.isAfter r1.end r2.start || Date.isSameDay r1.end r2.start)

-- | Show date range for debug output.
showDateRange :: DateRange -> String
showDateRange r =
  "(DateRange " <> Date.dateToISO8601 r.start <> " to " <> Date.dateToISO8601 r.end <> ")"

-- | Check if two date ranges are equal.
sameDateRange :: DateRange -> DateRange -> Boolean
sameDateRange r1 r2 =
  Date.isSameDay r1.start r2.start && Date.isSameDay r1.end r2.end

-- | Count days between two dates (simple approximation).
countDaysBetween :: Date.Date -> Date.Date -> Int
countDaysBetween d1 d2 =
  let y1 = Date.unwrapYear (Date.dateYear d1)
      m1 = Date.unwrapMonth (Date.dateMonth d1)
      day1 = Date.unwrapDay (Date.dateDay d1)
      y2 = Date.unwrapYear (Date.dateYear d2)
      m2 = Date.unwrapMonth (Date.dateMonth d2)
      day2 = Date.unwrapDay (Date.dateDay d2)
      -- Simplified: days from epoch approximation
      days1 = y1 * 365 + m1 * 30 + day1
      days2 = y2 * 365 + m2 * 30 + day2
  in if days2 >= days1 then days2 - days1 else days1 - days2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // datetime range
-- ═════════════════════════════════════════════════════════════════════════════

-- | DateTimeRange - span between two datetimes.
type DateTimeRange =
  { start :: DateTime
  , end :: DateTime
  }

-- | Construct a datetime range (ensures start <= end).
dateTimeRange :: DateTime -> DateTime -> DateTimeRange
dateTimeRange s e =
  if isDateTimeBefore s e || compareDateTimes s e == EQ
  then { start: s, end: e }
  else { start: e, end: s }

-- | Get range start.
dateTimeRangeStart :: DateTimeRange -> DateTime
dateTimeRangeStart r = r.start

-- | Get range end.
dateTimeRangeEnd :: DateTimeRange -> DateTime
dateTimeRangeEnd r = r.end

-- | Calculate duration in milliseconds (approximation).
dateTimeRangeDurationMs :: DateTimeRange -> Number
dateTimeRangeDurationMs r =
  let daysDiff = countDaysBetween r.start.date r.end.date
      startMs = Time.toMillisOfDay r.start.time
      endMs = Time.toMillisOfDay r.end.time
      dayMs = 86400000.0  -- 24 * 60 * 60 * 1000
  in (intToNumber daysDiff * dayMs) + (intToNumber endMs - intToNumber startMs)

-- | Show datetime range for debug output.
showDateTimeRange :: DateTimeRange -> String
showDateTimeRange r =
  "(DateTimeRange " <> dateTimeToISO8601 r.start <> " to " <> dateTimeToISO8601 r.end <> ")"

-- | Check if two datetime ranges are equal.
sameDateTimeRange :: DateTimeRange -> DateTimeRange -> Boolean
sameDateTimeRange r1 r2 =
  sameDateTime r1.start r2.start && sameDateTime r1.end r2.end

-- | Convert Int to Number.
intToNumber :: Int -> Number
intToNumber = Int.toNumber
