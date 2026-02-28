-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // temporal // date
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar date atoms and molecules.
-- |
-- | ## Year
-- | Bounded year type (1-9999 for practical range).
-- |
-- | ## Month
-- | Bounded month type (1-12).
-- |
-- | ## Day
-- | Bounded day-of-month type (1-31).
-- |
-- | ## Date
-- | Complete calendar date (Year + Month + Day).

module Hydrogen.Schema.Temporal.Date
  ( -- * Year
    Year(..)
  , year
  , unwrapYear
  , yearBounds
  
  -- * Month
  , Month(..)
  , month
  , unwrapMonth
  , monthBounds
  , monthName
  , monthShortName
  , daysInMonth
  
  -- * Month Constants
  , january
  , february
  , march
  , april
  , may
  , june
  , july
  , august
  , september
  , october
  , november
  , december
  
  -- * Day
  , Day(..)
  , day
  , unwrapDay
  , dayBounds
  
  -- * Week
  , WeekOfYear(..)
  , weekOfYear
  , unwrapWeekOfYear
  , weekBounds
  
  -- * Date Molecule
  , Date
  , date
  , dateYear
  , dateMonth
  , dateDay
  , isValidDate
  , isLeapYear
  
  -- * Date Operations
  , addDays
  , addMonths
  , addYears
  , compareDates
  , isBefore
  , isAfter
  , isSameDay
  
  -- * Formatting
  , dateToISO8601
  , dateToComponents
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(..)
  , show
  , compare
  , otherwise
  , (&&)
  , (||)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (/=)
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , mod
  , max
  , min
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // year
-- ═════════════════════════════════════════════════════════════════════════════

-- | Year - calendar year.
-- | Bounded to 1-9999 for practical range (CE years).
newtype Year = Year Int

derive instance eqYear :: Eq Year
derive instance ordYear :: Ord Year

instance showYear :: Show Year where
  show (Year y) = "(Year " <> show y <> ")"

-- | Bounds for year.
yearBounds :: Bounded.IntBounds
yearBounds = Bounded.intBounds 1 9999 "Year" "Calendar year (1-9999 CE)"

-- | Construct a bounded year.
year :: Int -> Year
year y = Year (Bounded.clampInt 1 9999 y)

-- | Unwrap year.
unwrapYear :: Year -> Int
unwrapYear (Year y) = y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // month
-- ═════════════════════════════════════════════════════════════════════════════

-- | Month - calendar month (1-12).
newtype Month = Month Int

derive instance eqMonth :: Eq Month
derive instance ordMonth :: Ord Month

instance showMonth :: Show Month where
  show m = "(Month " <> monthShortName m <> ")"

-- | Bounds for month.
monthBounds :: Bounded.IntBounds
monthBounds = Bounded.intBounds 1 12 "Month" "Calendar month (1-12)"

-- | Construct a bounded month.
month :: Int -> Month
month m = Month (Bounded.clampInt 1 12 m)

-- | Unwrap month.
unwrapMonth :: Month -> Int
unwrapMonth (Month m) = m

-- | Get full month name.
monthName :: Month -> String
monthName (Month 1) = "January"
monthName (Month 2) = "February"
monthName (Month 3) = "March"
monthName (Month 4) = "April"
monthName (Month 5) = "May"
monthName (Month 6) = "June"
monthName (Month 7) = "July"
monthName (Month 8) = "August"
monthName (Month 9) = "September"
monthName (Month 10) = "October"
monthName (Month 11) = "November"
monthName (Month 12) = "December"
monthName _ = "Unknown"

-- | Get short month name.
monthShortName :: Month -> String
monthShortName (Month 1) = "Jan"
monthShortName (Month 2) = "Feb"
monthShortName (Month 3) = "Mar"
monthShortName (Month 4) = "Apr"
monthShortName (Month 5) = "May"
monthShortName (Month 6) = "Jun"
monthShortName (Month 7) = "Jul"
monthShortName (Month 8) = "Aug"
monthShortName (Month 9) = "Sep"
monthShortName (Month 10) = "Oct"
monthShortName (Month 11) = "Nov"
monthShortName (Month 12) = "Dec"
monthShortName _ = "???"

-- | Get days in month (requires year for February).
daysInMonth :: Year -> Month -> Int
daysInMonth y (Month 2) = if isLeapYear y then 29 else 28
daysInMonth _ (Month m)
  | m == 4 || m == 6 || m == 9 || m == 11 = 30
  | otherwise = 31

-- Month constants
january :: Month
january = Month 1

february :: Month
february = Month 2

march :: Month
march = Month 3

april :: Month
april = Month 4

may :: Month
may = Month 5

june :: Month
june = Month 6

july :: Month
july = Month 7

august :: Month
august = Month 8

september :: Month
september = Month 9

october :: Month
october = Month 10

november :: Month
november = Month 11

december :: Month
december = Month 12

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // day
-- ═════════════════════════════════════════════════════════════════════════════

-- | Day - day of month (1-31).
newtype Day = Day Int

derive instance eqDay :: Eq Day
derive instance ordDay :: Ord Day

instance showDay :: Show Day where
  show (Day d) = "(Day " <> show d <> ")"

-- | Bounds for day.
dayBounds :: Bounded.IntBounds
dayBounds = Bounded.intBounds 1 31 "Day" "Day of month (1-31)"

-- | Construct a bounded day.
day :: Int -> Day
day d = Day (Bounded.clampInt 1 31 d)

-- | Unwrap day.
unwrapDay :: Day -> Int
unwrapDay (Day d) = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // week
-- ═════════════════════════════════════════════════════════════════════════════

-- | WeekOfYear - ISO week number (1-53).
newtype WeekOfYear = WeekOfYear Int

derive instance eqWeekOfYear :: Eq WeekOfYear
derive instance ordWeekOfYear :: Ord WeekOfYear

instance showWeekOfYear :: Show WeekOfYear where
  show (WeekOfYear w) = "(WeekOfYear " <> show w <> ")"

-- | Bounds for week of year.
weekBounds :: Bounded.IntBounds
weekBounds = Bounded.intBounds 1 53 "WeekOfYear" "ISO week number (1-53)"

-- | Construct a bounded week.
weekOfYear :: Int -> WeekOfYear
weekOfYear w = WeekOfYear (Bounded.clampInt 1 53 w)

-- | Unwrap week.
unwrapWeekOfYear :: WeekOfYear -> Int
unwrapWeekOfYear (WeekOfYear w) = w

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // date
-- ═════════════════════════════════════════════════════════════════════════════

-- | Date - complete calendar date.
type Date =
  { year :: Year
  , month :: Month
  , day :: Day
  }

-- | Construct a date with validation.
-- | Day is clamped to valid range for the month.
date :: Int -> Int -> Int -> Date
date y m d =
  let yr = year y
      mo = month m
      maxDay = daysInMonth yr mo
      dy = day (min d maxDay)
  in { year: yr, month: mo, day: dy }

-- | Get year from date.
dateYear :: Date -> Year
dateYear dt = dt.year

-- | Get month from date.
dateMonth :: Date -> Month
dateMonth dt = dt.month

-- | Get day from date.
dateDay :: Date -> Day
dateDay dt = dt.day

-- | Check if date is valid (day within month range).
isValidDate :: Int -> Int -> Int -> Boolean
isValidDate y m d =
  let yr = year y
      mo = month m
      maxDay = daysInMonth yr mo
  in d >= 1 && d <= maxDay && m >= 1 && m <= 12

-- | Check if year is a leap year.
isLeapYear :: Year -> Boolean
isLeapYear (Year y) =
  (y `mod` 4 == 0 && y `mod` 100 /= 0) || (y `mod` 400 == 0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // date operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add days to a date (simplified - handles basic overflow).
addDays :: Int -> Date -> Date
addDays n dt
  | n == 0 = dt
  | n > 0 = addDaysPositive n dt
  | otherwise = addDaysNegative (0 - n) dt

-- | Add positive days.
addDaysPositive :: Int -> Date -> Date
addDaysPositive n dt =
  let yr = unwrapYear dt.year
      mo = unwrapMonth dt.month
      dy = unwrapDay dt.day
      maxDay = daysInMonth dt.year dt.month
      newDay = dy + n
  in if newDay <= maxDay
     then date yr mo newDay
     else 
       let overflow = newDay - maxDay
           nextMonth = if mo == 12 then 1 else mo + 1
           nextYear = if mo == 12 then yr + 1 else yr
       in addDaysPositive (overflow - 1) (date nextYear nextMonth 1)

-- | Subtract days (add negative).
addDaysNegative :: Int -> Date -> Date
addDaysNegative n dt =
  let yr = unwrapYear dt.year
      mo = unwrapMonth dt.month
      dy = unwrapDay dt.day
      newDay = dy - n
  in if newDay >= 1
     then date yr mo newDay
     else
       let prevMonth = if mo == 1 then 12 else mo - 1
           prevYear = if mo == 1 then yr - 1 else yr
           prevMonthDays = daysInMonth (year prevYear) (month prevMonth)
           overflow = 0 - newDay
       in addDaysNegative overflow (date prevYear prevMonth prevMonthDays)

-- | Add months to a date.
addMonths :: Int -> Date -> Date
addMonths n dt =
  let yr = unwrapYear dt.year
      mo = unwrapMonth dt.month
      dy = unwrapDay dt.day
      totalMonths = (yr * 12) + (mo - 1) + n
      newYear = totalMonths / 12
      newMonth = (totalMonths `mod` 12) + 1
      newYr = year newYear
      newMo = month newMonth
      maxDay = daysInMonth newYr newMo
  in date newYear newMonth (min dy maxDay)

-- | Add years to a date.
addYears :: Int -> Date -> Date
addYears n dt =
  let yr = unwrapYear dt.year
      mo = unwrapMonth dt.month
      dy = unwrapDay dt.day
      newYear = yr + n
      newYr = year newYear
      maxDay = daysInMonth newYr dt.month
  in date newYear mo (min dy maxDay)

-- | Compare two dates.
compareDates :: Date -> Date -> Ordering
compareDates d1 d2 =
  case compare d1.year d2.year of
    EQ -> case compare d1.month d2.month of
            EQ -> compare d1.day d2.day
            other -> other
    other -> other

-- | Is first date before second?
isBefore :: Date -> Date -> Boolean
isBefore d1 d2 = compareDates d1 d2 == LT

-- | Is first date after second?
isAfter :: Date -> Date -> Boolean
isAfter d1 d2 = compareDates d1 d2 == GT

-- | Are dates the same day?
isSameDay :: Date -> Date -> Boolean
isSameDay d1 d2 = compareDates d1 d2 == EQ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format date as ISO 8601 string (YYYY-MM-DD).
dateToISO8601 :: Date -> String
dateToISO8601 dt =
  let yr = unwrapYear dt.year
      mo = unwrapMonth dt.month
      dy = unwrapDay dt.day
  in padYear yr <> "-" <> pad2 mo <> "-" <> pad2 dy

-- | Convert date to component integers.
dateToComponents :: Date -> { year :: Int, month :: Int, day :: Int }
dateToComponents dt =
  { year: unwrapYear dt.year
  , month: unwrapMonth dt.month
  , day: unwrapDay dt.day
  }

-- | Pad number to 2 digits.
pad2 :: Int -> String
pad2 n = if n < 10 then "0" <> show n else show n

-- | Pad year to 4 digits.
padYear :: Int -> String
padYear n
  | n < 10 = "000" <> show n
  | n < 100 = "00" <> show n
  | n < 1000 = "0" <> show n
  | otherwise = show n
