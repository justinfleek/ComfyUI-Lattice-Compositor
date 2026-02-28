-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // temporal // time-of-day
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TimeOfDay — Composite molecule representing wall-clock time.
-- |
-- | Composed from Hour, Minute, Second, and Millisecond atoms.
-- | Represents complete time-of-day with millisecond precision.
-- |
-- | ## Design Philosophy
-- |
-- | TimeOfDay is a **molecule** (composite of atoms), not an atom itself.
-- | All arithmetic wraps at 24 hours (86400000 milliseconds).

module Hydrogen.Schema.Temporal.TimeOfDay
  ( -- * Core Type
    TimeOfDay
  
  -- * Constructors
  , timeOfDay
  , timeHM
  , timeHMS
  , midnight
  , noon
  
  -- * Accessors
  , getHour
  , getMinute
  , getSecond
  , getMillisecond
  , toRecord
  
  -- * Operations
  , addHours
  , addMinutes
  , addSeconds
  , addMilliseconds
  , diffMilliseconds
  , compareTimes
  
  -- * Formatting
  , format24H
  , format12H
  , formatISO
  
  -- * Conversion
  , toMillisOfDay
  , fromMillisOfDay
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , compare
  , (<>)
  , (+)
  , (-)
  , (*)
  , (<)
  , (>)
  , (==)
  , mod
  , Ordering
  )

import Data.Int (quot, rem)

import Hydrogen.Schema.Temporal.Hour as Hour
import Hydrogen.Schema.Temporal.Minute as Minute
import Hydrogen.Schema.Temporal.Second as Second
import Hydrogen.Schema.Temporal.Millisecond as Millisecond

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // time of day
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete time of day with hour, minute, second, millisecond
-- |
-- | A molecule composed of Hour, Minute, Second, and Millisecond atoms.
-- | Represents wall-clock time independent of timezone.
newtype TimeOfDay = TimeOfDay
  { hour :: Hour.Hour
  , minute :: Minute.Minute
  , second :: Second.Second
  , millisecond :: Millisecond.Millisecond
  }

derive instance eqTimeOfDay :: Eq TimeOfDay
derive instance ordTimeOfDay :: Ord TimeOfDay

instance showTimeOfDay :: Show TimeOfDay where
  show t = formatISO t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a full TimeOfDay from raw Int values
-- |
-- | Values are clamped to valid ranges by their respective atom constructors.
timeOfDay :: Int -> Int -> Int -> Int -> TimeOfDay
timeOfDay h m s ms = TimeOfDay
  { hour: Hour.hour h
  , minute: Minute.minute m
  , second: Second.second s
  , millisecond: Millisecond.millisecond ms
  }

-- | Create TimeOfDay with just hours and minutes (seconds = 0, ms = 0)
-- |
-- | Useful for calendar event times like "2:30 PM"
timeHM :: Int -> Int -> TimeOfDay
timeHM h m = timeOfDay h m 0 0

-- | Create TimeOfDay with hours, minutes, seconds (ms = 0)
-- |
-- | Useful for standard timestamp display
timeHMS :: Int -> Int -> Int -> TimeOfDay
timeHMS h m s = timeOfDay h m s 0

-- | Midnight (00:00:00.000)
midnight :: TimeOfDay
midnight = timeOfDay 0 0 0 0

-- | Noon (12:00:00.000)
noon :: TimeOfDay
noon = timeOfDay 12 0 0 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the Hour atom
getHour :: TimeOfDay -> Hour.Hour
getHour (TimeOfDay t) = t.hour

-- | Extract the Minute atom
getMinute :: TimeOfDay -> Minute.Minute
getMinute (TimeOfDay t) = t.minute

-- | Extract the Second atom
getSecond :: TimeOfDay -> Second.Second
getSecond (TimeOfDay t) = t.second

-- | Extract the Millisecond atom
getMillisecond :: TimeOfDay -> Millisecond.Millisecond
getMillisecond (TimeOfDay t) = t.millisecond

-- | Convert TimeOfDay to record of raw Ints
-- |
-- | Useful for pattern matching and external APIs
toRecord :: TimeOfDay -> { hour :: Int, minute :: Int, second :: Int, millisecond :: Int }
toRecord (TimeOfDay t) =
  { hour: Hour.toInt t.hour
  , minute: Minute.toInt t.minute
  , second: Second.toInt t.second
  , millisecond: Millisecond.toInt t.millisecond
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add hours to time (wraps at 24)
addHours :: TimeOfDay -> Int -> TimeOfDay
addHours t hours =
  let
    totalMs = toMillisOfDay t + (hours * 3600000)
    wrapped = totalMs `mod` 86400000
  in
    fromMillisOfDay (if wrapped < 0 then wrapped + 86400000 else wrapped)

-- | Add minutes to time (wraps at 24 hours)
addMinutes :: TimeOfDay -> Int -> TimeOfDay
addMinutes t mins =
  let
    totalMs = toMillisOfDay t + (mins * 60000)
    wrapped = totalMs `mod` 86400000
  in
    fromMillisOfDay (if wrapped < 0 then wrapped + 86400000 else wrapped)

-- | Add seconds to time (wraps at 24 hours)
addSeconds :: TimeOfDay -> Int -> TimeOfDay
addSeconds t secs =
  let
    totalMs = toMillisOfDay t + (secs * 1000)
    wrapped = totalMs `mod` 86400000
  in
    fromMillisOfDay (if wrapped < 0 then wrapped + 86400000 else wrapped)

-- | Add milliseconds to time (wraps at 24 hours)
addMilliseconds :: TimeOfDay -> Int -> TimeOfDay
addMilliseconds t ms =
  let
    totalMs = toMillisOfDay t + ms
    wrapped = totalMs `mod` 86400000
  in
    fromMillisOfDay (if wrapped < 0 then wrapped + 86400000 else wrapped)

-- | Difference between two times in milliseconds
-- |
-- | Returns positive if a > b, negative if a < b.
-- | Does not account for day boundaries.
diffMilliseconds :: TimeOfDay -> TimeOfDay -> Int
diffMilliseconds a b = toMillisOfDay a - toMillisOfDay b

-- | Compare two times
compareTimes :: TimeOfDay -> TimeOfDay -> Ordering
compareTimes a b = compare (toMillisOfDay a) (toMillisOfDay b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert time to milliseconds since midnight
-- |
-- | Range: 0 to 86399999 (24 hours - 1 millisecond)
toMillisOfDay :: TimeOfDay -> Int
toMillisOfDay (TimeOfDay t) =
  Hour.toInt t.hour * 3600000 +
  Minute.toInt t.minute * 60000 +
  Second.toInt t.second * 1000 +
  Millisecond.toInt t.millisecond

-- | Create time from milliseconds since midnight
-- |
-- | Wraps at 24 hours (86400000 ms). Negative values wrap backward from midnight.
fromMillisOfDay :: Int -> TimeOfDay
fromMillisOfDay totalMs =
  let
    ms = totalMs `mod` 86400000
    msNorm = if ms < 0 then ms + 86400000 else ms
    
    h = msNorm `quot` 3600000
    remainAfterHours = msNorm `rem` 3600000
    
    m = remainAfterHours `quot` 60000
    remainAfterMinutes = remainAfterHours `rem` 60000
    
    s = remainAfterMinutes `quot` 1000
    msec = remainAfterMinutes `rem` 1000
  in
    timeOfDay h m s msec

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format as 24-hour time (HH:MM)
-- |
-- | Example: "14:30"
format24H :: TimeOfDay -> String
format24H (TimeOfDay t) =
  padZero (Hour.toInt t.hour) <> ":" <> padZero (Minute.toInt t.minute)

-- | Format as 12-hour time with AM/PM (h:MM AM/PM)
-- |
-- | Example: "2:30 PM"
format12H :: TimeOfDay -> String
format12H (TimeOfDay t) =
  let
    h = Hour.toInt t.hour
    hour12 = if h == 0 then 12 else if h > 12 then h - 12 else h
    ampm = if h < 12 then "AM" else "PM"
  in
    show hour12 <> ":" <> padZero (Minute.toInt t.minute) <> " " <> ampm

-- | Format as ISO 8601 time (HH:MM:SS or HH:MM:SS.mmm)
-- |
-- | Example: "14:30:00" or "14:30:00.500"
formatISO :: TimeOfDay -> String
formatISO (TimeOfDay t) =
  let
    base = padZero (Hour.toInt t.hour) <> ":" <>
           padZero (Minute.toInt t.minute) <> ":" <>
           padZero (Second.toInt t.second)
    ms = Millisecond.toInt t.millisecond
  in
    if ms == 0 then base else base <> "." <> padZero3 ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pad number to 2 digits with leading zero
padZero :: Int -> String
padZero n
  | n < 10 = "0" <> show n
  | otherwise = show n

-- | Pad number to 3 digits with leading zeros
padZero3 :: Int -> String
padZero3 n
  | n < 10 = "00" <> show n
  | n < 100 = "0" <> show n
  | otherwise = show n
