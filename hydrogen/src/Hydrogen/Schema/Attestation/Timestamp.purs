-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // attestation // timestamp
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | UTC Timestamp — Milliseconds since Unix epoch (1970-01-01T00:00:00Z).
-- |
-- | This is the canonical timestamp type for attestations. It provides:
-- | - Unambiguous point-in-time representation
-- | - No timezone complexity
-- | - Direct serialization to/from Number
-- | - Deterministic ordering
-- |
-- | ## Why Milliseconds?
-- |
-- | - Sufficient precision for scheduling (sub-second events)
-- | - Matches JavaScript Date.now() semantics
-- | - Fits in Number without precision loss until year 275760
-- | - Standard for JSON/API timestamps
-- |
-- | ## Representation
-- |
-- | We use Number (IEEE 754 double) rather than Int because:
-- | - Int is 32-bit, overflows in 2038
-- | - Number safely represents integers up to 2^53
-- | - Milliseconds since epoch easily exceeds 32-bit range

module Hydrogen.Schema.Attestation.Timestamp
  ( Timestamp
  , timestamp
  , unsafeTimestamp
  , toNumber
  , toMillis
  , toSeconds
  , toISO8601
  , fromSeconds
  , epoch
  , addMillis
  , addSeconds
  , addMinutes
  , addHours
  , addDays
  , diff
  -- * Bounds
  , timestampBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , mod
  )

import Data.Int (floor, toNumber) as Int
import Data.Number (floor) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // timestamp
-- ═════════════════════════════════════════════════════════════════════════════

-- | UTC timestamp in milliseconds since Unix epoch.
-- |
-- | Invariant: value >= 0 (no timestamps before 1970)
newtype Timestamp = Timestamp Number

derive instance eqTimestamp :: Eq Timestamp
derive instance ordTimestamp :: Ord Timestamp

instance showTimestamp :: Show Timestamp where
  show ts = toISO8601 ts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Timestamp, clamping to [0, 253402300800000] ms
-- |
-- | Maximum is year 10000 — far enough in the future for any practical use.
timestamp :: Number -> Timestamp
timestamp ms
  | ms < 0.0 = Timestamp 0.0
  | ms > 253402300800000.0 = Timestamp 253402300800000.0
  | otherwise = Timestamp (Number.floor ms)

-- | Create a Timestamp without bounds checking
-- |
-- | Use only when you know the value is valid (non-negative).
unsafeTimestamp :: Number -> Timestamp
unsafeTimestamp = Timestamp

-- | Unix epoch (1970-01-01T00:00:00Z)
epoch :: Timestamp
epoch = Timestamp 0.0

-- | Create timestamp from seconds since epoch
fromSeconds :: Number -> Timestamp
fromSeconds s = timestamp (s * 1000.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract raw Number (milliseconds since epoch)
toNumber :: Timestamp -> Number
toNumber (Timestamp ms) = ms

-- | Alias for toNumber
toMillis :: Timestamp -> Number
toMillis = toNumber

-- | Convert to seconds since epoch
toSeconds :: Timestamp -> Number
toSeconds (Timestamp ms) = ms / 1000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // arithmetic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add milliseconds to timestamp
addMillis :: Number -> Timestamp -> Timestamp
addMillis delta (Timestamp ms) = timestamp (ms + delta)

-- | Add seconds to timestamp
addSeconds :: Number -> Timestamp -> Timestamp
addSeconds delta ts = addMillis (delta * 1000.0) ts

-- | Add minutes to timestamp
addMinutes :: Number -> Timestamp -> Timestamp
addMinutes delta ts = addSeconds (delta * 60.0) ts

-- | Add hours to timestamp
addHours :: Number -> Timestamp -> Timestamp
addHours delta ts = addMinutes (delta * 60.0) ts

-- | Add days to timestamp
addDays :: Number -> Timestamp -> Timestamp
addDays delta ts = addHours (delta * 24.0) ts

-- | Difference between two timestamps in milliseconds
-- |
-- | Returns: t1 - t2 (positive if t1 is later)
diff :: Timestamp -> Timestamp -> Number
diff (Timestamp t1) (Timestamp t2) = t1 - t2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format as ISO 8601 string (simplified)
-- |
-- | Returns: YYYY-MM-DDTHH:MM:SS.sssZ
-- |
-- | Note: This is a pure implementation without timezone database.
-- | It calculates UTC components directly from milliseconds.
toISO8601 :: Timestamp -> String
toISO8601 (Timestamp ms) =
  let
    -- Total seconds and remaining milliseconds
    totalSecs = Number.floor (ms / 1000.0)
    millis = Int.floor (ms - (totalSecs * 1000.0))
    
    -- Days since epoch
    totalDays = Number.floor (totalSecs / 86400.0)
    remainingSecs = totalSecs - (totalDays * 86400.0)
    
    -- Time of day
    hours = Int.floor (remainingSecs / 3600.0)
    remainingAfterHours = remainingSecs - (Int.toNumber hours * 3600.0)
    minutes = Int.floor (remainingAfterHours / 60.0)
    seconds = Int.floor (remainingAfterHours - (Int.toNumber minutes * 60.0))
    
    -- Date calculation (simplified Gregorian)
    dateComponents = daysToYMD (Int.floor totalDays)
  in
    padZero4 dateComponents.year <> "-" <>
    padZero2 dateComponents.month <> "-" <>
    padZero2 dateComponents.day <> "T" <>
    padZero2 hours <> ":" <>
    padZero2 minutes <> ":" <>
    padZero2 seconds <> "." <>
    padZero3 millis <> "Z"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // date helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert days since epoch to year/month/day
-- |
-- | Uses simplified Gregorian calendar calculation.
daysToYMD :: Int -> { year :: Int, month :: Int, day :: Int }
daysToYMD totalDays =
  let
    -- Find year
    yearResult = findYear 1970 totalDays
    year = yearResult.year
    remainingDays = yearResult.remaining
    
    -- Find month within year
    monthResult = findMonth year 1 remainingDays
  in
    { year: year
    , month: monthResult.month
    , day: monthResult.remaining + 1
    }

-- | Find year and remaining days
findYear :: Int -> Int -> { year :: Int, remaining :: Int }
findYear year days
  | days < daysInYear year = { year, remaining: days }
  | otherwise = findYear (year + 1) (days - daysInYear year)

-- | Find month and remaining days
findMonth :: Int -> Int -> Int -> { month :: Int, remaining :: Int }
findMonth year month days
  | month >= 13 = { month: 12, remaining: days }
  | days < daysInMonth year month = { month, remaining: days }
  | otherwise = findMonth year (month + 1) (days - daysInMonth year month)

-- | Days in a given year
daysInYear :: Int -> Int
daysInYear year = if isLeapYear year then 366 else 365

-- | Is this a leap year?
isLeapYear :: Int -> Boolean
isLeapYear year =
  (year `mod` 4 == 0) &&
  ((year `mod` 100 /= 0) || (year `mod` 400 == 0))

-- | Days in a given month (1-indexed)
daysInMonth :: Int -> Int -> Int
daysInMonth year month
  | month == 1 = 31
  | month == 2 = if isLeapYear year then 29 else 28
  | month == 3 = 31
  | month == 4 = 30
  | month == 5 = 31
  | month == 6 = 30
  | month == 7 = 31
  | month == 8 = 31
  | month == 9 = 30
  | month == 10 = 31
  | month == 11 = 30
  | otherwise = 31

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pad number to 2 digits with leading zeros
padZero2 :: Int -> String
padZero2 n
  | n < 10 = "0" <> show n
  | otherwise = show n

-- | Pad number to 3 digits with leading zeros
padZero3 :: Int -> String
padZero3 n
  | n < 10 = "00" <> show n
  | n < 100 = "0" <> show n
  | otherwise = show n

-- | Pad number to 4 digits with leading zeros
padZero4 :: Int -> String
padZero4 n
  | n < 10 = "000" <> show n
  | n < 100 = "00" <> show n
  | n < 1000 = "0" <> show n
  | otherwise = show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Timestamp [0, 253402300800000] ms
-- |
-- | - 0: Unix epoch (1970-01-01T00:00:00Z)
-- | - 253402300800000: Year 10000 — far future ceiling
timestampBounds :: Bounded.NumberBounds
timestampBounds = Bounded.numberBounds 0.0 253402300800000.0 "Timestamp"
  "UTC timestamp in milliseconds since Unix epoch (1970 to year 10000)"
