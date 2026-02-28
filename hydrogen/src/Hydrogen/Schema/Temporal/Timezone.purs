-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // temporal // timezone
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Timezone — UTC offset and IANA timezone identifier atoms.
-- |
-- | Represents timezone information for scheduling and datetime display.
-- | All data is pure PureScript lookup tables — no JavaScript Intl API.
-- |
-- | ## Design Philosophy
-- |
-- | Timezones are complex due to DST rules that change over time.
-- | This module provides:
-- | - UtcOffset: Fixed offset from UTC (for storage/transmission)
-- | - TimezoneId: IANA identifier (for DST-aware display)
-- |
-- | For full DST support, use TimezoneId with external DST rule data.
-- | UtcOffset is sufficient for most scheduling use cases.

module Hydrogen.Schema.Temporal.Timezone
  ( -- * UTC Offset
    UtcOffset
  , utcOffset
  , utcOffsetFromMinutes
  , unsafeUtcOffset
  , utc
  , offsetHours
  , offsetMinutes
  , totalOffsetMinutes
  , formatOffset
  , formatOffsetISO
  
  -- * Timezone Identifiers
  , TimezoneId
  , timezoneId
  , unsafeTimezoneId
  , getIdentifier
  , getDisplayName
  , getStandardOffset
  
  -- * Common Timezones
  , utcZone
  , americaNewYork
  , americaLosAngeles
  , americaChicago
  , americaDenver
  , europeLondon
  , europeParis
  , europeBerlin
  , asiaTokyo
  , asiaShanghai
  , asiaDubai
  , australiaSydney
  , pacificHonolulu
  
  -- * Lookup
  , allTimezones
  , findTimezone
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , (<>)
  , (<)
  , (>)
  , (>=)
  , (==)
  , (*)
  , (+)
  , (-)
  , (/)
  , mod
  )

import Data.Array (find)
import Data.Maybe (Maybe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // utc offset
-- ═════════════════════════════════════════════════════════════════════════════

-- | UTC offset in minutes
-- |
-- | Bounded to valid range: -720 to +840 minutes (-12:00 to +14:00).
-- | Stored as total minutes for precision (some zones have :30 or :45 offsets).
newtype UtcOffset = UtcOffset Int

derive instance eqUtcOffset :: Eq UtcOffset
derive instance ordUtcOffset :: Ord UtcOffset

instance showUtcOffset :: Show UtcOffset where
  show o = formatOffset o

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // offset constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a UTC offset from hours and minutes
-- |
-- | Hours: -12 to +14, Minutes: 0 to 59
-- | Clamps to valid range.
utcOffset :: Int -> Int -> UtcOffset
utcOffset hours mins =
  let
    -- Clamp hours
    h = if hours < (-12) then (-12) else if hours > 14 then 14 else hours
    -- Clamp minutes to 0-59
    m = if mins < 0 then 0 else if mins > 59 then 59 else mins
    -- Calculate total, respecting sign
    total = if h < 0 then h * 60 - m else h * 60 + m
    -- Final clamp
    clamped = if total < (-720) then (-720) else if total > 840 then 840 else total
  in
    UtcOffset clamped

-- | Create a UTC offset from total minutes
-- |
-- | Range: -720 to +840 (-12:00 to +14:00)
utcOffsetFromMinutes :: Int -> UtcOffset
utcOffsetFromMinutes mins
  | mins < (-720) = UtcOffset (-720)
  | mins > 840 = UtcOffset 840
  | otherwise = UtcOffset mins

-- | Create a UTC offset without bounds checking
unsafeUtcOffset :: Int -> UtcOffset
unsafeUtcOffset = UtcOffset

-- | UTC (zero offset)
utc :: UtcOffset
utc = UtcOffset 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // offset accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the hours component of the offset
offsetHours :: UtcOffset -> Int
offsetHours (UtcOffset mins) = mins / 60

-- | Get the minutes component of the offset (0-59)
offsetMinutes :: UtcOffset -> Int
offsetMinutes (UtcOffset mins) = abs (mins `mod` 60)

-- | Get total offset in minutes
totalOffsetMinutes :: UtcOffset -> Int
totalOffsetMinutes (UtcOffset mins) = mins

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // offset formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format offset as human-readable string
-- |
-- | Examples: "UTC", "UTC+5", "UTC-8", "UTC+5:30", "UTC+5:45"
formatOffset :: UtcOffset -> String
formatOffset (UtcOffset 0) = "UTC"
formatOffset (UtcOffset mins) =
  let
    sign = if mins >= 0 then "+" else ""
    h = mins / 60
    m = abs (mins `mod` 60)
  in
    if m == 0
      then "UTC" <> sign <> show h
      else "UTC" <> sign <> show h <> ":" <> padZero m

-- | Format offset as ISO 8601 string
-- |
-- | Examples: "Z", "+05:00", "-08:00", "+05:30"
formatOffsetISO :: UtcOffset -> String
formatOffsetISO (UtcOffset 0) = "Z"
formatOffsetISO (UtcOffset mins) =
  let
    sign = if mins >= 0 then "+" else "-"
    totalAbs = abs mins
    h = totalAbs / 60
    m = totalAbs `mod` 60
  in
    sign <> padZero h <> ":" <> padZero m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // timezone identifier
-- ═════════════════════════════════════════════════════════════════════════════

-- | IANA timezone identifier
-- |
-- | Represents a named timezone with DST rules.
-- | The identifier follows IANA format: "Area/Location"
newtype TimezoneId = TimezoneId
  { identifier :: String
  , displayName :: String
  , standardOffset :: UtcOffset
  }

derive instance eqTimezoneId :: Eq TimezoneId
derive instance ordTimezoneId :: Ord TimezoneId

instance showTimezoneId :: Show TimezoneId where
  show (TimezoneId tz) = tz.identifier

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // timezone constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a timezone identifier
-- |
-- | For custom/dynamic timezones. Prefer the predefined constants.
timezoneId :: String -> String -> UtcOffset -> TimezoneId
timezoneId id name offset = TimezoneId
  { identifier: id
  , displayName: name
  , standardOffset: offset
  }

-- | Create a timezone identifier without validation
unsafeTimezoneId :: String -> String -> UtcOffset -> TimezoneId
unsafeTimezoneId = timezoneId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // timezone accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the IANA identifier string
getIdentifier :: TimezoneId -> String
getIdentifier (TimezoneId tz) = tz.identifier

-- | Get the human-readable display name
getDisplayName :: TimezoneId -> String
getDisplayName (TimezoneId tz) = tz.displayName

-- | Get the standard (non-DST) UTC offset
getStandardOffset :: TimezoneId -> UtcOffset
getStandardOffset (TimezoneId tz) = tz.standardOffset

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // common timezones
-- ═════════════════════════════════════════════════════════════════════════════

-- | UTC timezone
utcZone :: TimezoneId
utcZone = timezoneId "UTC" "Coordinated Universal Time" utc

-- | Eastern Time (US)
americaNewYork :: TimezoneId
americaNewYork = timezoneId "America/New_York" "Eastern Time" (utcOffset (-5) 0)

-- | Pacific Time (US)
americaLosAngeles :: TimezoneId
americaLosAngeles = timezoneId "America/Los_Angeles" "Pacific Time" (utcOffset (-8) 0)

-- | Central Time (US)
americaChicago :: TimezoneId
americaChicago = timezoneId "America/Chicago" "Central Time" (utcOffset (-6) 0)

-- | Mountain Time (US)
americaDenver :: TimezoneId
americaDenver = timezoneId "America/Denver" "Mountain Time" (utcOffset (-7) 0)

-- | British Time
europeLondon :: TimezoneId
europeLondon = timezoneId "Europe/London" "British Time" utc

-- | Central European Time
europeParis :: TimezoneId
europeParis = timezoneId "Europe/Paris" "Central European Time" (utcOffset 1 0)

-- | Central European Time
europeBerlin :: TimezoneId
europeBerlin = timezoneId "Europe/Berlin" "Central European Time" (utcOffset 1 0)

-- | Japan Standard Time
asiaTokyo :: TimezoneId
asiaTokyo = timezoneId "Asia/Tokyo" "Japan Standard Time" (utcOffset 9 0)

-- | China Standard Time
asiaShanghai :: TimezoneId
asiaShanghai = timezoneId "Asia/Shanghai" "China Standard Time" (utcOffset 8 0)

-- | Gulf Standard Time
asiaDubai :: TimezoneId
asiaDubai = timezoneId "Asia/Dubai" "Gulf Standard Time" (utcOffset 4 0)

-- | Australian Eastern Time
australiaSydney :: TimezoneId
australiaSydney = timezoneId "Australia/Sydney" "Australian Eastern Time" (utcOffset 10 0)

-- | Hawaii-Aleutian Time
pacificHonolulu :: TimezoneId
pacificHonolulu = timezoneId "Pacific/Honolulu" "Hawaii-Aleutian Time" (utcOffset (-10) 0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // lookup
-- ═════════════════════════════════════════════════════════════════════════════

-- | All predefined timezones
allTimezones :: Array TimezoneId
allTimezones =
  [ utcZone
  , americaNewYork
  , americaLosAngeles
  , americaChicago
  , americaDenver
  , europeLondon
  , europeParis
  , europeBerlin
  , asiaTokyo
  , asiaShanghai
  , asiaDubai
  , australiaSydney
  , pacificHonolulu
  ]

-- | Find a timezone by IANA identifier
findTimezone :: String -> Maybe TimezoneId
findTimezone id = find (\tz -> getIdentifier tz == id) allTimezones

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pad number to 2 digits with leading zero
padZero :: Int -> String
padZero n
  | n < 10 = "0" <> show n
  | otherwise = show n

-- | Absolute value of an Int
abs :: Int -> Int
abs n = if n < 0 then negate n else n
