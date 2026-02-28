-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // timepicker // format
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TimePicker Format — Pure PureScript time formatting and parsing.
-- |
-- | Handles conversion between TimeOfDay and string representations.
-- | No JavaScript FFI. All parsing and formatting is pure PureScript.
-- |
-- | ## Design Philosophy
-- |
-- | Uses the Schema's TimeOfDay molecule directly. No redundant Time type.
-- | All formatting operations work on bounded Schema atoms.

module Hydrogen.Element.Compound.TimePicker.Format
  ( -- * Formatting
    formatTime
  , format24H
  , format12H
  , formatWithSeconds
  
  -- * Parsing
  , parseTime
  , parse24H
  , parse12H
  
  -- * Conversion Helpers
  , hourTo12
  , hourTo24
  , periodFromHour
  
  -- * String Utilities
  , padZero
  ) where

import Prelude
  ( class Show
  , show
  , otherwise
  , (<>)
  , (+)
  , (-)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (&&)
  , (||)
  , bind
  , pure
  )

import Data.Array (uncons) as Array
import Data.Int (fromString) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, split, toUpper, trim) as String
import Data.String.Pattern (Pattern(Pattern))
import Data.String.CodeUnits (take, drop) as String

import Hydrogen.Schema.Temporal.TimeOfDay as TimeOfDay
import Hydrogen.Element.Compound.TimePicker.Types (HourFormat(Hour12, Hour24), Period(AM, PM))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format time according to hour format setting
-- |
-- | Routes to format24H or format12H based on HourFormat.
formatTime :: HourFormat -> Boolean -> TimeOfDay.TimeOfDay -> String
formatTime hourFormat showSeconds time =
  case hourFormat of
    Hour24 -> if showSeconds then formatWithSeconds time else format24H time
    Hour12 -> format12H time

-- | Format as 24-hour time (HH:MM)
-- |
-- | Example: "14:30"
format24H :: TimeOfDay.TimeOfDay -> String
format24H = TimeOfDay.format24H

-- | Format as 12-hour time with AM/PM (h:MM AM/PM)
-- |
-- | Example: "2:30 PM"
format12H :: TimeOfDay.TimeOfDay -> String
format12H = TimeOfDay.format12H

-- | Format with seconds (HH:MM:SS)
-- |
-- | Example: "14:30:45"
formatWithSeconds :: TimeOfDay.TimeOfDay -> String
formatWithSeconds time =
  let
    rec = TimeOfDay.toRecord time
  in
    padZero rec.hour <> ":" <> padZero rec.minute <> ":" <> padZero rec.second

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // parsing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parse time from string, auto-detecting format
-- |
-- | Handles formats:
-- | - "HH:MM" or "HH:MM:SS" (24-hour)
-- | - "h:MM AM/PM" or "HH:MM AM/PM" (12-hour)
parseTime :: String -> Maybe TimeOfDay.TimeOfDay
parseTime input =
  let
    cleaned = String.toUpper (String.trim input)
    hasAM = containsPattern "AM" cleaned
    hasPM = containsPattern "PM" cleaned
  in
    if hasAM || hasPM
      then parse12H cleaned
      else parse24H cleaned

-- | Parse 24-hour format time
-- |
-- | Accepts: "HH:MM" or "HH:MM:SS"
parse24H :: String -> Maybe TimeOfDay.TimeOfDay
parse24H input =
  let
    parts = String.split (Pattern ":") (String.trim input)
  in
    case parts of
      [hourStr, minuteStr, secondStr] -> do
        h <- parseIntBounded 0 23 hourStr
        m <- parseIntBounded 0 59 minuteStr
        s <- parseIntBounded 0 59 secondStr
        pure (TimeOfDay.timeHMS h m s)
      
      [hourStr, minuteStr] -> do
        h <- parseIntBounded 0 23 hourStr
        m <- parseIntBounded 0 59 minuteStr
        pure (TimeOfDay.timeHM h m)
      
      _ -> Nothing

-- | Parse 12-hour format time with AM/PM
-- |
-- | Accepts: "h:MM AM", "HH:MM PM", "h:MM:SS AM"
parse12H :: String -> Maybe TimeOfDay.TimeOfDay
parse12H input =
  let
    cleaned = String.toUpper (String.trim input)
    hasPM = containsPattern "PM" cleaned
    hasAM = containsPattern "AM" cleaned
    
    -- Remove AM/PM suffix
    timeStr = removePattern "PM" (removePattern "AM" cleaned)
    parts = String.split (Pattern ":") (String.trim timeStr)
  in
    case parts of
      [hourStr, minuteStr, secondStr] -> do
        h12 <- parseIntBounded 1 12 hourStr
        m <- parseIntBounded 0 59 minuteStr
        s <- parseIntBounded 0 59 secondStr
        let h24 = hourTo24 h12 (if hasPM then PM else AM)
        pure (TimeOfDay.timeHMS h24 m s)
      
      [hourStr, minuteStr] -> do
        h12 <- parseIntBounded 1 12 hourStr
        m <- parseIntBounded 0 59 minuteStr
        let h24 = hourTo24 h12 (if hasPM then PM else AM)
        pure (TimeOfDay.timeHM h24 m)
      
      _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // conversion helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert 24-hour value to 12-hour display value
-- |
-- | 0 -> 12 (midnight)
-- | 1-11 -> 1-11 (AM)
-- | 12 -> 12 (noon)
-- | 13-23 -> 1-11 (PM)
hourTo12 :: Int -> Int
hourTo12 h
  | h == 0 = 12
  | h > 12 = h - 12
  | otherwise = h

-- | Convert 12-hour value with period to 24-hour value
-- |
-- | (12, AM) -> 0 (midnight)
-- | (1-11, AM) -> 1-11
-- | (12, PM) -> 12 (noon)
-- | (1-11, PM) -> 13-23
hourTo24 :: Int -> Period -> Int
hourTo24 h period
  | period == AM && h == 12 = 0
  | period == AM = h
  | period == PM && h == 12 = 12
  | otherwise = h + 12

-- | Determine period (AM/PM) from 24-hour value
periodFromHour :: Int -> Period
periodFromHour h
  | h < 12 = AM
  | otherwise = PM

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // string utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pad number to 2 digits with leading zero
padZero :: Int -> String
padZero n
  | n < 10 = "0" <> show n
  | otherwise = show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // internal helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parse integer with bounds checking
parseIntBounded :: Int -> Int -> String -> Maybe Int
parseIntBounded minVal maxVal str = do
  n <- Int.fromString (String.trim str)
  if n >= minVal && n <= maxVal
    then Just n
    else Nothing

-- | Check if string contains a pattern (case-sensitive)
containsPattern :: String -> String -> Boolean
containsPattern pattern str =
  let
    patLen = String.length pattern
    strLen = String.length str
  in
    containsAt pattern str 0 patLen strLen

-- | Helper for containsPattern - check at each position
containsAt :: String -> String -> Int -> Int -> Int -> Boolean
containsAt pattern str pos patLen strLen
  | pos + patLen > strLen = false
  | String.take patLen (String.drop pos str) == pattern = true
  | otherwise = containsAt pattern str (pos + 1) patLen strLen

-- | Remove all occurrences of a pattern from string
removePattern :: String -> String -> String
removePattern pattern str =
  let
    parts = String.split (Pattern pattern) str
  in
    joinStrings parts

-- | Join array of strings (pure PureScript, no FFI)
joinStrings :: Array String -> String
joinStrings = joinWith ""

-- | Join array with separator
joinWith :: String -> Array String -> String
joinWith sep arr = joinWithAcc sep arr ""

-- | Accumulating helper for joinWith
joinWithAcc :: String -> Array String -> String -> String
joinWithAcc sep arr acc =
  case Array.uncons arr of
    Nothing -> acc
    Just { head: x, tail: xs } ->
      if acc == ""
        then joinWithAcc sep xs x
        else joinWithAcc sep xs (acc <> sep <> x)
