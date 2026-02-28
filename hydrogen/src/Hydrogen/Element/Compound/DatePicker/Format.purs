-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // datepicker // format
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DatePicker Format — Pure date formatting and parsing.
-- |
-- | This module provides date string formatting and parsing functions.
-- | **Pure PureScript implementation** — no JavaScript FFI required.
-- |
-- | ## Design Philosophy
-- |
-- | All formatting uses explicit lookup tables for month names.
-- | Parsing is done with string splitting and integer validation.
-- | No Intl API, no locale dependencies beyond what we embed.

module Hydrogen.Element.Compound.DatePicker.Format
  ( -- * Formatting
    formatDate
  , formatDateISO
  , formatDateUSShort
  , formatDateUSLong
  , formatDateEUShort
  , formatDateEULong
  
  -- * Parsing
  , parseDate
  , parseISO
  , parseUSShort
  , parseEUShort
  
  -- * Helpers
  , monthNameLong
  , padZero
  ) where

import Prelude
  ( show
  , bind
  , (<>)
  , (-)
  , (>=)
  , (&&)
  , (<=)
  )

import Data.Array as Array
import Data.Int (fromString) as Int
import Data.Maybe (Maybe(Nothing, Just))
import Data.String as String

import Hydrogen.Element.Compound.Calendar (CalendarDate, getDaysInMonth)
import Hydrogen.Element.Compound.DatePicker.Types (DateFormat(ISO, USShort, USLong, EUShort, EULong, Custom))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format a date according to the specified format.
-- |
-- | Dispatches to format-specific functions based on DateFormat.
formatDate :: DateFormat -> CalendarDate -> String
formatDate format date = case format of
  ISO -> formatDateISO date
  USShort -> formatDateUSShort date
  USLong -> formatDateUSLong date
  EUShort -> formatDateEUShort date
  EULong -> formatDateEULong date
  Custom _ -> formatDateISO date  -- Custom falls back to ISO

-- | Format as ISO 8601: YYYY-MM-DD
-- |
-- | Example: "2024-01-15"
formatDateISO :: CalendarDate -> String
formatDateISO date =
  padZero 4 date.year <> "-" <>
  padZero 2 date.month <> "-" <>
  padZero 2 date.day

-- | Format as US short: MM/DD/YYYY
-- |
-- | Example: "01/15/2024"
formatDateUSShort :: CalendarDate -> String
formatDateUSShort date =
  padZero 2 date.month <> "/" <>
  padZero 2 date.day <> "/" <>
  show date.year

-- | Format as US long: MMMM D, YYYY
-- |
-- | Example: "January 15, 2024"
formatDateUSLong :: CalendarDate -> String
formatDateUSLong date =
  monthNameLong date.month <> " " <>
  show date.day <> ", " <>
  show date.year

-- | Format as EU short: DD/MM/YYYY
-- |
-- | Example: "15/01/2024"
formatDateEUShort :: CalendarDate -> String
formatDateEUShort date =
  padZero 2 date.day <> "/" <>
  padZero 2 date.month <> "/" <>
  show date.year

-- | Format as EU long: D MMMM YYYY
-- |
-- | Example: "15 January 2024"
formatDateEULong :: CalendarDate -> String
formatDateEULong date =
  show date.day <> " " <>
  monthNameLong date.month <> " " <>
  show date.year

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // parsing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parse a date string according to the specified format.
-- |
-- | Returns Nothing if parsing fails or date is invalid.
parseDate :: DateFormat -> String -> Maybe CalendarDate
parseDate format str = case format of
  ISO -> parseISO str
  USShort -> parseUSShort str
  EUShort -> parseEUShort str
  USLong -> parseISO str     -- Long formats fall back to ISO for parsing
  EULong -> parseISO str     -- (users rarely type long format)
  Custom _ -> parseISO str

-- | Parse ISO format: YYYY-MM-DD
-- |
-- | Validates month/day ranges including leap years.
parseISO :: String -> Maybe CalendarDate
parseISO str = case String.split (String.Pattern "-") str of
  [y, m, d] -> do
    year <- parseInt y
    month <- parseInt m
    day <- parseInt d
    if isValidDate year month day
      then Just { year, month, day }
      else Nothing
  _ -> Nothing

-- | Parse US short format: MM/DD/YYYY
-- |
-- | Validates month/day ranges including leap years.
parseUSShort :: String -> Maybe CalendarDate
parseUSShort str = case String.split (String.Pattern "/") str of
  [m, d, y] -> do
    year <- parseInt y
    month <- parseInt m
    day <- parseInt d
    if isValidDate year month day
      then Just { year, month, day }
      else Nothing
  _ -> Nothing

-- | Parse EU short format: DD/MM/YYYY
-- |
-- | Validates month/day ranges including leap years.
parseEUShort :: String -> Maybe CalendarDate
parseEUShort str = case String.split (String.Pattern "/") str of
  [d, m, y] -> do
    year <- parseInt y
    month <- parseInt m
    day <- parseInt d
    if isValidDate year month day
      then Just { year, month, day }
      else Nothing
  _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if date components form a valid date.
-- |
-- | Uses daysInMonth from Calendar which handles leap years.
isValidDate :: Int -> Int -> Int -> Boolean
isValidDate year month day =
  year >= 1 && year <= 9999 &&
  month >= 1 && month <= 12 &&
  day >= 1 && day <= getDaysInMonth year month

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Full month name lookup (English).
-- |
-- | Pure PureScript lookup table. No JavaScript Intl API.
monthNameLong :: Int -> String
monthNameLong m = case m of
  1 -> "January"
  2 -> "February"
  3 -> "March"
  4 -> "April"
  5 -> "May"
  6 -> "June"
  7 -> "July"
  8 -> "August"
  9 -> "September"
  10 -> "October"
  11 -> "November"
  12 -> "December"
  _ -> "Unknown"

-- | Pad number with leading zeros to specified width.
-- |
-- | Pure PureScript implementation.
padZero :: Int -> Int -> String
padZero width n =
  let
    str = show n
    len = String.length str
  in
    if len >= width
      then str
      else String.joinWith "" (Array.replicate (width - len) "0") <> str

-- | Parse an integer from string.
-- |
-- | Uses Data.Int.fromString for safe parsing.
parseInt :: String -> Maybe Int
parseInt str = Int.fromString (String.trim str)


