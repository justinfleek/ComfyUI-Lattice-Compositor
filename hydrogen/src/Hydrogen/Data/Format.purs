-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // data // format
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure formatting functions for display
-- |
-- | This module provides pure, easily testable functions for formatting:
-- | - Bytes (KB, MB, GB, TB)
-- | - Numbers (compact notation, percentages)
-- | - Durations (seconds, minutes, hours)
-- | - Common calculations (percentages, rates)
module Hydrogen.Data.Format
  ( -- * Byte formatting
    formatBytes
  , formatBytesCompact
  , parseBytes
  , kb, mb, gb, tb
    -- * Number formatting
  , formatNum
  , formatNumCompact
  , formatPercent
  , formatCount
    -- * Duration formatting
  , formatDuration
  , formatDurationCompact
  , formatDurationMs
    -- * Calculations
  , percentage
  , rate
  , ratio
  ) where

import Prelude
  ( class Show
  , mod
  , not
  , otherwise
  , show
  , negate
  , ($)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (==)
  , (>=)
  , (<>)
  , (<$>)
  , (||)
  )

import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Number (isFinite)
import Data.Number (fromString) as Number
import Data.String (Pattern(Pattern), split) as S

-- ============================================================
-- Byte Constants
-- ============================================================

-- | 1 Kilobyte in bytes
kb :: Number
kb = 1024.0

-- | 1 Megabyte in bytes
mb :: Number
mb = 1024.0 * kb

-- | 1 Gigabyte in bytes
gb :: Number
gb = 1024.0 * mb

-- | 1 Terabyte in bytes
tb :: Number
tb = 1024.0 * gb

-- ============================================================
-- Byte Formatting
-- ============================================================

-- | Format bytes as human-readable string with space separator
-- | 
-- | ```purescript
-- | formatBytes 1024.0 == "1.0 KB"
-- | formatBytes (2.5 * gb) == "2.5 GB"
-- | formatBytes 0.0 == "0 B"
-- | formatBytes (-1024.0) == "-1.0 KB"
-- | ```
formatBytes :: Number -> String
formatBytes bytes
  | not (isFinite bytes) = "0 B"
  | bytes < 0.0 = "-" <> formatBytes (-bytes)
  | bytes >= tb = formatNum (bytes / tb) <> " TB"
  | bytes >= gb = formatNum (bytes / gb) <> " GB"
  | bytes >= mb = formatNum (bytes / mb) <> " MB"
  | bytes >= kb = formatNum (bytes / kb) <> " KB"
  | otherwise = show (floor bytes) <> " B"

-- | Compact byte format without space separator
-- |
-- | ```purescript
-- | formatBytesCompact (1.5 * gb) == "1.5GB"
-- | ```
formatBytesCompact :: Number -> String
formatBytesCompact bytes
  | not (isFinite bytes) = "0B"
  | bytes < 0.0 = "-" <> formatBytesCompact (-bytes)
  | bytes >= tb = formatNum (bytes / tb) <> "TB"
  | bytes >= gb = formatNum (bytes / gb) <> "GB"
  | bytes >= mb = formatNum (bytes / mb) <> "MB"
  | bytes >= kb = formatNum (bytes / kb) <> "KB"
  | otherwise = show (floor bytes) <> "B"

-- | Parse a bytes string back to number
-- | Returns Nothing for invalid input
-- |
-- | ```purescript
-- | parseBytes "1.0 KB" == Just 1024.0
-- | parseBytes "invalid" == Nothing
-- | ```
parseBytes :: String -> Maybe Number
parseBytes str = 
  let parts = S.split (S.Pattern " ") str
  in case parts of
    [numStr, "TB"] -> (_ * tb) <$> parseNum numStr
    [numStr, "GB"] -> (_ * gb) <$> parseNum numStr
    [numStr, "MB"] -> (_ * mb) <$> parseNum numStr
    [numStr, "KB"] -> (_ * kb) <$> parseNum numStr
    [numStr, "B"] -> parseNum numStr
    _ -> Nothing
  where
  parseNum :: String -> Maybe Number
  parseNum = Number.fromString

-- ============================================================
-- Number Formatting
-- ============================================================

-- | Format a number with 1 decimal place
-- |
-- | ```purescript
-- | formatNum 3.14159 == "3.1"
-- | formatNum 10.0 == "10.0"
-- | ```
formatNum :: Number -> String
formatNum n 
  | not (isFinite n) = "0"
  | otherwise = show (toNumber (floor (n * 10.0)) / 10.0)

-- | Format large numbers compactly (1000 -> 1k, 1000000 -> 1M)
-- |
-- | ```purescript
-- | formatNumCompact 1500.0 == "1.5k"
-- | formatNumCompact 2500000.0 == "2.5M"
-- | formatNumCompact 500.0 == "500"
-- | ```
formatNumCompact :: Number -> String
formatNumCompact n
  | not (isFinite n) = "0"
  | n < 0.0 = "-" <> formatNumCompact (-n)
  | n >= 1000000.0 = formatNum (n / 1000000.0) <> "M"
  | n >= 1000.0 = formatNum (n / 1000.0) <> "k"
  | otherwise = show (floor n)

-- | Format a percentage (0.0 - 1.0 range)
-- |
-- | ```purescript
-- | formatPercent 0.874 == "87.4%"
-- | formatPercent 1.0 == "100.0%"
-- | ```
formatPercent :: Number -> String
formatPercent rate' 
  | not (isFinite rate') = "0%"
  | otherwise = formatNum (rate' * 100.0) <> "%"

-- | Format counts with compact notation
-- |
-- | ```purescript
-- | formatCount 45230 == "45.2k"
-- | formatCount 500 == "500"
-- | ```
formatCount :: Int -> String
formatCount n
  | n >= 1000000 = formatNum (toNumber n / 1000000.0) <> "M"
  | n >= 1000 = formatNum (toNumber n / 1000.0) <> "k"
  | otherwise = show n

-- ============================================================
-- Duration Formatting
-- ============================================================

-- | Format duration in seconds to human readable
-- |
-- | ```purescript
-- | formatDuration 0 == "-"
-- | formatDuration 45 == "45s"
-- | formatDuration 125 == "2m 5s"
-- | formatDuration 3661 == "1h 1m 1s"
-- | ```
formatDuration :: Int -> String
formatDuration secs
  | secs <= 0 = "-"
  | secs < 60 = show secs <> "s"
  | secs < 3600 = show (secs / 60) <> "m " <> show (secs `mod` 60) <> "s"
  | otherwise = 
      let hours = secs / 3600
          mins = (secs `mod` 3600) / 60
          s = secs `mod` 60
      in show hours <> "h " <> show mins <> "m " <> show s <> "s"

-- | Compact duration format (largest unit only)
-- |
-- | ```purescript
-- | formatDurationCompact 125 == "2m"
-- | formatDurationCompact 3661 == "1h"
-- | ```
formatDurationCompact :: Int -> String
formatDurationCompact secs
  | secs <= 0 = "-"
  | secs < 60 = show secs <> "s"
  | secs < 3600 = show (secs / 60) <> "m"
  | otherwise = show (secs / 3600) <> "h"

-- | Format duration in milliseconds
-- |
-- | ```purescript
-- | formatDurationMs 45000 == "45s"
-- | formatDurationMs 125000 == "2m 5s"
-- | ```
formatDurationMs :: Int -> String
formatDurationMs ms = formatDuration (ms / 1000)

-- ============================================================
-- Calculations
-- ============================================================

-- | Calculate percentage as an integer (0-100)
-- | Safe against division by zero
-- |
-- | ```purescript
-- | percentage 750.0 1000.0 == 75
-- | percentage 0.0 0.0 == 0
-- | ```
percentage :: Number -> Number -> Int
percentage _ 0.0 = 0
percentage current limit 
  | not (isFinite current) || not (isFinite limit) = 0
  | otherwise = floor ((current / limit) * 100.0)

-- | Calculate a rate from success/total counts
-- | Safe against division by zero
-- |
-- | ```purescript
-- | rate 90 100 == 0.9
-- | rate 0 0 == 0.0
-- | ```
rate :: Int -> Int -> Number
rate _ 0 = 0.0
rate success total = toNumber success / toNumber total

-- | Calculate a ratio from numerator/denominator
-- | Safe against division by zero
-- |
-- | ```purescript
-- | ratio 3.0 4.0 == 0.75
-- | ratio 1.0 0.0 == 0.0
-- | ```
ratio :: Number -> Number -> Number
ratio _ 0.0 = 0.0
ratio num denom
  | not (isFinite num) || not (isFinite denom) = 0.0
  | otherwise = num / denom
