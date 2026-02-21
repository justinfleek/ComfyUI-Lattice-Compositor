-- | Lattice UI Utilities
-- |
-- | Re-exports Hydrogen formatting utilities plus Lattice-specific helpers.
-- | NO JavaScript FFI except for getElementById (DOM necessity).
-- |
-- | STRAYLIGHT PROTOCOL: Full type safety, no escape hatches.
module Lattice.UI.Utils
  ( -- Re-exports from Hydrogen.Data.Format
    module Hydrogen.Data.Format
    -- Lattice-specific formatting
  , formatFixed
  , formatNumber
    -- Number operations (re-exports from Data.Int/Data.Number)
  , floor
  , ceil
  , round
  , toNumber
  , log
  , pow
    -- String operations
  , padStart
  , padEnd
    -- Hex conversion
  , intToHex
  , hexToInt
    -- Array operations
  , arrayLength
  , arrayIndex
    -- Parsing (safe, with defaults)
  , parseIntOr
  , parseFloatOr
    -- MIDI utilities
  , midiNoteToName
    -- Timecode utilities
  , formatTimecode
  , formatFrameCount
    -- DOM operations (minimal FFI)
  , getElementById
  , getElementByIdImpl
  ) where

import Prelude

import Data.Array (replicate, index, length) as Array
import Data.Int as Int
import Data.Int (hexadecimal, toStringAs, fromStringAs) as IntRadix
import Data.Maybe (Maybe, fromMaybe)
import Data.Nullable (Nullable, toMaybe)
import Data.Number as Number
import Data.Number.Format (toStringWith, fixed)
import Data.String.CodeUnits as SCU
import Effect (Effect)
import Hydrogen.Data.Format (formatBytes, formatBytesCompact, parseBytes, kb, mb, gb, tb, formatNum, formatNumCompact, formatPercent, formatCount, formatDuration, formatDurationCompact, formatDurationMs, percentage, rate, ratio)
import Web.HTML.HTMLDocument as HTMLDocument
import Web.HTML.HTMLElement as HTMLElement

-- =============================================================================
--                                                       // number // formatting
-- =============================================================================

-- | Format a number with fixed decimal places
-- | formatFixed 2 3.14159 == "3.14"
formatFixed :: Int -> Number -> String
formatFixed decimals n = toStringWith (fixed decimals) n

-- | Format a Number with specified decimal places (alias for formatFixed)
-- | formatNumber 2 3.14159 == "3.14"
formatNumber :: Int -> Number -> String
formatNumber = formatFixed

-- =============================================================================
--                                                       // number // operations
-- =============================================================================

-- | Floor a Number to Int
-- | floor 3.7 == 3
floor :: Number -> Int
floor = Int.floor

-- | Ceiling a Number to Int
-- | ceil 3.2 == 4
ceil :: Number -> Int
ceil = Int.ceil

-- | Round a Number to nearest Int
-- | round 3.5 == 4
round :: Number -> Int
round = Int.round

-- | Convert Int to Number
-- | toNumber 42 == 42.0
toNumber :: Int -> Number
toNumber = Int.toNumber

-- | Natural logarithm
-- | log 2.718281828 ~= 1.0
log :: Number -> Number
log = Number.log

-- | Power function
-- | pow 2.0 3.0 == 8.0
pow :: Number -> Number -> Number
pow = Number.pow

-- =============================================================================
--                                                       // string // operations
-- =============================================================================

-- | Pad a string at the start to reach target length
-- | padStart 5 '0' "42" == "00042"
-- | padStart 3 '0' "12345" == "12345"
padStart :: Int -> String -> String -> String
padStart targetLength padStr str =
  let
    currentLength = SCU.length str
    padding = max 0 (targetLength - currentLength)
    -- Repeat padStr enough times and take first padding characters
    paddingStr = SCU.take padding (repeatStr padding padStr)
  in
    paddingStr <> str
  where
    repeatStr :: Int -> String -> String
    repeatStr n s
      | n <= 0 = ""
      | otherwise = s <> repeatStr (n - 1) s

-- | Pad a string at the end to reach target length
-- | padEnd 5 " " "Hi" == "Hi   "
padEnd :: Int -> String -> String -> String
padEnd targetLength padStr str =
  let
    currentLength = SCU.length str
    padding = max 0 (targetLength - currentLength)
    paddingStr = SCU.take padding (repeatStr padding padStr)
  in
    str <> paddingStr
  where
    repeatStr :: Int -> String -> String
    repeatStr n s
      | n <= 0 = ""
      | otherwise = s <> repeatStr (n - 1) s

-- =============================================================================
--                                                              // safe // parsing
-- =============================================================================

-- | Parse an Int from a String, returning a default value on failure
-- | parseIntOr 0 "42" == 42
-- | parseIntOr 0 "abc" == 0
-- | parseIntOr 100 "" == 100
parseIntOr :: Int -> String -> Int
parseIntOr defaultVal str = fromMaybe defaultVal (Int.fromString str)

-- | Parse a Number (float) from a String, returning a default value on failure
-- | parseFloatOr 0.0 "3.14" == 3.14
-- | parseFloatOr 0.0 "abc" == 0.0
parseFloatOr :: Number -> String -> Number
parseFloatOr defaultVal str = fromMaybe defaultVal (Number.fromString str)

-- =============================================================================
--                                                              // hex // conversion
-- =============================================================================

-- | Convert an Int to a hexadecimal String (lowercase)
-- | intToHex 255 == "ff"
-- | intToHex 16 == "10"
intToHex :: Int -> String
intToHex n = IntRadix.toStringAs IntRadix.hexadecimal n

-- | Parse an Int from a hexadecimal String
-- | hexToInt "ff" == 255
-- | hexToInt "10" == 16
-- | hexToInt "invalid" == 0
hexToInt :: String -> Int
hexToInt str = fromMaybe 0 (IntRadix.fromStringAs IntRadix.hexadecimal str)

-- =============================================================================
--                                                            // array // operations
-- =============================================================================

-- | Get the length of an array
-- | arrayLength [1, 2, 3] == 3
arrayLength :: forall a. Array a -> Int
arrayLength = Array.length

-- | Get element at index (returns Maybe)
-- | arrayIndex 0 [1, 2, 3] == Just 1
-- | arrayIndex 5 [1, 2, 3] == Nothing
arrayIndex :: forall a. Int -> Array a -> Maybe a
arrayIndex = flip Array.index

-- =============================================================================
--                                                             // midi // utilities
-- =============================================================================

-- | Convert a MIDI note number to note name
-- | midiNoteToName 60 == "C4"
-- | midiNoteToName 69 == "A4"
-- | midiNoteToName 61 == "C#4"
midiNoteToName :: Int -> String
midiNoteToName noteNum =
  let
    noteNames = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]
    noteName = fromMaybe "?" (Array.index noteNames (noteNum `mod` 12))
    octave = (noteNum / 12) - 1
  in
    noteName <> show octave

-- =============================================================================
--                                                         // timecode // utilities
-- =============================================================================

-- | Format frame number as SMPTE timecode (HH:MM:SS:FF)
-- | formatTimecode 30 1800 == "00:01:00:00"
-- | formatTimecode 24 72 == "00:00:03:00"
formatTimecode :: Int -> Int -> String
formatTimecode fps frame =
  let
    totalSeconds = frame / fps
    remainingFrames = frame `mod` fps
    hours = totalSeconds / 3600
    minutes = (totalSeconds `mod` 3600) / 60
    seconds = totalSeconds `mod` 60
  in
    padStart 2 "0" (show hours) <> ":" <>
    padStart 2 "0" (show minutes) <> ":" <>
    padStart 2 "0" (show seconds) <> ":" <>
    padStart 2 "0" (show remainingFrames)

-- | Format frame count with frame number and total
-- | formatFrameCount 150 300 == "150 / 300"
formatFrameCount :: Int -> Int -> String
formatFrameCount current total = show current <> " / " <> show total

-- =============================================================================
--                                                              // dom // operations
-- =============================================================================

-- | Get an element by ID
-- | This is the ONE necessary FFI for DOM operations - standard pattern from
-- | purescript-radix-main/src/Radix/Pure/Tabs.purs
getElementById :: String -> HTMLDocument.HTMLDocument -> Effect (Maybe HTMLElement.HTMLElement)
getElementById id doc = toMaybe <$> getElementByIdImpl id doc

-- | FFI for getElementById - necessary because the standard web-dom library
-- | returns Element, not HTMLElement, and we need HTMLElement for focus operations
foreign import getElementByIdImpl :: String -> HTMLDocument.HTMLDocument -> Effect (Nullable HTMLElement.HTMLElement)
