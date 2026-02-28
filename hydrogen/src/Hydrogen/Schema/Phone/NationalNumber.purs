-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // phone // national-number
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NationalNumber — Phone number digits without country code.
-- |
-- | A bounded string type representing the national significant number portion
-- | of a phone number. Contains only digits (0-9), no formatting.
-- |
-- | ## E.164 Specification
-- |
-- | According to ITU-T E.164:
-- | - Maximum total length (including country code): 15 digits
-- | - Maximum national number length: 14 digits (for +1 countries)
-- | - Minimum significant digits: varies by country (typically 4+)
-- |
-- | ## Stored Format
-- |
-- | Always stored as raw digits only: "5551234567"
-- | Never with formatting: NOT "(555) 123-4567"
-- | Formatting is applied at display time by the formatter.

module Hydrogen.Schema.Phone.NationalNumber
  ( -- * Type
    NationalNumber
  
  -- * Construction
  , nationalNumber
  , fromString
  , fromDigits
  , fromDigitAt
  , empty
  
  -- * Accessors
  , toString
  , toDigits
  , digitAt
  , length
  , isEmpty
  
  -- * Manipulation
  , appendDigit
  , prependDigit
  , insertDigitAt
  , dropLast
  , dropFirst
  , removeDigitAt
  , takeDigits
  , dropDigits
  , slice
  , reverse
  , concat
  
  -- * Validation
  , isValid
  , hasMinLength
  , hasMaxLength
  , isLongerThan
  , isShorterThan
  , hasSameLengthAs
  
  -- * Bounds
  , maxLength
  , minUsableLength
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , (<>)
  , (==)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (&&)
  , (+)
  , (-)
  , ($)
  )

import Data.Array (filter, take, index, reverse) as Array
import Data.Maybe (Maybe)
import Data.String (length, take, drop) as String
import Data.String.CodeUnits (toCharArray, fromCharArray) as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // national number
-- ═════════════════════════════════════════════════════════════════════════════

-- | National significant number (digits only, max 14 chars).
-- |
-- | Stores the subscriber number portion of a phone number,
-- | excluding the country code. Always raw digits, no formatting.
newtype NationalNumber = NationalNumber String

derive instance eqNationalNumber :: Eq NationalNumber

instance ordNationalNumber :: Ord NationalNumber where
  compare (NationalNumber a) (NationalNumber b) = compare a b

instance showNationalNumber :: Show NationalNumber where
  show (NationalNumber s) = "NationalNumber \"" <> s <> "\""

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum length per E.164 (15 total minus at least 1 for country code).
maxLength :: Int
maxLength = 14

-- | Minimum usable length (most countries require at least 4 digits).
minUsableLength :: Int
minUsableLength = 4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a national number from a string, extracting only digits.
-- |
-- | Filters out non-digit characters and truncates to max length.
-- | Example: "(555) 123-4567" becomes "5551234567"
nationalNumber :: String -> NationalNumber
nationalNumber s =
  let digits = extractDigits s
      truncated = String.take maxLength digits
  in NationalNumber truncated

-- | Alias for nationalNumber.
fromString :: String -> NationalNumber
fromString = nationalNumber

-- | Create from an array of characters (filters to digits only).
-- |
-- | Useful when processing keyboard input or clipboard data as char arrays.
fromDigits :: Array Char -> NationalNumber
fromDigits chars =
  let digits = Array.filter isDigit chars
      truncated = Array.take maxLength digits
  in NationalNumber (String.fromCharArray truncated)

-- | Create from a single digit character at a position.
-- |
-- | Returns empty if character is not a digit.
fromDigitAt :: Char -> NationalNumber
fromDigitAt c =
  if isDigit c
    then NationalNumber (charToString c)
    else empty

-- | Empty national number.
empty :: NationalNumber
empty = NationalNumber ""

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the digits as a string.
toString :: NationalNumber -> String
toString (NationalNumber s) = s

-- | Get digits as character array.
toDigits :: NationalNumber -> Array Char
toDigits (NationalNumber s) = String.toCharArray s

-- | Get digit at index (0-based).
digitAt :: Int -> NationalNumber -> Maybe Char
digitAt idx (NationalNumber s) = Array.index (String.toCharArray s) idx

-- | Get the number of digits.
length :: NationalNumber -> Int
length (NationalNumber s) = String.length s

-- | Check if empty (no digits).
isEmpty :: NationalNumber -> Boolean
isEmpty (NationalNumber s) = String.length s == 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Append a digit character at the end (ignored if not a digit or at max length).
appendDigit :: Char -> NationalNumber -> NationalNumber
appendDigit c (NationalNumber s) =
  if isDigit c && String.length s <= maxLength - 1
    then NationalNumber (s <> charToString c)
    else NationalNumber s

-- | Prepend a digit character at the start (ignored if not a digit or at max length).
prependDigit :: Char -> NationalNumber -> NationalNumber
prependDigit c (NationalNumber s) =
  if isDigit c && String.length s <= maxLength - 1
    then NationalNumber (charToString c <> s)
    else NationalNumber s

-- | Insert a digit at a specific index (0-based).
-- |
-- | Index is clamped to valid range. Ignored if not a digit or at max length.
insertDigitAt :: Int -> Char -> NationalNumber -> NationalNumber
insertDigitAt idx c (NationalNumber s) =
  if isDigit c && String.length s <= maxLength - 1
    then let 
           clampedIdx = clampIndex idx (String.length s)
           before = String.take clampedIdx s
           after = String.drop clampedIdx s
         in NationalNumber (before <> charToString c <> after)
    else NationalNumber s

-- | Remove the last digit.
dropLast :: NationalNumber -> NationalNumber
dropLast (NationalNumber s) =
  let len = String.length s
  in if len == 0
       then NationalNumber ""
       else NationalNumber (String.take (len - 1) s)

-- | Remove the first digit.
dropFirst :: NationalNumber -> NationalNumber
dropFirst (NationalNumber s) = NationalNumber (String.drop 1 s)

-- | Remove digit at a specific index.
removeDigitAt :: Int -> NationalNumber -> NationalNumber
removeDigitAt idx (NationalNumber s) =
  let len = String.length s
  in if idx < 0 then NationalNumber s
     else if idx >= len then NationalNumber s
     else let before = String.take idx s
              after = String.drop (idx + 1) s
          in NationalNumber (before <> after)

-- | Take first n digits.
takeDigits :: Int -> NationalNumber -> NationalNumber
takeDigits n (NationalNumber s) = NationalNumber (String.take n s)

-- | Drop first n digits.
dropDigits :: Int -> NationalNumber -> NationalNumber
dropDigits n (NationalNumber s) = NationalNumber (String.drop n s)

-- | Extract a slice of digits (start inclusive, end exclusive).
slice :: Int -> Int -> NationalNumber -> NationalNumber
slice start end (NationalNumber s) =
  let len = String.length s
      clampedStart = clampIndex start len
      clampedEnd = clampIndex end len
      sliceLen = if clampedEnd >= clampedStart then clampedEnd - clampedStart else 0
  in NationalNumber (String.take sliceLen (String.drop clampedStart s))

-- | Reverse the digit order.
reverse :: NationalNumber -> NationalNumber
reverse (NationalNumber s) = 
  NationalNumber (String.fromCharArray (Array.reverse (String.toCharArray s)))

-- | Concatenate two national numbers (truncated to max length).
concat :: NationalNumber -> NationalNumber -> NationalNumber
concat (NationalNumber a) (NationalNumber b) = 
  NationalNumber (String.take maxLength (a <> b))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if the national number has a valid length.
isValid :: NationalNumber -> Boolean
isValid nn = hasMinLength nn && hasMaxLength nn

-- | Check if has minimum usable length.
hasMinLength :: NationalNumber -> Boolean
hasMinLength nn = length nn >= minUsableLength

-- | Check if within maximum length.
hasMaxLength :: NationalNumber -> Boolean
hasMaxLength nn = length nn <= maxLength

-- | Check if this number is longer than another.
isLongerThan :: NationalNumber -> NationalNumber -> Boolean
isLongerThan a b = length a > length b

-- | Check if this number is shorter than another.
isShorterThan :: NationalNumber -> NationalNumber -> Boolean
isShorterThan a b = length a < length b

-- | Check if two numbers have the same length.
hasSameLengthAs :: NationalNumber -> NationalNumber -> Boolean
hasSameLengthAs a b = length a == length b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract only digit characters from a string.
extractDigits :: String -> String
extractDigits s = String.fromCharArray $ Array.filter isDigit $ String.toCharArray s

-- | Check if a character is a digit (0-9).
isDigit :: Char -> Boolean
isDigit c = c >= '0' && c <= '9'

-- | Convert a single character to a string.
charToString :: Char -> String
charToString c = String.fromCharArray [c]

-- | Clamp an index to valid range [0, max].
clampIndex :: Int -> Int -> Int
clampIndex idx maxVal =
  if idx <= 0 then 0
  else if idx >= maxVal then maxVal
  else idx
