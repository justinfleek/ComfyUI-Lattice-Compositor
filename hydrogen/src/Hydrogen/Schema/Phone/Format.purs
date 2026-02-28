-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // phone // format
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Phone number formatting engine.
-- |
-- | Provides format-as-you-type functionality with cursor position preservation.
-- | This is pure data transformation — no side effects, no FFI.
-- |
-- | ## Key Features
-- |
-- | - Format phone numbers according to country patterns
-- | - Preserve cursor position through format changes
-- | - Support partial formatting during input
-- | - Calculate cursor position after formatting
-- |
-- | ## Format Pattern Syntax
-- |
-- | - `#` = digit placeholder
-- | - Any other character = literal (inserted as-is)
-- |
-- | Examples:
-- | - `(###) ###-####` — US format
-- | - `## #### ####` — Australia format
-- | - `##-####-####` — Japan format

module Hydrogen.Schema.Phone.Format
  ( -- * Formatting
    format
  , formatWithPattern
  , formatPartial
  
  -- * Cursor Handling
  , CursorResult
  , cursorPosition
  , formattedValue
  , formatWithCursor
  , calculateCursorAfterFormat
  , calculateCursorAfterDelete
  
  -- * Unformatting
  , unformat
  , extractDigits
  
  -- * Pattern Analysis
  , digitPositions
  , literalPositions
  , isDigitPosition
  , positionToDigitIndex
  , digitIndexToPosition
  
  -- * Pattern Utilities
  , patternDigitCount
  , nationalNumberLength
  , findFirstDigitPosition
  , appendDigit
  , formatOrDefault
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , (<>)
  , (==)
  , (/=)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (+)
  , (-)
  , ($)
  , (&&)
  )

import Data.Array (filter, length, mapWithIndex, findIndex, take, drop, index, reverse, snoc) as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.String (length) as String
import Data.String.CodeUnits (toCharArray, fromCharArray) as String
import Data.Tuple (Tuple(Tuple), fst, snd)

import Hydrogen.Schema.Phone.Country (Country, FormatPattern, formatPattern, patternToString)
import Hydrogen.Schema.Phone.NationalNumber (NationalNumber)
import Hydrogen.Schema.Phone.NationalNumber (toString, length) as NN

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // cursor result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of formatting with cursor position tracking.
-- |
-- | Contains both the formatted string and the new cursor position,
-- | allowing UI components to maintain proper cursor placement.
newtype CursorResult = CursorResult
  { formatted :: String
  , cursor :: Int
  }

derive instance eqCursorResult :: Eq CursorResult

instance showCursorResult :: Show CursorResult where
  show (CursorResult r) = "CursorResult { formatted: " <> show r.formatted 
    <> ", cursor: " <> show r.cursor <> " }"

-- | Get the formatted value from a cursor result.
formattedValue :: CursorResult -> String
formattedValue (CursorResult r) = r.formatted

-- | Get the cursor position from a cursor result.
cursorPosition :: CursorResult -> Int
cursorPosition (CursorResult r) = r.cursor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format a national number using the country's format pattern.
-- |
-- | Example:
-- | ```
-- | format usCountry (nationalNumber "5551234567")
-- | -- Returns: "(555) 123-4567"
-- | ```
format :: Country -> NationalNumber -> String
format country nn = formatWithPattern (formatPattern country) nn

-- | Format a national number with a specific pattern.
-- |
-- | Replaces `#` placeholders in the pattern with digits from the number.
-- | Stops when either digits or placeholders run out.
formatWithPattern :: FormatPattern -> NationalNumber -> String
formatWithPattern pattern nn =
  let patternStr = patternToString pattern
      digits = String.toCharArray (NN.toString nn)
  in String.fromCharArray (applyPattern (String.toCharArray patternStr) digits)

-- | Format partially — for use during typing.
-- |
-- | Like format, but doesn't require the number to fill all placeholders.
-- | Trailing literals after the last digit are trimmed.
formatPartial :: FormatPattern -> NationalNumber -> String
formatPartial pattern nn =
  let patternStr = patternToString pattern
      digits = String.toCharArray (NN.toString nn)
      formatted = applyPatternPartial (String.toCharArray patternStr) digits
  in String.fromCharArray (trimTrailingLiterals formatted)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // cursor handling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format a number and calculate the new cursor position.
-- |
-- | Given the input cursor position (in the unformatted digits), returns
-- | both the formatted string and where the cursor should be placed.
-- |
-- | This is the primary function for format-as-you-type implementations.
formatWithCursor :: FormatPattern -> NationalNumber -> Int -> CursorResult
formatWithCursor pattern nn cursorInDigits =
  let formatted = formatPartial pattern nn
      newCursor = digitIndexToPosition pattern cursorInDigits
  in CursorResult { formatted: formatted, cursor: newCursor }

-- | Calculate cursor position after formatting.
-- |
-- | Maps a position in the raw digits to a position in the formatted string.
-- | Accounts for literal characters that are inserted during formatting.
calculateCursorAfterFormat :: FormatPattern -> Int -> Int
calculateCursorAfterFormat pattern digitIndex = 
  digitIndexToPosition pattern digitIndex

-- | Calculate cursor position after a delete operation.
-- |
-- | When the user deletes a character, we need to figure out where the
-- | cursor should land. If they deleted a literal, move to the previous digit.
-- |
-- | Uses the pattern structure and current formatted string length to
-- | determine proper cursor placement.
calculateCursorAfterDelete :: FormatPattern -> String -> Int -> Int
calculateCursorAfterDelete pattern currentFormatted cursorPos =
  let patternChars = String.toCharArray (patternToString pattern)
      formattedLen = String.length currentFormatted
      patternLen = Array.length patternChars
      -- Clamp cursor to valid range
      clampedCursor = if cursorPos > formattedLen then formattedLen else cursorPos
      -- Find the digit index at or before cursor position
      digitIdx = positionToDigitIndex pattern (clampedCursor - 1)
  in case digitIdx of
       Nothing -> 
         -- If no digit before cursor, and pattern has digits, go to first digit position
         if patternLen > 0 then 0 else 0
       Just idx -> digitIndexToPosition pattern idx

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // unformatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Remove formatting and extract just the digits.
-- |
-- | Example:
-- | ```
-- | unformat "(555) 123-4567" -- Returns: "5551234567"
-- | ```
unformat :: String -> String
unformat = extractDigits

-- | Extract only digit characters from a string.
extractDigits :: String -> String
extractDigits s = 
  String.fromCharArray $ Array.filter isDigit $ String.toCharArray s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // pattern analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all positions in the formatted string that contain digits.
-- |
-- | Returns 0-based indices of digit positions.
digitPositions :: FormatPattern -> Array Int
digitPositions pattern =
  let chars = String.toCharArray (patternToString pattern)
      indexed = Array.mapWithIndex Tuple chars
  in map fst $ Array.filter (\t -> snd t == '#') indexed

-- | Get all positions in the formatted string that contain literal characters.
literalPositions :: FormatPattern -> Array Int
literalPositions pattern =
  let chars = String.toCharArray (patternToString pattern)
      indexed = Array.mapWithIndex Tuple chars
  in map fst $ Array.filter (\t -> snd t /= '#') indexed

-- | Check if a position in the formatted string is a digit position.
isDigitPosition :: FormatPattern -> Int -> Boolean
isDigitPosition pattern pos =
  let chars = String.toCharArray (patternToString pattern)
  in case Array.index chars pos of
       Just '#' -> true
       _ -> false

-- | Convert a position in the formatted string to a digit index.
-- |
-- | Returns Nothing if the position is not a digit position or out of bounds.
positionToDigitIndex :: FormatPattern -> Int -> Maybe Int
positionToDigitIndex pattern pos =
  let chars = String.toCharArray (patternToString pattern)
      -- Count how many '#' characters appear before or at this position
      beforeAndAt = Array.take (pos + 1) chars
      digitCount = Array.length $ Array.filter (\c -> c == '#') beforeAndAt
  in if pos < 0 then Nothing
     else if pos >= Array.length chars then Nothing
     else if digitCount > 0 then Just (digitCount - 1)
     else Nothing

-- | Convert a digit index to a position in the formatted string.
-- |
-- | Given the index of a digit (0-based), returns where it appears
-- | in the formatted output. Uses the pattern character array length
-- | as a fallback for extrapolation beyond the pattern bounds.
digitIndexToPosition :: FormatPattern -> Int -> Int
digitIndexToPosition pattern digitIdx =
  let chars = String.toCharArray (patternToString pattern)
      patternLen = Array.length chars
      positions = digitPositions pattern
  in case Array.index positions digitIdx of
       Just pos -> pos + 1  -- Position after the digit
       Nothing -> 
         -- If digit index is beyond pattern, extrapolate from pattern end
         case Array.index positions (Array.length positions - 1) of
           Just lastPos -> lastPos + 1 + (digitIdx - Array.length positions + 1)
           Nothing -> 
             -- No positions at all, use pattern length as guide
             if patternLen > 0 then patternLen else digitIdx

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a format pattern to digits.
-- |
-- | Walks through pattern, replacing '#' with digits.
-- | Stops when either pattern or digits are exhausted.
applyPattern :: Array Char -> Array Char -> Array Char
applyPattern patternChars digits =
  let result = foldl applyChar { output: [], remaining: digits } patternChars
  in result.output

-- | State for pattern application fold.
type ApplyState =
  { output :: Array Char
  , remaining :: Array Char
  }

-- | Apply a single pattern character.
applyChar :: ApplyState -> Char -> ApplyState
applyChar state c =
  if c == '#' then
    -- This is a digit placeholder
    case arrayUncons state.remaining of
      Just { head: digit, tail: rest } ->
        { output: state.output <> [digit], remaining: rest }
      Nothing ->
        -- No more digits, stop here
        state
  else
    -- This is a literal character
    case arrayUncons state.remaining of
      Just _ ->
        -- Still have digits to place, include the literal
        { output: state.output <> [c], remaining: state.remaining }
      Nothing ->
        -- No more digits, don't add trailing literals
        state

-- | Apply pattern for partial input (during typing).
applyPatternPartial :: Array Char -> Array Char -> Array Char
applyPatternPartial patternChars digits =
  let result = foldl applyCharPartial { output: [], remaining: digits, lastWasDigit: false } patternChars
  in result.output

-- | State for partial pattern application.
type ApplyPartialState =
  { output :: Array Char
  , remaining :: Array Char
  , lastWasDigit :: Boolean
  }

-- | Apply a single pattern character for partial formatting.
applyCharPartial :: ApplyPartialState -> Char -> ApplyPartialState
applyCharPartial state c =
  if c == '#' then
    case arrayUncons state.remaining of
      Just { head: digit, tail: rest } ->
        { output: state.output <> [digit], remaining: rest, lastWasDigit: true }
      Nothing ->
        { output: state.output, remaining: [], lastWasDigit: false }
  else
    case arrayUncons state.remaining of
      Just _ ->
        { output: state.output <> [c], remaining: state.remaining, lastWasDigit: false }
      Nothing ->
        { output: state.output, remaining: [], lastWasDigit: false }

-- | Trim trailing literal characters (non-digits) from formatted output.
trimTrailingLiterals :: Array Char -> Array Char
trimTrailingLiterals chars =
  let reversed = arrayReverse chars
      trimmed = dropWhileNotDigit reversed
  in arrayReverse trimmed

-- | Drop characters while they are not digits.
dropWhileNotDigit :: Array Char -> Array Char
dropWhileNotDigit arr = case arrayUncons arr of
  Nothing -> []
  Just { head: c, tail: rest } ->
    if isDigit c then arr
    else dropWhileNotDigit rest

-- | Check if a character is a digit.
isDigit :: Char -> Boolean
isDigit c = c >= '0' && c <= '9'

-- | Safe uncons for arrays (head + tail).
arrayUncons :: forall a. Array a -> Maybe { head :: a, tail :: Array a }
arrayUncons arr = case Array.index arr 0 of
  Nothing -> Nothing
  Just h -> Just { head: h, tail: arrayDrop 1 arr }

-- | Drop first n elements from array.
arrayDrop :: forall a. Int -> Array a -> Array a
arrayDrop n arr = Array.drop n arr

-- | Reverse an array.
arrayReverse :: forall a. Array a -> Array a
arrayReverse = Array.reverse

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // pattern utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Count the number of digit placeholders in a pattern.
-- |
-- | This tells you the maximum number of digits the pattern can display.
patternDigitCount :: FormatPattern -> Int
patternDigitCount pattern =
  let chars = String.toCharArray (patternToString pattern)
  in Array.length $ Array.filter (\c -> c == '#') chars

-- | Get the length of a national number's digit string.
nationalNumberLength :: NationalNumber -> Int
nationalNumberLength nn = NN.length nn

-- | Find the position of the first digit placeholder in a pattern.
-- |
-- | Useful for positioning cursor at the start of phone input.
-- | Returns 0 if no digit placeholder found.
findFirstDigitPosition :: FormatPattern -> Int
findFirstDigitPosition pattern =
  let chars = String.toCharArray (patternToString pattern)
  in case Array.findIndex (\c -> c == '#') chars of
       Just pos -> pos
       Nothing -> 0

-- | Append a digit character to a formatted phone number.
-- |
-- | Extracts current digits, adds the new one, and reformats.
-- | Returns the new formatted string.
appendDigit :: FormatPattern -> String -> Char -> String
appendDigit pattern currentFormatted digit =
  if isDigit digit then
    let currentDigits = String.toCharArray (extractDigits currentFormatted)
        newDigits = Array.snoc currentDigits digit
    in String.fromCharArray (applyPatternPartial (String.toCharArray (patternToString pattern)) newDigits)
  else
    currentFormatted

-- | Format a phone number, returning a default if the number is empty.
-- |
-- | Useful for displaying placeholder text when no digits entered.
formatOrDefault :: FormatPattern -> NationalNumber -> String -> String
formatOrDefault pattern nn defaultValue =
  let formatted = formatPartial pattern nn
  in fromMaybe defaultValue (if formatted == "" then Nothing else Just formatted)
