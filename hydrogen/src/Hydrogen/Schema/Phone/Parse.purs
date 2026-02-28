-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // phone // parse
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Phone number parsing engine.
-- |
-- | Provides intelligent parsing of phone numbers from various input formats:
-- | - Paste detection (E.164, national, formatted)
-- | - Country auto-detection from dial code
-- | - Input normalization
-- |
-- | ## Parsing Strategy
-- |
-- | 1. Extract digits from input
-- | 2. Detect if input starts with '+' (international format)
-- | 3. Try to match dial codes to identify country
-- | 4. Return parsed result with detected country and national number

module Hydrogen.Schema.Phone.Parse
  ( -- * Parse Result
    ParseResult
  , parseResult
  , parsedCountry
  , parsedNational
  , parseConfidence
  , isSuccessfulParse
  
  -- * Confidence Levels
  , Confidence
      ( High
      , Medium
      , Low
      , None
      )
  , confidenceToInt
  
  -- * Parsing Functions
  , parse
  , parseWithHint
  , parseE164
  , parseNational
  
  -- * Detection
  , detectCountry
  , detectCountryFromDialCode
  , detectCountryFromNumber
  , extractDialCode
  , hasInternationalPrefix
  
  -- * Normalization
  , normalize
  , stripInternationalPrefix
  , stripTrunkPrefix
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
  , map
  , (<>)
  , (==)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (+)
  , (-)
  , (*)
  , ($)
  , (&&)
  , (||)
  )

import Data.Array (filter, find, head, length) as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing), isJust)
import Data.String (take, drop) as String
import Data.String.CodeUnits (toCharArray, fromCharArray, charAt) as String

import Hydrogen.Schema.Phone.Country (Country)
import Hydrogen.Schema.Phone.Country (dialCode, name) as Country
import Hydrogen.Schema.Phone.DialCode (toInt) as DC
import Hydrogen.Schema.Phone.NationalNumber (NationalNumber)
import Hydrogen.Schema.Phone.NationalNumber (nationalNumber) as NN

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // confidence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Confidence level of a parse result.
-- |
-- | Indicates how certain we are about the parsed result.
data Confidence
  = High    -- ^ E.164 format or explicit dial code match
  | Medium  -- ^ Likely match based on number length/format
  | Low     -- ^ Ambiguous, multiple possible countries
  | None    -- ^ Could not determine country

derive instance eqConfidence :: Eq Confidence

instance ordConfidence :: Ord Confidence where
  compare a b = compare (confidenceToInt a) (confidenceToInt b)

instance showConfidence :: Show Confidence where
  show High = "High"
  show Medium = "Medium"
  show Low = "Low"
  show None = "None"

-- | Convert confidence to numeric value for comparison.
confidenceToInt :: Confidence -> Int
confidenceToInt c = case c of
  High -> 3
  Medium -> 2
  Low -> 1
  None -> 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // parse result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of parsing a phone number.
-- |
-- | Contains the detected country (if any), the national number portion,
-- | and the confidence level of the detection.
newtype ParseResult = ParseResult
  { country :: Maybe Country
  , national :: NationalNumber
  , confidence :: Confidence
  , originalInput :: String
  }

derive instance eqParseResult :: Eq ParseResult

instance showParseResult :: Show ParseResult where
  show (ParseResult r) = "ParseResult { "
    <> "country: " <> show (map Country.name r.country)
    <> ", national: " <> show r.national
    <> ", confidence: " <> show r.confidence
    <> " }"

-- | Create a parse result.
parseResult :: Maybe Country -> NationalNumber -> Confidence -> String -> ParseResult
parseResult country national confidence original = ParseResult
  { country: country
  , national: national
  , confidence: confidence
  , originalInput: original
  }

-- | Get the parsed country.
parsedCountry :: ParseResult -> Maybe Country
parsedCountry (ParseResult r) = r.country

-- | Get the parsed national number.
parsedNational :: ParseResult -> NationalNumber
parsedNational (ParseResult r) = r.national

-- | Get the parse confidence.
parseConfidence :: ParseResult -> Confidence
parseConfidence (ParseResult r) = r.confidence

-- | Check if parsing was successful (has a country match).
isSuccessfulParse :: ParseResult -> Boolean
isSuccessfulParse (ParseResult r) = isJust r.country && r.confidence > None

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // parsing functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parse a phone number string, attempting to detect the country.
-- |
-- | Accepts various formats:
-- | - E.164: "+14155551234"
-- | - International: "+1 (415) 555-1234"
-- | - National with leading zero: "0415 555 1234"
-- | - Raw digits: "4155551234"
parse :: Array Country -> String -> ParseResult
parse countries input =
  let normalized = normalize input
      hasPlus = hasInternationalPrefix input
  in if hasPlus
       then parseE164 countries normalized
       else parseNational countries normalized

-- | Parse with a country hint (preferred country for ambiguous cases).
-- |
-- | If the number could belong to multiple countries, prefer the hint.
parseWithHint :: Array Country -> Country -> String -> ParseResult
parseWithHint countries hint input =
  let result = parse countries input
  in case parsedCountry result of
       Nothing -> 
         -- No country detected, assume hint country
         parseResult (Just hint) (NN.nationalNumber (normalize input)) Low input
       Just _ -> result

-- | Parse an E.164 formatted number (starts with +).
-- |
-- | Example: "+14155551234" -> Country: US, National: "4155551234"
parseE164 :: Array Country -> String -> ParseResult
parseE164 countries input =
  let digits = extractDigits input
      detected = detectCountryFromDialCode countries digits
  in case detected of
       Just { country, remaining } ->
         parseResult (Just country) (NN.nationalNumber remaining) High input
       Nothing ->
         parseResult Nothing (NN.nationalNumber digits) None input

-- | Parse a national format number (no country code).
-- |
-- | Uses number length and format to guess the country.
parseNational :: Array Country -> String -> ParseResult
parseNational countries input =
  let digits = extractDigits input
      -- Try to detect country from number characteristics
      detected = detectCountryFromNumber countries digits
  in case detected of
       Just country ->
         let national = stripTrunkPrefix digits
         in parseResult (Just country) (NN.nationalNumber national) Medium input
       Nothing ->
         parseResult Nothing (NN.nationalNumber digits) None input

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Detect country from a phone number string.
detectCountry :: Array Country -> String -> Maybe Country
detectCountry countries input =
  let result = parse countries input
  in parsedCountry result

-- | Detect country from dial code prefix.
-- |
-- | Tries dial codes of length 1, 2, 3 (in that order) to find a match.
-- | Returns the matching country and the remaining digits.
detectCountryFromDialCode :: Array Country -> String -> Maybe { country :: Country, remaining :: String }
detectCountryFromDialCode countries digits =
  -- Try longest dial codes first (3 digits), then 2, then 1
  -- This handles cases like +1 (US) vs +1242 (Bahamas)
  let tryLength len =
        let prefix = String.take len digits
            remaining = String.drop len digits
            prefixInt = stringToInt prefix
        in case prefixInt of
             Nothing -> Nothing
             Just code ->
               case findCountryByDialCode countries code of
                 Just c -> Just { country: c, remaining: remaining }
                 Nothing -> Nothing
      -- Get unique dial code lengths to try (longest first)
      lengths = [3, 2, 1]
  in foldl (\acc len -> case acc of
              Just r -> Just r
              Nothing -> tryLength len
           ) Nothing lengths

-- | Detect country from number characteristics (length, format).
-- |
-- | This is a heuristic approach for national format numbers.
detectCountryFromNumber :: Array Country -> String -> Maybe Country
detectCountryFromNumber _countries _digits =
  -- For now, return Nothing - proper implementation would use
  -- number length rules per country
  Nothing

-- | Extract dial code from digits.
-- |
-- | Returns the dial code portion (1-3 digits) if detected.
extractDialCode :: Array Country -> String -> Maybe Int
extractDialCode countries digits =
  case detectCountryFromDialCode countries digits of
    Just { country } -> Just (DC.toInt (Country.dialCode country))
    Nothing -> Nothing

-- | Check if input starts with international prefix (+ or 00).
hasInternationalPrefix :: String -> Boolean
hasInternationalPrefix s =
  case String.charAt 0 s of
    Just '+' -> true
    Just '0' -> 
      case String.charAt 1 s of
        Just '0' -> true  -- "00" prefix (common in Europe)
        _ -> false
    _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // normalization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalize a phone number input.
-- |
-- | - Removes all non-digit characters except leading +
-- | - Converts "00" prefix to "+"
normalize :: String -> String
normalize input =
  let chars = String.toCharArray input
      -- Check for leading + or 00
      hasPlus = case Array.head chars of
                  Just '+' -> true
                  _ -> false
      hasDoubleZero = String.take 2 input == "00"
      -- Extract digits
      digits = extractDigits input
      -- Handle 00 prefix by removing the leading zeros
      finalDigits = if hasDoubleZero 
                      then String.drop 2 digits
                      else digits
  in if hasPlus || hasDoubleZero
       then "+" <> finalDigits
       else digits

-- | Strip international prefix (+ or 00) from input.
stripInternationalPrefix :: String -> String
stripInternationalPrefix s =
  if hasInternationalPrefix s
    then case String.charAt 0 s of
           Just '+' -> String.drop 1 s
           _ -> String.drop 2 s  -- "00" prefix
    else s

-- | Strip trunk prefix (leading 0) common in national format.
-- |
-- | Many countries use "0" as a trunk prefix for national dialing.
-- | Example: "0412345678" -> "412345678"
stripTrunkPrefix :: String -> String
stripTrunkPrefix s =
  case String.charAt 0 s of
    Just '0' -> String.drop 1 s
    _ -> s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract only digit characters from a string.
extractDigits :: String -> String
extractDigits s = 
  String.fromCharArray $ Array.filter isDigit $ String.toCharArray s

-- | Check if a character is a digit.
isDigit :: Char -> Boolean
isDigit c = c >= '0' && c <= '9'

-- | Find a country by its dial code.
findCountryByDialCode :: Array Country -> Int -> Maybe Country
findCountryByDialCode countries code =
  Array.find (\c -> DC.toInt (Country.dialCode c) == code) countries

-- | Convert a string of digits to an integer.
-- |
-- | Returns Nothing if the string is empty or contains non-digits.
stringToInt :: String -> Maybe Int
stringToInt s =
  let chars = String.toCharArray s
  in if Array.length chars == 0
       then Nothing
       else foldl accumDigit (Just 0) chars

-- | Accumulate digits into an integer.
accumDigit :: Maybe Int -> Char -> Maybe Int
accumDigit acc c =
  case acc of
    Nothing -> Nothing
    Just n ->
      case charToDigit c of
        Nothing -> Nothing
        Just d -> Just (n * 10 + d)

-- | Convert a character to its digit value.
charToDigit :: Char -> Maybe Int
charToDigit c =
  if c == '0' then Just 0
  else if c == '1' then Just 1
  else if c == '2' then Just 2
  else if c == '3' then Just 3
  else if c == '4' then Just 4
  else if c == '5' then Just 5
  else if c == '6' then Just 6
  else if c == '7' then Just 7
  else if c == '8' then Just 8
  else if c == '9' then Just 9
  else Nothing
