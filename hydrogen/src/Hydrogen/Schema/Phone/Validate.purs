-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // phone // validate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Phone number validation engine.
-- |
-- | Provides comprehensive validation for phone numbers based on:
-- | - E.164 specification (max 15 digits total)
-- | - Country-specific rules (min/max national number length)
-- | - Format pattern matching
-- |
-- | ## Validation Levels
-- |
-- | 1. **Structural** — Basic digit count and format
-- | 2. **Country-specific** — Length rules per country
-- | 3. **Pattern** — Matches expected format pattern
-- |
-- | ## Pure Implementation
-- |
-- | All validation is pure data transformation — no FFI, no regex libraries.
-- | Pattern matching is done with simple string operations.

module Hydrogen.Schema.Phone.Validate
  ( -- * Validation Result
    ValidationResult
      ( Valid
      , Invalid
      )
  , validationErrors
  , isValid
  , isInvalid
  
  -- * Validation Errors
  , ValidationError
      ( TooShort
      , TooLong
      , InvalidCharacters
      , MissingCountry
      , IncompleteNumber
      )
  , errorMessage
  , errorCode
  
  -- * Validation Functions
  , validate
  , validateStrict
  , validateWithCountry
  , validateE164
  
  -- * Individual Checks
  , checkMinLength
  , checkMaxLength
  , checkDigitsOnly
  , checkCountryLength
  
  -- * Length Rules
  , LengthRule
  , lengthRule
  , minDigits
  , maxDigits
  , defaultLengthRule
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (<<<)
  , (==)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , ($)
  , (&&)
  , (-)
  , not
  )

import Data.Array (filter, null, uncons, drop, length, catMaybes) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String.CodeUnits (toCharArray) as String

import Hydrogen.Schema.Phone.Country (Country)
import Hydrogen.Schema.Phone.Country (countFormatSlots, formatPattern) as Country
import Hydrogen.Schema.Phone.NationalNumber (NationalNumber)
import Hydrogen.Schema.Phone.NationalNumber (length, toString) as NN

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // validation error
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validation error types.
-- |
-- | Each error has a code and human-readable message.
data ValidationError
  = TooShort Int Int        -- ^ (actual, minimum)
  | TooLong Int Int         -- ^ (actual, maximum)
  | InvalidCharacters       -- ^ Non-digit characters found
  | MissingCountry          -- ^ No country selected
  | IncompleteNumber Int Int -- ^ (actual, expected)

derive instance eqValidationError :: Eq ValidationError

instance showValidationError :: Show ValidationError where
  show err = errorMessage err

-- | Get human-readable error message.
errorMessage :: ValidationError -> String
errorMessage err = case err of
  TooShort actual minLen ->
    "Phone number is too short (" <> show actual <> " digits, minimum " <> show minLen <> ")"
  TooLong actual maxLen ->
    "Phone number is too long (" <> show actual <> " digits, maximum " <> show maxLen <> ")"
  InvalidCharacters ->
    "Phone number contains invalid characters"
  MissingCountry ->
    "Please select a country"
  IncompleteNumber actual expected ->
    "Phone number is incomplete (" <> show actual <> " of " <> show expected <> " digits)"

-- | Get error code for programmatic handling.
errorCode :: ValidationError -> String
errorCode err = case err of
  TooShort _ _ -> "TOO_SHORT"
  TooLong _ _ -> "TOO_LONG"
  InvalidCharacters -> "INVALID_CHARS"
  MissingCountry -> "MISSING_COUNTRY"
  IncompleteNumber _ _ -> "INCOMPLETE"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // validation result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of validating a phone number.
data ValidationResult
  = Valid
  | Invalid (Array ValidationError)

derive instance eqValidationResult :: Eq ValidationResult

instance showValidationResult :: Show ValidationResult where
  show Valid = "Valid"
  show (Invalid errs) = "Invalid: " <> show errs

-- | Get validation errors (empty array if valid).
validationErrors :: ValidationResult -> Array ValidationError
validationErrors Valid = []
validationErrors (Invalid errs) = errs

-- | Check if validation passed.
isValid :: ValidationResult -> Boolean
isValid Valid = true
isValid (Invalid _) = false

-- | Check if validation failed.
isInvalid :: ValidationResult -> Boolean
isInvalid = not <<< isValid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // length rules
-- ═════════════════════════════════════════════════════════════════════════════

-- | Length validation rule.
-- |
-- | Specifies minimum and maximum digit counts for a phone number.
newtype LengthRule = LengthRule
  { min :: Int
  , max :: Int
  }

derive instance eqLengthRule :: Eq LengthRule

instance showLengthRule :: Show LengthRule where
  show (LengthRule r) = "LengthRule { min: " <> show r.min <> ", max: " <> show r.max <> " }"

-- | Create a length rule.
lengthRule :: Int -> Int -> LengthRule
lengthRule minLen maxLen = LengthRule { min: minLen, max: maxLen }

-- | Get minimum digits from rule.
minDigits :: LengthRule -> Int
minDigits (LengthRule r) = r.min

-- | Get maximum digits from rule.
maxDigits :: LengthRule -> Int
maxDigits (LengthRule r) = r.max

-- | Default length rule (E.164 compliant).
-- |
-- | - Minimum: 4 digits (shortest valid numbers)
-- | - Maximum: 14 digits (E.164 max minus 1 for country code)
defaultLengthRule :: LengthRule
defaultLengthRule = LengthRule { min: 4, max: 14 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // validation functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate a national number with default rules.
-- |
-- | Checks:
-- | - Minimum length (4 digits)
-- | - Maximum length (14 digits)
-- | - Digits only
validate :: NationalNumber -> ValidationResult
validate nn =
  let errors = collectErrors
        [ checkMinLength 4 nn
        , checkMaxLength 14 nn
        , checkDigitsOnly nn
        ]
  in if Array.null errors
       then Valid
       else Invalid errors

-- | Validate with strict country-specific rules.
-- |
-- | Uses the country's format pattern to determine expected length.
validateStrict :: Country -> NationalNumber -> ValidationResult
validateStrict country nn =
  let errors = collectErrors
        [ checkCountryLength country nn
        , checkDigitsOnly nn
        ]
  in if Array.null errors
       then Valid
       else Invalid errors

-- | Validate with a specific country.
-- |
-- | Less strict than validateStrict — allows partial numbers.
validateWithCountry :: Country -> NationalNumber -> ValidationResult
validateWithCountry country nn =
  let maxLen = Country.countFormatSlots (Country.formatPattern country)
      errors = collectErrors
        [ checkMinLength 1 nn  -- Allow partial numbers
        , checkMaxLength maxLen nn
        , checkDigitsOnly nn
        ]
  in if Array.null errors
       then Valid
       else Invalid errors

-- | Validate an E.164 formatted string.
-- |
-- | Checks:
-- | - Starts with +
-- | - Contains only digits after +
-- | - Total length between 2 and 16 characters
validateE164 :: String -> ValidationResult
validateE164 s =
  let chars = String.toCharArray s
      len = Array.length chars
      startsWithPlus = case Array.uncons chars of
        Nothing -> false
        Just { head: c } -> c == '+'
      digitsAfterPlus = Array.filter isDigit (safeTail chars)
      digitCount = Array.length digitsAfterPlus
      allDigits = Array.length digitsAfterPlus == (len - 1)
  in if not startsWithPlus
       then Invalid [ InvalidCharacters ]
       else if not allDigits
         then Invalid [ InvalidCharacters ]
         else if digitCount < 1
           then Invalid [ TooShort digitCount 1 ]
           else if digitCount > 15
             then Invalid [ TooLong digitCount 15 ]
             else Valid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // individual checks
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check minimum length.
checkMinLength :: Int -> NationalNumber -> Maybe ValidationError
checkMinLength minLen nn =
  let len = NN.length nn
  in if len < minLen
       then Just (TooShort len minLen)
       else Nothing

-- | Check maximum length.
checkMaxLength :: Int -> NationalNumber -> Maybe ValidationError
checkMaxLength maxLen nn =
  let len = NN.length nn
  in if len > maxLen
       then Just (TooLong len maxLen)
       else Nothing

-- | Check that string contains only digits.
checkDigitsOnly :: NationalNumber -> Maybe ValidationError
checkDigitsOnly nn =
  let str = NN.toString nn
      chars = String.toCharArray str
      nonDigits = Array.filter (\c -> not (isDigit c)) chars
  in if Array.null nonDigits
       then Nothing
       else Just InvalidCharacters

-- | Check length matches country's expected format.
checkCountryLength :: Country -> NationalNumber -> Maybe ValidationError
checkCountryLength country nn =
  let actual = NN.length nn
      expected = Country.countFormatSlots (Country.formatPattern country)
  in if actual == expected
       then Nothing
       else if actual < expected
         then Just (IncompleteNumber actual expected)
         else Just (TooLong actual expected)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a character is a digit.
isDigit :: Char -> Boolean
isDigit c = c >= '0' && c <= '9'

-- | Collect non-Nothing errors into an array.
collectErrors :: Array (Maybe ValidationError) -> Array ValidationError
collectErrors = Array.catMaybes

-- | Safe tail (returns empty array for empty input).
safeTail :: forall a. Array a -> Array a
safeTail = Array.drop 1
