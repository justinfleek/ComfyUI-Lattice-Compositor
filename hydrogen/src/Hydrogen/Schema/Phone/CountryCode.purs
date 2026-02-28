-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // phone // country-code
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CountryCode — ISO 3166-1 alpha-2 country code atom.
-- |
-- | A bounded string type representing exactly 2 uppercase ASCII letters.
-- | Examples: "US", "GB", "DE", "JP", "AU"
-- |
-- | ## Bounds
-- |
-- | - Length: exactly 2 characters
-- | - Characters: A-Z only (uppercase ASCII letters)
-- | - Total possible values: 26² = 676
-- |
-- | ## E.164 Compliance
-- |
-- | Country codes are used with dial codes to form internationally 
-- | recognizable phone number prefixes. The ISO 3166-1 alpha-2 standard
-- | is the de facto standard for phone number country identification.

module Hydrogen.Schema.Phone.CountryCode
  ( -- * Type
    CountryCode
  
  -- * Construction
  , countryCode
  , unsafeCountryCode
  
  -- * Accessors
  , toString
  , toUpper
  
  -- * Validation
  , isValid
  , validate
  
  -- * Common Codes
  , us
  , gb
  , ca
  , au
  , de
  , fr
  , jp
  , cn
  , in_
  , br
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
  , (==)
  , (&&)
  , (>=)
  , (<=)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, toUpper) as String
import Data.String.CodeUnits (toCharArray) as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // country code
-- ═════════════════════════════════════════════════════════════════════════════

-- | ISO 3166-1 alpha-2 country code.
-- |
-- | Exactly 2 uppercase ASCII letters identifying a country or territory.
-- | Validated at construction time - invalid inputs return Nothing.
newtype CountryCode = CountryCode String

derive instance eqCountryCode :: Eq CountryCode

instance ordCountryCode :: Ord CountryCode where
  compare (CountryCode a) (CountryCode b) = compare a b

instance showCountryCode :: Show CountryCode where
  show (CountryCode s) = "CountryCode " <> show s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a country code from a string (validates and normalizes to uppercase).
-- |
-- | Returns Nothing if:
-- | - Length is not exactly 2
-- | - Contains non-letter characters
countryCode :: String -> Maybe CountryCode
countryCode s =
  let normalized = String.toUpper s
  in if isValidCode normalized
       then Just (CountryCode normalized)
       else Nothing

-- | Create a country code without validation.
-- |
-- | Use only for known-valid codes (e.g., from database constants).
-- | Normalizes to uppercase.
unsafeCountryCode :: String -> CountryCode
unsafeCountryCode s = CountryCode (String.toUpper s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the string representation.
toString :: CountryCode -> String
toString (CountryCode s) = s

-- | Get uppercase string (identity since always stored uppercase).
toUpper :: CountryCode -> String
toUpper (CountryCode s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a string is a valid country code format.
isValid :: String -> Boolean
isValid s = isValidCode (String.toUpper s)

-- | Validate and return the normalized code or Nothing.
validate :: String -> Maybe CountryCode
validate = countryCode

-- | Internal validation for already-uppercase strings.
isValidCode :: String -> Boolean
isValidCode s =
  String.length s == 2 && allUpperAlpha (String.toCharArray s)

-- | Check if all characters are uppercase ASCII letters (A-Z).
allUpperAlpha :: Array Char -> Boolean
allUpperAlpha chars = case chars of
  [c1, c2] -> isUpperAlpha c1 && isUpperAlpha c2
  _ -> false

-- | Check if a character is an uppercase ASCII letter.
isUpperAlpha :: Char -> Boolean
isUpperAlpha c = c >= 'A' && c <= 'Z'

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // common codes
-- ═════════════════════════════════════════════════════════════════════════════

-- | United States
us :: CountryCode
us = CountryCode "US"

-- | United Kingdom
gb :: CountryCode
gb = CountryCode "GB"

-- | Canada
ca :: CountryCode
ca = CountryCode "CA"

-- | Australia
au :: CountryCode
au = CountryCode "AU"

-- | Germany
de :: CountryCode
de = CountryCode "DE"

-- | France
fr :: CountryCode
fr = CountryCode "FR"

-- | Japan
jp :: CountryCode
jp = CountryCode "JP"

-- | China
cn :: CountryCode
cn = CountryCode "CN"

-- | India (underscore to avoid reserved word)
in_ :: CountryCode
in_ = CountryCode "IN"

-- | Brazil
br :: CountryCode
br = CountryCode "BR"
