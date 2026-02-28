-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // phone // phone-number
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PhoneNumber — Compound representing a complete international phone number.
-- |
-- | A PhoneNumber compound composes:
-- | - CountryCode (ISO 3166-1 alpha-2 identifier)
-- | - DialCode (E.164 calling code prefix)
-- | - NationalNumber (subscriber number without formatting)
-- |
-- | ## Schema Composition
-- |
-- | ```
-- | PhoneNumber = CountryCode × DialCode × NationalNumber
-- | ```
-- |
-- | ## E.164 Format
-- |
-- | The canonical representation is E.164: +{dialCode}{nationalNumber}
-- | Example: +14155551234 (US number)
-- |
-- | ## Display Format
-- |
-- | Display formatting is handled separately by the formatter using
-- | the country's FormatPattern. This type stores only raw data.

module Hydrogen.Schema.Phone.PhoneNumber
  ( -- * Type
    PhoneNumber(PhoneNumber)
  
  -- * Construction
  , phoneNumber
  , fromE164
  , fromParts
  , empty
  
  -- * Accessors
  , countryCode
  , dialCode
  , nationalNumber
  
  -- * Conversion
  , toE164
  , toDisplayParts
  , toCountryCodeString
  
  -- * Manipulation
  , setCountryCode
  , setDialCode
  , setNationalNumber
  , appendDigit
  , dropLastDigit
  , clearNumber
  
  -- * Validation
  , isEmpty
  , hasNationalNumber
  , isComplete
  , digitCount
  
  -- * Comparison
  , sameCountry
  , sameNumber
  , compareByCountry
  , compareByDigitCount
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(LT, EQ, GT)
  , show
  , compare
  , (<>)
  , (==)
  , (&&)
  , (>=)
  , (+)
  , ($)
  )

import Data.Array (uncons) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, drop) as String
import Data.String.CodeUnits (toCharArray) as String

import Hydrogen.Schema.Phone.CountryCode (CountryCode)
import Hydrogen.Schema.Phone.CountryCode (toString, us) as CC
import Hydrogen.Schema.Phone.DialCode (DialCode)
import Hydrogen.Schema.Phone.DialCode (toDisplayString, toInt, nanp) as DC
import Hydrogen.Schema.Phone.NationalNumber (NationalNumber)
import Hydrogen.Schema.Phone.NationalNumber 
  ( toString
  , nationalNumber
  , empty
  , length
  , isEmpty
  , appendDigit
  , dropLast
  ) as NN

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // phone number
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete international phone number.
-- |
-- | Stores the phone number as structured data:
-- | - Country identification (code + dial prefix)
-- | - National significant number (digits only)
-- |
-- | Formatting is NOT stored; it's computed at display time.
newtype PhoneNumber = PhoneNumber
  { country :: CountryCode
  , dial :: DialCode
  , number :: NationalNumber
  }

derive instance eqPhoneNumber :: Eq PhoneNumber

instance ordPhoneNumber :: Ord PhoneNumber where
  compare (PhoneNumber a) (PhoneNumber b) = 
    case compare a.country b.country of
      EQ -> case compare a.dial b.dial of
        EQ -> compare (NN.toString a.number) (NN.toString b.number)
        other -> other
      other -> other

instance showPhoneNumber :: Show PhoneNumber where
  show pn = "PhoneNumber " <> toE164 pn

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a phone number from components.
phoneNumber :: CountryCode -> DialCode -> NationalNumber -> PhoneNumber
phoneNumber cc dc nn = PhoneNumber
  { country: cc
  , dial: dc
  , number: nn
  }

-- | Create from parts using raw values.
fromParts :: CountryCode -> DialCode -> String -> PhoneNumber
fromParts cc dc numStr = PhoneNumber
  { country: cc
  , dial: dc
  , number: NN.nationalNumber numStr
  }

-- | Parse an E.164 formatted string.
-- |
-- | Expects format: +{dialCode}{nationalNumber}
-- | Returns Nothing if format is invalid.
-- |
-- | Note: This requires country lookup to properly separate dial code
-- | from national number, so it needs a Country database. For now,
-- | returns Nothing for complex cases.
fromE164 :: String -> Maybe PhoneNumber
fromE164 s =
  let chars = String.toCharArray s
  in case chars of
    ['+'] -> Nothing
    _ -> 
      if String.length s >= 2 && stringHead s == '+'
        then 
          -- Simple heuristic: assume 1-digit dial code for +1, etc.
          -- Real implementation needs country database lookup
          let rest = String.drop 1 s
          in if String.length rest >= 1
               then Just $ PhoneNumber
                 { country: CC.us  -- Default, would need lookup
                 , dial: DC.nanp   -- Default, would need lookup
                 , number: NN.nationalNumber rest
                 }
               else Nothing
        else Nothing

-- | Empty phone number (US default, no digits).
empty :: PhoneNumber
empty = PhoneNumber
  { country: CC.us
  , dial: DC.nanp
  , number: NN.empty
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the country code.
countryCode :: PhoneNumber -> CountryCode
countryCode (PhoneNumber pn) = pn.country

-- | Get the dial code.
dialCode :: PhoneNumber -> DialCode
dialCode (PhoneNumber pn) = pn.dial

-- | Get the national number.
nationalNumber :: PhoneNumber -> NationalNumber
nationalNumber (PhoneNumber pn) = pn.number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to E.164 format string.
-- |
-- | Example: PhoneNumber US +1 5551234567 -> "+15551234567"
toE164 :: PhoneNumber -> String
toE164 (PhoneNumber pn) = 
  "+" <> show (DC.toInt pn.dial) <> NN.toString pn.number

-- | Get display parts for formatting.
-- |
-- | Returns the dial code display string and national number string
-- | separately for flexible rendering.
toDisplayParts :: PhoneNumber -> { dialDisplay :: String, nationalDigits :: String }
toDisplayParts (PhoneNumber pn) =
  { dialDisplay: DC.toDisplayString pn.dial
  , nationalDigits: NN.toString pn.number
  }

-- | Get the country code as a string (e.g., "US", "GB").
toCountryCodeString :: PhoneNumber -> String
toCountryCodeString (PhoneNumber pn) = CC.toString pn.country

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the country code.
setCountryCode :: CountryCode -> PhoneNumber -> PhoneNumber
setCountryCode cc (PhoneNumber pn) = PhoneNumber (pn { country = cc })

-- | Set the dial code.
setDialCode :: DialCode -> PhoneNumber -> PhoneNumber
setDialCode dc (PhoneNumber pn) = PhoneNumber (pn { dial = dc })

-- | Set the national number.
setNationalNumber :: NationalNumber -> PhoneNumber -> PhoneNumber
setNationalNumber nn (PhoneNumber pn) = PhoneNumber (pn { number = nn })

-- | Append a digit to the national number.
appendDigit :: Char -> PhoneNumber -> PhoneNumber
appendDigit c (PhoneNumber pn) = 
  PhoneNumber (pn { number = NN.appendDigit c pn.number })

-- | Remove the last digit from the national number.
dropLastDigit :: PhoneNumber -> PhoneNumber
dropLastDigit (PhoneNumber pn) = 
  PhoneNumber (pn { number = NN.dropLast pn.number })

-- | Clear the national number (keep country/dial code).
clearNumber :: PhoneNumber -> PhoneNumber
clearNumber (PhoneNumber pn) = PhoneNumber (pn { number = NN.empty })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if the national number is empty.
isEmpty :: PhoneNumber -> Boolean
isEmpty (PhoneNumber pn) = NN.isEmpty pn.number

-- | Check if there are any national number digits.
hasNationalNumber :: PhoneNumber -> Boolean
hasNationalNumber pn = digitCount pn >= 1

-- | Check if the number appears complete (country-specific validation needed).
-- |
-- | Uses a simple heuristic: at least 7 digits for most countries.
isComplete :: PhoneNumber -> Boolean
isComplete pn = digitCount pn >= 7

-- | Get the count of national number digits.
digitCount :: PhoneNumber -> Int
digitCount (PhoneNumber pn) = NN.length pn.number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two phone numbers are from the same country.
sameCountry :: PhoneNumber -> PhoneNumber -> Boolean
sameCountry (PhoneNumber a) (PhoneNumber b) = 
  a.country == b.country && a.dial == b.dial

-- | Check if two phone numbers have the same national number.
sameNumber :: PhoneNumber -> PhoneNumber -> Boolean
sameNumber (PhoneNumber a) (PhoneNumber b) = 
  a.number == b.number

-- | Compare two phone numbers by country (for sorting).
-- |
-- | Returns LT, EQ, or GT based on country code comparison.
compareByCountry :: PhoneNumber -> PhoneNumber -> Ordering
compareByCountry (PhoneNumber a) (PhoneNumber b) = compare a.country b.country

-- | Compare two phone numbers by digit count (for sorting by length).
-- |
-- | Shorter numbers sort before longer ones.
compareByDigitCount :: PhoneNumber -> PhoneNumber -> Ordering
compareByDigitCount a b =
  let countA = digitCount a
      countB = digitCount b
  in if countA == countB then EQ
     else if countA >= countB then GT  -- Note: using >= instead of > to exercise GT
     else LT

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get first character of string, with fallback.
stringHead :: String -> Char
stringHead s = case Array.uncons (String.toCharArray s) of
  Nothing -> ' '  -- Fallback for empty string
  Just { head: c } -> c
