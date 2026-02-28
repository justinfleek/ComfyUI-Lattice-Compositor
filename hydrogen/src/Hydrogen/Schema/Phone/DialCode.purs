-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // phone // dial-code
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DialCode — International dialing prefix atom.
-- |
-- | A bounded positive integer representing the E.164 country calling code.
-- | Examples: 1 (US/CA), 44 (GB), 49 (DE), 81 (JP), 61 (AU)
-- |
-- | ## Bounds
-- |
-- | - Minimum: 1
-- | - Maximum: 999 (no country code exceeds 3 digits)
-- | - Examples: 1, 7, 20, 27, 30-39, 40-49, 51-58, 60-66, 81-86, 90-98, 211-299, 350-389, 420-429, 500-509, 590-599, 670-679, 680-689, 690-699, 850-859, 870-879, 880-889, 960-999
-- |
-- | ## E.164 Format
-- |
-- | Dial codes are prefixed with "+" in E.164 format: +1, +44, +49

module Hydrogen.Schema.Phone.DialCode
  ( -- * Type
    DialCode
  
  -- * Construction
  , dialCode
  , unsafeDialCode
  
  -- * Accessors
  , toInt
  , toNumber
  , toDisplayString
  , toE164Prefix
  
  -- * Validation
  , isValid
  
  -- * Bounds
  , minDialCode
  , maxDialCode
  
  -- * Common Codes
  , nanp           -- +1 (North American Numbering Plan)
  , uk             -- +44
  , germany        -- +49
  , france         -- +33
  , japan          -- +81
  , china          -- +86
  , india          -- +91
  , australia      -- +61
  , brazil         -- +55
  , russia         -- +7
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
  , (>=)
  , (<=)
  , (&&)
  )

import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // dial code
-- ═════════════════════════════════════════════════════════════════════════════

-- | International dialing prefix (1-999).
-- |
-- | Represents the numeric portion of an E.164 country calling code.
-- | Validated at construction time.
newtype DialCode = DialCode Int

derive instance eqDialCode :: Eq DialCode

instance ordDialCode :: Ord DialCode where
  compare (DialCode a) (DialCode b) = compare a b

instance showDialCode :: Show DialCode where
  show (DialCode n) = "DialCode " <> show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum valid dial code.
minDialCode :: Int
minDialCode = 1

-- | Maximum valid dial code.
maxDialCode :: Int
maxDialCode = 999

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a dial code from an integer.
-- |
-- | Returns Nothing if outside valid range (1-999).
dialCode :: Int -> Maybe DialCode
dialCode n =
  if isValid n
    then Just (DialCode n)
    else Nothing

-- | Create a dial code without validation.
-- |
-- | Use only for known-valid codes. Clamps to valid range.
unsafeDialCode :: Int -> DialCode
unsafeDialCode n = DialCode (clamp minDialCode maxDialCode n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the integer value.
toInt :: DialCode -> Int
toInt (DialCode n) = n

-- | Get as Number for calculations.
toNumber :: DialCode -> Number
toNumber (DialCode n) = Int.toNumber n

-- | Get display string (e.g., "+1", "+44").
toDisplayString :: DialCode -> String
toDisplayString (DialCode n) = "+" <> show n

-- | Get E.164 prefix format (same as display string).
toE164Prefix :: DialCode -> String
toE164Prefix = toDisplayString

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if an integer is a valid dial code.
isValid :: Int -> Boolean
isValid n = n >= minDialCode && n <= maxDialCode

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // common codes
-- ═════════════════════════════════════════════════════════════════════════════

-- | North American Numbering Plan (+1): US, Canada, Caribbean
nanp :: DialCode
nanp = DialCode 1

-- | United Kingdom (+44)
uk :: DialCode
uk = DialCode 44

-- | Germany (+49)
germany :: DialCode
germany = DialCode 49

-- | France (+33)
france :: DialCode
france = DialCode 33

-- | Japan (+81)
japan :: DialCode
japan = DialCode 81

-- | China (+86)
china :: DialCode
china = DialCode 86

-- | India (+91)
india :: DialCode
india = DialCode 91

-- | Australia (+61)
australia :: DialCode
australia = DialCode 61

-- | Brazil (+55)
brazil :: DialCode
brazil = DialCode 55

-- | Russia (+7)
russia :: DialCode
russia = DialCode 7

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp integer to range.
clamp :: Int -> Int -> Int -> Int
clamp lo hi x =
  if x <= lo then lo
  else if x >= hi then hi
  else x
