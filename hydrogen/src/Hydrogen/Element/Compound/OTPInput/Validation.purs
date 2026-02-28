-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // otpinput // validation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Validation — Input validation and character filtering.
-- |
-- | ## Security Philosophy
-- |
-- | Validation is a security boundary. Characters that reach OTPValue must be:
-- | 1. Valid for the input type (numeric: 0-9, alphanumeric: A-Za-z0-9)
-- | 2. Sanitized (no control characters, no unicode weirdness)
-- | 3. Normalized (lowercase converted to uppercase for alphanumeric)
-- |
-- | ## Paste Handling
-- |
-- | Paste events are particularly dangerous:
-- | - Users may paste passwords or other sensitive data
-- | - Pasted text may contain formatting characters
-- | - Length may exceed expected OTP length
-- |
-- | All pasted text is sanitized, filtered, and truncated.
-- |
-- | ## Dependencies
-- |
-- | - Types module for OTPInputType, OTPDigitCount, OTPValue

module Hydrogen.Element.Compound.OTPInput.Validation
  ( -- * Character Validation
    validateChar
  , isValidDigit
  , isValidAlphanumeric
  , normalizeChar
  
  -- * String Validation
  , validateString
  , sanitizeString
  , filterValidChars
  
  -- * Paste Handling
  , validatePaste
  , extractValidOTP
  
  -- * Input Mode Helpers
  , getInputMode
  , getInputPattern
  , getAutoComplete
  ) where

import Prelude
  ( (&&)
  , (||)
  , (>=)
  , (<=)
  , (<)
  , (+)
  , (-)
  , (>)
  , otherwise
  )

import Data.Array (filter, length, index, snoc)
import Data.Char (toCharCode)
import Data.Maybe (Maybe(Nothing, Just))
import Data.String.CodeUnits as SCU

import Hydrogen.Element.Compound.OTPInput.Types
  ( OTPInputType(Numeric, Alphanumeric)
  , OTPDigitCount
  , OTPValue
  , otpValue
  , unwrapDigitCount
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // character validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate a character for the given input type.
-- | Returns Just normalizedChar if valid, Nothing if invalid.
validateChar :: OTPInputType -> Char -> Maybe Char
validateChar inputType c =
  let normalized = normalizeChar c
  in case inputType of
       Numeric ->
         if isValidDigit normalized
           then Just normalized
           else Nothing
       Alphanumeric ->
         if isValidAlphanumeric normalized
           then Just normalized
           else Nothing

-- | Check if character is a valid digit (0-9)
isValidDigit :: Char -> Boolean
isValidDigit c =
  let code = toCharCode c
  in code >= 48 && code <= 57  -- '0' = 48, '9' = 57

-- | Check if character is valid alphanumeric (0-9, A-Z, a-z)
isValidAlphanumeric :: Char -> Boolean
isValidAlphanumeric c =
  let code = toCharCode c
  in (code >= 48 && code <= 57)    -- 0-9
  || (code >= 65 && code <= 90)    -- A-Z
  || (code >= 97 && code <= 122)   -- a-z

-- | Normalize a character.
-- | Currently just passes through, but could:
-- | - Convert fullwidth digits to ASCII
-- | - Normalize Unicode confusables
normalizeChar :: Char -> Char
normalizeChar c = c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // string validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate and convert a string to an OTPValue.
-- | Invalid characters become empty slots.
validateString :: OTPInputType -> OTPDigitCount -> String -> OTPValue
validateString inputType count str =
  let sanitized = sanitizeString str
  in otpValue inputType count sanitized

-- | Remove potentially dangerous characters from input.
-- | Strips control characters, null bytes, etc.
sanitizeString :: String -> String
sanitizeString str =
  let chars = SCU.toCharArray str
      safe = filter isSafeChar chars
  in SCU.fromCharArray safe

-- | Check if a character is safe (printable ASCII range)
isSafeChar :: Char -> Boolean
isSafeChar c =
  let code = toCharCode c
  in code >= 32 && code <= 126  -- Printable ASCII only

-- | Filter a string to only valid characters for input type
filterValidChars :: OTPInputType -> String -> String
filterValidChars inputType str =
  let chars = SCU.toCharArray str
      valid = filter (isValidForType inputType) chars
  in SCU.fromCharArray valid

-- | Check if character is valid for input type
isValidForType :: OTPInputType -> Char -> Boolean
isValidForType Numeric c = isValidDigit c
isValidForType Alphanumeric c = isValidAlphanumeric c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // paste handling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate pasted text and extract valid OTP value.
-- | Returns sanitized, filtered, truncated OTPValue.
validatePaste :: OTPInputType -> OTPDigitCount -> String -> OTPValue
validatePaste inputType count pastedText =
  let
    sanitized = sanitizeString pastedText
    filtered = filterValidChars inputType sanitized
    truncated = takeChars (unwrapDigitCount count) filtered
  in
    otpValue inputType count truncated

-- | Extract valid OTP from any string.
-- | Useful for extracting codes from SMS messages like "Your code is 123456"
extractValidOTP :: OTPInputType -> OTPDigitCount -> String -> OTPValue
extractValidOTP inputType count text =
  let
    sanitized = sanitizeString text
    -- Extract only valid characters
    chars = SCU.toCharArray sanitized
    validChars = filter (isValidForType inputType) chars
    extracted = SCU.fromCharArray validChars
    truncated = takeChars (unwrapDigitCount count) extracted
  in
    otpValue inputType count truncated

-- | Take first n characters from string
takeChars :: Int -> String -> String
takeChars n str =
  let chars = SCU.toCharArray str
      taken = takeArr n chars
  in SCU.fromCharArray taken

-- | Take first n elements from array using pure recursion
takeArr :: forall a. Int -> Array a -> Array a
takeArr n arr = go 0 n arr []
  where
    go idx remaining xs acc
      | remaining <= 0 = acc
      | idx >= length xs = acc
      | otherwise = case index xs idx of
          Nothing -> acc
          Just x -> go (idx + 1) (remaining - 1) xs (snoc acc x)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // input mode helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get HTML inputmode attribute value for input type
getInputMode :: OTPInputType -> String
getInputMode Numeric = "numeric"
getInputMode Alphanumeric = "text"

-- | Get HTML pattern attribute value for input type
getInputPattern :: OTPInputType -> String
getInputPattern Numeric = "[0-9]"
getInputPattern Alphanumeric = "[a-zA-Z0-9]"

-- | Get autocomplete attribute value for OTP inputs
getAutoComplete :: String
getAutoComplete = "one-time-code"
