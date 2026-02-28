-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // creditcard // validation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CreditCard Validation — Pure validation functions for credit card data.
-- |
-- | Implements Luhn algorithm, card type detection, and field validation.
-- | All functions are pure — no FFI, no effects.

module Hydrogen.Element.Compound.CreditCard.Validation
  ( luhnCheck
  , validateCardNumber
  , isAllDigits
  , detectCardType
  , validateExpiry
  , validateCvv
  , validateCardholder
  , validateCard
  , validateCardValue
  ) where

import Prelude
  ( mod
  , (+)
  , (-)
  , (*)
  , (>)
  , (<)
  , (>=)
  , (<=)
  , (==)
  , (&&)
  , (||)
  , (<>)
  , not
  )

import Data.Array (reverse, length, foldl, mapWithIndex, filter) as Array
import Data.Int (fromString) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, take, drop) as String
import Data.String.CodeUnits (toCharArray) as CU

import Hydrogen.Element.Compound.CreditCard.Types
  ( CardType(Visa, Mastercard, Amex, Discover, DinersClub, JCB, UnionPay, Unknown)
  , CardValidation
  , cardNumberLength
  , cvvLength
  )

import Hydrogen.Element.Compound.CreditCard.Format (stripSpaces, digitsOnly)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // luhn algorithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate card number using Luhn algorithm (mod 10 check)
luhnCheck :: String -> Boolean
luhnCheck numStr =
  let
    digits = stripSpaces numStr
    len = String.length digits
  in
    if len < 13 || len > 19 then false
    else if not (isAllDigits digits) then false
    else luhnCheckDigits digits

-- | Internal: run Luhn algorithm on clean digit string
luhnCheckDigits :: String -> Boolean
luhnCheckDigits digits =
  let
    chars = CU.toCharArray digits
    nums = charArrayToIntArray chars
    reversed = Array.reverse nums
    processed = Array.mapWithIndex processLuhnDigit reversed
    total = Array.foldl (+) 0 processed
  in total `mod` 10 == 0

-- | Process a single digit in Luhn algorithm
processLuhnDigit :: Int -> Int -> Int
processLuhnDigit idx digit =
  if idx `mod` 2 == 1
    then
      let doubled = digit * 2
      in if doubled > 9 then doubled - 9 else doubled
    else digit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // card number validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate card number (correct length for type + Luhn check)
validateCardNumber :: String -> Boolean
validateCardNumber num =
  let
    digits = stripSpaces num
    cardType = detectCardType digits
    expectedLength = cardNumberLength cardType
    actualLength = String.length digits
  in actualLength == expectedLength && luhnCheck digits

-- | Check if string contains only digit characters
isAllDigits :: String -> Boolean
isAllDigits str =
  let
    chars = CU.toCharArray str
    len = Array.length chars
    digitChars = Array.filter isDigitChar chars
    digitLen = Array.length digitChars
  in len > 0 && len == digitLen

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // card type detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Detect card type from IIN/BIN prefix
detectCardType :: String -> CardType
detectCardType numStr =
  let
    digits = stripSpaces numStr
    p1 = String.take 1 digits
    p2 = String.take 2 digits
    p3 = String.take 3 digits
    p4 = String.take 4 digits
  in
    if p1 == "4" then Visa
    else if p2 == "34" || p2 == "37" then Amex
    else if p2 >= "51" && p2 <= "55" then Mastercard
    else if p4 >= "2221" && p4 <= "2720" then Mastercard
    else if p4 == "6011" then Discover
    else if p2 == "65" then Discover
    else if p3 >= "644" && p3 <= "649" then Discover
    else if p3 >= "300" && p3 <= "305" then DinersClub
    else if p2 == "36" || p2 == "38" then DinersClub
    else if p2 == "35" then JCB
    else if p2 == "62" then UnionPay
    else Unknown

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // field validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate expiry date (MM/YY format)
validateExpiry :: String -> Boolean
validateExpiry expiry =
  let
    digits = digitsOnly expiry
    len = String.length digits
  in
    if len == 4
      then
        let
          monthStr = String.take 2 digits
          yearStr = String.drop 2 digits
        in case Int.fromString monthStr of
          Nothing -> false
          Just month -> case Int.fromString yearStr of
            Nothing -> false
            Just year -> month >= 1 && month <= 12 && year >= 0 && year <= 99
      else false

-- | Validate CVV (3 or 4 digits depending on card type)
validateCvv :: String -> CardType -> Boolean
validateCvv cvvStr cardType =
  let
    len = String.length cvvStr
    expectedLen = cvvLength cardType
  in len == expectedLen && isAllDigits cvvStr

-- | Validate cardholder name (2-100 characters)
validateCardholder :: String -> Boolean
validateCardholder name =
  let len = String.length name
  in len >= 2 && len <= 100

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // complete validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate all card fields
validateCard
  :: { cardNumber :: String
     , expiryDate :: String
     , cvv :: String
     , cardholderName :: String
     }
  -> CardValidation
validateCard input =
  let
    cardType = detectCardType input.cardNumber
    numberValid = validateCardNumber input.cardNumber
    expiryValid = validateExpiry input.expiryDate
    cvvValid = validateCvv input.cvv cardType
    cardholderValid = validateCardholder input.cardholderName
    allComplete = numberValid && expiryValid && cvvValid && cardholderValid
  in
    { cardNumber: numberValid
    , expiry: expiryValid
    , cvv: cvvValid
    , cardholder: cardholderValid
    , complete: allComplete
    }

-- | Validate card value record (accepts records with additional fields)
validateCardValue
  :: forall r
   . { cardNumber :: String
     , expiryDate :: String
     , cvv :: String
     , cardholderName :: String
     | r
     }
  -> CardValidation
validateCardValue value = validateCard
  { cardNumber: value.cardNumber
  , expiryDate: value.expiryDate
  , cvv: value.cvv
  , cardholderName: value.cardholderName
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // internal helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if character is a digit (0-9)
isDigitChar :: Char -> Boolean
isDigitChar c = c >= '0' && c <= '9'

-- | Convert digit character to integer
charToDigit :: Char -> Int
charToDigit c = case c of
  '0' -> 0
  '1' -> 1
  '2' -> 2
  '3' -> 3
  '4' -> 4
  '5' -> 5
  '6' -> 6
  '7' -> 7
  '8' -> 8
  '9' -> 9
  _ -> 0

-- | Convert array of digit characters to array of integers
charArrayToIntArray :: Array Char -> Array Int
charArrayToIntArray chars = Array.foldl (\acc c -> acc <> [charToDigit c]) [] chars
