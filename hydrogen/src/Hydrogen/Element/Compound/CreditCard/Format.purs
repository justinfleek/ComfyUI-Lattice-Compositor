-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // creditcard // format
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CreditCard Format — Pure formatting functions for credit card data.
-- |
-- | All functions are pure — no FFI, no effects.

module Hydrogen.Element.Compound.CreditCard.Format
  ( formatCardNumber
  , formatStandard
  , formatAmex
  , formatDiners
  , formatExpiry
  , placeholderCardNumber
  , placeholderExpiry
  , placeholderCvv
  , maskCardNumber
  , displayCardNumber
  , displayExpiry
  , displayCardholder
  , stripSpaces
  , digitsOnly
  ) where

import Prelude
  ( (<>)
  , (>)
  , (==)
  , (&&)
  , (>=)
  , (<=)
  , (-)
  , not
  )

import Data.Array (filter) as Array
import Data.String (length, take, drop, joinWith, toCodePointArray, fromCodePointArray, toUpper) as String
import Data.String.CodePoints (codePointFromChar) as CP
import Data.String.CodeUnits (toCharArray, fromCharArray) as CU

import Hydrogen.Element.Compound.CreditCard.Types
  ( CardType(Visa, Mastercard, Amex, Discover, DinersClub, JCB, UnionPay, Unknown)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // card number formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format card number with appropriate spacing for card type.
formatCardNumber :: String -> CardType -> String
formatCardNumber num cardType =
  let
    digits = stripSpaces num
  in case cardType of
    Amex -> formatAmex digits
    DinersClub -> formatDiners digits
    Visa -> formatStandard digits
    Mastercard -> formatStandard digits
    Discover -> formatStandard digits
    JCB -> formatStandard digits
    UnionPay -> formatStandard digits
    Unknown -> formatStandard digits

-- | Format with standard 4-4-4-4 grouping.
formatStandard :: String -> String
formatStandard digits =
  let
    g1 = String.take 4 digits
    g2 = String.take 4 (String.drop 4 digits)
    g3 = String.take 4 (String.drop 8 digits)
    g4 = String.take 4 (String.drop 12 digits)
  in String.joinWith " " (filterNonEmpty [g1, g2, g3, g4])

-- | Format with Amex 4-6-5 grouping.
formatAmex :: String -> String
formatAmex digits =
  let
    g1 = String.take 4 digits
    g2 = String.take 6 (String.drop 4 digits)
    g3 = String.take 5 (String.drop 10 digits)
  in String.joinWith " " (filterNonEmpty [g1, g2, g3])

-- | Format with Diners Club 4-6-4 grouping.
formatDiners :: String -> String
formatDiners digits =
  let
    g1 = String.take 4 digits
    g2 = String.take 6 (String.drop 4 digits)
    g3 = String.take 4 (String.drop 10 digits)
  in String.joinWith " " (filterNonEmpty [g1, g2, g3])

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // expiry formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format expiry input to MM/YY.
formatExpiry :: String -> String
formatExpiry input =
  let
    digits = digitsOnly input
    len = String.length digits
  in
    if len == 0 then ""
    else if len == 1 then digits
    else if len == 2 then digits <> "/"
    else String.take 2 digits <> "/" <> String.take 2 (String.drop 2 digits)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // placeholder generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Placeholder text for card number input.
placeholderCardNumber :: CardType -> String
placeholderCardNumber Amex = "•••• •••••• •••••"
placeholderCardNumber DinersClub = "•••• •••••• ••••"
placeholderCardNumber _ = "•••• •••• •••• ••••"

-- | Placeholder text for expiry input.
placeholderExpiry :: String
placeholderExpiry = "MM/YY"

-- | Placeholder text for CVV input.
placeholderCvv :: CardType -> String
placeholderCvv Amex = "••••"
placeholderCvv _ = "•••"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // display helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mask card number showing only last 4 digits.
maskCardNumber :: String -> String
maskCardNumber num =
  let
    digits = stripSpaces num
    len = String.length digits
    last4 = String.drop (len - 4) digits
  in
    if len >= 4
      then "•••• •••• •••• " <> last4
      else digits

-- | Display card number for preview, with fallback.
displayCardNumber :: String -> CardType -> String
displayCardNumber num cardType =
  let
    formatted = formatCardNumber num cardType
  in
    if String.length formatted > 0
      then formatted
      else placeholderCardNumber cardType

-- | Display expiry for preview, with fallback.
displayExpiry :: String -> String
displayExpiry expiry =
  if String.length expiry > 0
    then expiry
    else placeholderExpiry

-- | Display cardholder name for preview, with fallback.
displayCardholder :: String -> String
displayCardholder name =
  if String.length name > 0
    then String.toUpper name
    else "YOUR NAME"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // input processing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Remove all spaces from a string.
stripSpaces :: String -> String
stripSpaces str =
  let
    codePoints = String.toCodePointArray str
    spaceCP = CP.codePointFromChar ' '
  in String.fromCodePointArray (Array.filter (\cp -> not (cp == spaceCP)) codePoints)

-- | Extract only digit characters from a string.
digitsOnly :: String -> String
digitsOnly str =
  CU.fromCharArray (Array.filter isDigitChar (CU.toCharArray str))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter empty strings from an array.
filterNonEmpty :: Array String -> Array String
filterNonEmpty = Array.filter (\s -> String.length s > 0)

-- | Check if a character is a digit (0-9).
isDigitChar :: Char -> Boolean
isDigitChar c = c >= '0' && c <= '9'
