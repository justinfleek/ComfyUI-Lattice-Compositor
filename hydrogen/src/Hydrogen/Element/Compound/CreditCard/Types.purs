-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // creditcard // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CreditCard Types — Core data types for credit card component.
-- |
-- | ## Overview
-- |
-- | Defines all types used by the credit card component:
-- | - Card network types (Visa, Mastercard, Amex, etc.)
-- | - Field identifiers for focus tracking
-- | - Value record for complete card state
-- | - Validation result record
-- | - Field-specific error types

module Hydrogen.Element.Compound.CreditCard.Types
  ( CardType(Visa, Mastercard, Amex, Discover, DinersClub, JCB, UnionPay, Unknown)
  , CardField(CardNumberField, ExpiryField, CvvField, CardholderField, NoField)
  , CreditCardValue
  , CardValidation
  , CardFieldError(InvalidNumber, InvalidExpiry, InvalidCvv, InvalidCardholder, EmptyField)
  , CardErrors
  , cardNumberLength
  , cvvLength
  , cardTypeName
  , cardTypeGradient
  , cardTypeFullName
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  )

import Data.Maybe (Maybe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // card network type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card network/brand type.
-- |
-- | Detected from the IIN/BIN prefix of the card number.
data CardType
  = Visa
  | Mastercard
  | Amex
  | Discover
  | DinersClub
  | JCB
  | UnionPay
  | Unknown

derive instance eqCardType :: Eq CardType

instance showCardType :: Show CardType where
  show Visa = "Visa"
  show Mastercard = "Mastercard"
  show Amex = "American Express"
  show Discover = "Discover"
  show DinersClub = "Diners Club"
  show JCB = "JCB"
  show UnionPay = "UnionPay"
  show Unknown = "Unknown"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // field identifier
-- ═════════════════════════════════════════════════════════════════════════════

-- | Which field is currently focused.
-- |
-- | Used for visual feedback and card flip animation.
data CardField
  = CardNumberField
  | ExpiryField
  | CvvField
  | CardholderField
  | NoField

derive instance eqCardField :: Eq CardField

instance showCardField :: Show CardField where
  show CardNumberField = "CardNumber"
  show ExpiryField = "Expiry"
  show CvvField = "CVV"
  show CardholderField = "Cardholder"
  show NoField = "None"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // card value record
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete credit card value state.
type CreditCardValue =
  { cardNumber :: String
  , expiryDate :: String
  , cvv :: String
  , cardholderName :: String
  , cardType :: CardType
  , isValid :: Boolean
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // validation records
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validation result for each field.
type CardValidation =
  { cardNumber :: Boolean
  , expiry :: Boolean
  , cvv :: Boolean
  , cardholder :: Boolean
  , complete :: Boolean
  }

-- | Specific error types for card fields.
data CardFieldError
  = InvalidNumber
  | InvalidExpiry
  | InvalidCvv
  | InvalidCardholder
  | EmptyField

derive instance eqCardFieldError :: Eq CardFieldError

instance showCardFieldError :: Show CardFieldError where
  show InvalidNumber = "Invalid card number"
  show InvalidExpiry = "Invalid expiry date"
  show InvalidCvv = "Invalid security code"
  show InvalidCardholder = "Invalid cardholder name"
  show EmptyField = "This field is required"

-- | Error state for all fields.
type CardErrors =
  { cardNumber :: Maybe CardFieldError
  , expiry :: Maybe CardFieldError
  , cvv :: Maybe CardFieldError
  , cardholder :: Maybe CardFieldError
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Expected card number length for each network.
cardNumberLength :: CardType -> Int
cardNumberLength cardType =
  if cardType == Amex then 15
  else if cardType == DinersClub then 14
  else 16

-- | Expected CVV length for each network.
cvvLength :: CardType -> Int
cvvLength cardType =
  if cardType == Amex then 4
  else 3

-- | Display name for card type (short form for UI).
cardTypeName :: CardType -> String
cardTypeName Visa = "VISA"
cardTypeName Mastercard = "MC"
cardTypeName Amex = "AMEX"
cardTypeName Discover = "DISCOVER"
cardTypeName DinersClub = "DINERS"
cardTypeName JCB = "JCB"
cardTypeName UnionPay = "UNIONPAY"
cardTypeName Unknown = ""

-- | CSS gradient classes for card preview background.
cardTypeGradient :: CardType -> String
cardTypeGradient Visa = "from-blue-600 to-blue-800"
cardTypeGradient Mastercard = "from-red-500 to-orange-500"
cardTypeGradient Amex = "from-gray-700 to-gray-900"
cardTypeGradient Discover = "from-orange-400 to-orange-600"
cardTypeGradient DinersClub = "from-gray-600 to-gray-800"
cardTypeGradient JCB = "from-green-600 to-green-800"
cardTypeGradient UnionPay = "from-red-600 to-red-800"
cardTypeGradient Unknown = "from-gray-600 to-gray-800"

-- | Full display name for card type (using Show instance)
-- | Useful for accessibility and detailed UI
cardTypeFullName :: CardType -> String
cardTypeFullName = show

