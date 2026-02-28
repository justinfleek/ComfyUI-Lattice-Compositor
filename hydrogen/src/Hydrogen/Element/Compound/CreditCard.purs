-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // component // credit-card
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CreditCard — Schema-native credit card input component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the 12 pillars.
-- |
-- | The component provides:
-- | - Card number input with automatic formatting and type detection
-- | - Expiry date input with MM/YY formatting
-- | - CVV input with card-type-specific length
-- | - Optional cardholder name input
-- | - Optional visual card preview with flip animation
-- |
-- | ## Pure Validation
-- |
-- | All validation is pure PureScript — no FFI:
-- | - Luhn algorithm for card number checksum
-- | - IIN/BIN prefix detection for card type
-- | - Expiry date format validation
-- | - CVV length validation per card type
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.CreditCard as CreditCard
-- |
-- | -- Basic credit card input
-- | CreditCard.creditCard
-- |   [ CreditCard.cardNumber "4111111111111111"
-- |   , CreditCard.expiryDate "12/25"
-- |   , CreditCard.cvv "123"
-- |   , CreditCard.onChange HandleCardChange
-- |   ]
-- |
-- | -- With cardholder name
-- | CreditCard.creditCard
-- |   [ CreditCard.cardNumber cardNum
-- |   , CreditCard.cardholderName "John Doe"
-- |   , CreditCard.showCardholderName true
-- |   ]
-- |
-- | -- With visual card preview
-- | CreditCard.creditCardWithPreview
-- |   [ CreditCard.cardNumber cardNum
-- |   , CreditCard.expiryDate expiry
-- |   , CreditCard.cvv cvv
-- |   , CreditCard.cardholderName name
-- |   ]
-- | ```

module Hydrogen.Element.Compound.CreditCard
  ( -- * Main Components
    creditCard
  , creditCardWithPreview
  , cardNumberInput
  , expiryInput
  , cvvInput
  , cardholderInput
  , cardPreview
  
  -- * Props
  , CreditCardProps
  , CreditCardProp
  , defaultProps
  
  -- * Prop Builders
  , cardNumber
  , expiryDate
  , cvv
  , cardholderName
  , showCardholderName
  , showCardPreview
  , focusedField
  , disabled
  , className
  , onCardNumberChange
  , onExpiryChange
  , onCvvChange
  , onCardholderChange
  , onChange
  , onValidate
  , onFocusChange
  
  -- * Re-exports from Types
  , module Hydrogen.Element.Compound.CreditCard.Types
  
  -- * Re-exports from Validation
  , module Hydrogen.Element.Compound.CreditCard.Validation
  
  -- * Re-exports from Format
  , module Hydrogen.Element.Compound.CreditCard.Format
  ) where

import Prelude
  ( (<>)
  , (==)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.CreditCard.Types
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
  )

import Hydrogen.Element.Compound.CreditCard.Validation
  ( luhnCheck
  , validateCardNumber
  , isAllDigits
  , detectCardType
  , validateExpiry
  , validateCvv
  , validateCardholder
  , validateCard
  , validateCardValue
  )

import Hydrogen.Element.Compound.CreditCard.Format
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
  )

import Hydrogen.Element.Compound.CreditCard.Render as Render

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Credit card component properties.
type CreditCardProps msg =
  { -- Field values
    cardNumber :: String
  , expiryDate :: String
  , cvv :: String
  , cardholderName :: String
  
  -- Display options
  , showCardholderName :: Boolean
  , showCardPreview :: Boolean
  , focusedField :: CardField
  , disabled :: Boolean
  , className :: String
  
  -- Error messages
  , errors :: CardErrors
  
  -- Event handlers
  , onCardNumberChange :: Maybe (String -> msg)
  , onExpiryChange :: Maybe (String -> msg)
  , onCvvChange :: Maybe (String -> msg)
  , onCardholderChange :: Maybe (String -> msg)
  , onChange :: Maybe (CreditCardValue -> msg)
  , onValidate :: Maybe (CardValidation -> msg)
  , onFocusChange :: Maybe (CardField -> msg)
  }

-- | Property modifier function.
type CreditCardProp msg = CreditCardProps msg -> CreditCardProps msg

-- | Default properties.
defaultProps :: forall msg. CreditCardProps msg
defaultProps =
  { cardNumber: ""
  , expiryDate: ""
  , cvv: ""
  , cardholderName: ""
  , showCardholderName: false
  , showCardPreview: false
  , focusedField: NoField
  , disabled: false
  , className: ""
  , errors:
      { cardNumber: Nothing
      , expiry: Nothing
      , cvv: Nothing
      , cardholder: Nothing
      }
  , onCardNumberChange: Nothing
  , onExpiryChange: Nothing
  , onCvvChange: Nothing
  , onCardholderChange: Nothing
  , onChange: Nothing
  , onValidate: Nothing
  , onFocusChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set card number value.
cardNumber :: forall msg. String -> CreditCardProp msg
cardNumber n props = props { cardNumber = n }

-- | Set expiry date value.
expiryDate :: forall msg. String -> CreditCardProp msg
expiryDate e props = props { expiryDate = e }

-- | Set CVV value.
cvv :: forall msg. String -> CreditCardProp msg
cvv c props = props { cvv = c }

-- | Set cardholder name value.
cardholderName :: forall msg. String -> CreditCardProp msg
cardholderName n props = props { cardholderName = n }

-- | Show cardholder name field.
showCardholderName :: forall msg. Boolean -> CreditCardProp msg
showCardholderName s props = props { showCardholderName = s }

-- | Show visual card preview.
showCardPreview :: forall msg. Boolean -> CreditCardProp msg
showCardPreview s props = props { showCardPreview = s }

-- | Set currently focused field.
focusedField :: forall msg. CardField -> CreditCardProp msg
focusedField f props = props { focusedField = f }

-- | Set disabled state.
disabled :: forall msg. Boolean -> CreditCardProp msg
disabled d props = props { disabled = d }

-- | Add custom CSS class to root element.
className :: forall msg. String -> CreditCardProp msg
className c props = props { className = props.className <> " " <> c }

-- | Set card number change handler.
onCardNumberChange :: forall msg. (String -> msg) -> CreditCardProp msg
onCardNumberChange handler props = props { onCardNumberChange = Just handler }

-- | Set expiry change handler.
onExpiryChange :: forall msg. (String -> msg) -> CreditCardProp msg
onExpiryChange handler props = props { onExpiryChange = Just handler }

-- | Set CVV change handler.
onCvvChange :: forall msg. (String -> msg) -> CreditCardProp msg
onCvvChange handler props = props { onCvvChange = Just handler }

-- | Set cardholder name change handler.
onCardholderChange :: forall msg. (String -> msg) -> CreditCardProp msg
onCardholderChange handler props = props { onCardholderChange = Just handler }

-- | Set overall change handler.
onChange :: forall msg. (CreditCardValue -> msg) -> CreditCardProp msg
onChange handler props = props { onChange = Just handler }

-- | Set validation handler.
onValidate :: forall msg. (CardValidation -> msg) -> CreditCardProp msg
onValidate handler props = props { onValidate = Just handler }

-- | Set focus change handler.
onFocusChange :: forall msg. (CardField -> msg) -> CreditCardProp msg
onFocusChange handler props = props { onFocusChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Main credit card input component.
creditCard :: forall msg. Array (CreditCardProp msg) -> E.Element msg
creditCard propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    cardType = detectCardType props.cardNumber
    rootAttrs = 
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "16px"
      ] <> if props.className == "" 
             then [] 
             else [ E.class_ props.className ]
  in
    E.div_ rootAttrs
      [ -- Card number
        cardNumberInput props cardType
      -- Expiry and CVV row
      , E.div_
          [ E.style "display" "flex"
          , E.style "gap" "16px"
          ]
          [ E.div_
              [ E.style "flex" "1" ]
              [ expiryInput props ]
          , E.div_
              [ E.style "width" "96px" ]
              [ cvvInput props cardType ]
          ]
      -- Cardholder name (optional)
      , if props.showCardholderName
          then cardholderInput props
          else E.empty
      ]

-- | Credit card with visual preview.
creditCardWithPreview :: forall msg. Array (CreditCardProp msg) -> E.Element msg
creditCardWithPreview propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    cardType = detectCardType props.cardNumber
    rootAttrs = 
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "24px"
      ] <> if props.className == "" 
             then [] 
             else [ E.class_ props.className ]
  in
    E.div_ rootAttrs
      [ -- Visual card preview
        cardPreview props cardType
      -- Input fields
      , creditCard propMods
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // individual inputs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card number input field.
cardNumberInput :: forall msg. CreditCardProps msg -> CardType -> E.Element msg
cardNumberInput props cardType =
  Render.renderCardNumberInput
    { value: props.cardNumber
    , cardType: cardType
    , hasError: hasCardNumberError props.errors
    , errorMsg: errorToString props.errors.cardNumber
    , disabled: props.disabled
    , onInput: props.onCardNumberChange
    , onFocus: focusMsg props.onFocusChange CardNumberField
    , onBlur: focusMsg props.onFocusChange NoField
    }

-- | Expiry date input field.
expiryInput :: forall msg. CreditCardProps msg -> E.Element msg
expiryInput props =
  Render.renderExpiryInput
    { value: props.expiryDate
    , hasError: hasExpiryError props.errors
    , errorMsg: errorToString props.errors.expiry
    , disabled: props.disabled
    , onInput: props.onExpiryChange
    , onFocus: focusMsg props.onFocusChange ExpiryField
    , onBlur: focusMsg props.onFocusChange NoField
    }

-- | CVV input field.
cvvInput :: forall msg. CreditCardProps msg -> CardType -> E.Element msg
cvvInput props cardType =
  Render.renderCvvInput
    { value: props.cvv
    , cardType: cardType
    , hasError: hasCvvError props.errors
    , errorMsg: errorToString props.errors.cvv
    , disabled: props.disabled
    , onInput: props.onCvvChange
    , onFocus: focusMsg props.onFocusChange CvvField
    , onBlur: focusMsg props.onFocusChange NoField
    }

-- | Cardholder name input field.
cardholderInput :: forall msg. CreditCardProps msg -> E.Element msg
cardholderInput props =
  Render.renderCardholderInput
    { value: props.cardholderName
    , hasError: hasCardholderError props.errors
    , errorMsg: errorToString props.errors.cardholder
    , disabled: props.disabled
    , onInput: props.onCardholderChange
    , onFocus: focusMsg props.onFocusChange CardholderField
    , onBlur: focusMsg props.onFocusChange NoField
    }

-- | Visual card preview.
cardPreview :: forall msg. CreditCardProps msg -> CardType -> E.Element msg
cardPreview props cardType =
  Render.renderCardPreview
    { cardNumber: props.cardNumber
    , expiryDate: props.expiryDate
    , cvv: props.cvv
    , cardholderName: props.cardholderName
    , cardType: cardType
    , focusedField: props.focusedField
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if card number has error.
hasCardNumberError :: CardErrors -> Boolean
hasCardNumberError errors = case errors.cardNumber of
  Nothing -> false
  Just _ -> true

-- | Check if expiry has error.
hasExpiryError :: CardErrors -> Boolean
hasExpiryError errors = case errors.expiry of
  Nothing -> false
  Just _ -> true

-- | Check if CVV has error.
hasCvvError :: CardErrors -> Boolean
hasCvvError errors = case errors.cvv of
  Nothing -> false
  Just _ -> true

-- | Check if cardholder has error.
hasCardholderError :: CardErrors -> Boolean
hasCardholderError errors = case errors.cardholder of
  Nothing -> false
  Just _ -> true

-- | Convert error to display string.
errorToString :: Maybe CardFieldError -> Maybe String
errorToString maybeError = case maybeError of
  Nothing -> Nothing
  Just err -> Just (showError err)

-- | Show error as string.
showError :: CardFieldError -> String
showError InvalidNumber = "Invalid card number"
showError InvalidExpiry = "Invalid expiry date"
showError InvalidCvv = "Invalid security code"
showError InvalidCardholder = "Invalid cardholder name"
showError EmptyField = "This field is required"

-- | Create focus change message.
focusMsg :: forall msg. Maybe (CardField -> msg) -> CardField -> Maybe msg
focusMsg maybeHandler field = case maybeHandler of
  Nothing -> Nothing
  Just handler -> Just (handler field)
