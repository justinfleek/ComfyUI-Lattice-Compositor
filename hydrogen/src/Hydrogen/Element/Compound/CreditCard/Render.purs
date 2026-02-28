-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // creditcard // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CreditCard Render — Element rendering helpers for credit card UI.

module Hydrogen.Element.Compound.CreditCard.Render
  ( renderCardNumberInput
  , renderExpiryInput
  , renderCvvInput
  , renderCardholderInput
  , renderCardPreview
  , renderCardFront
  , renderCardBack
  , renderCardIcon
  , renderCardBrandLogo
  , renderQuestionIcon
  , renderFieldLabel
  , renderFieldError
  , renderInputWrapper
  ) where

import Prelude (show, (<>), (==))
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.CreditCard.Types
  ( CardType(Visa, Mastercard, Amex, Discover, DinersClub, JCB, UnionPay, Unknown)
  , CardField(CvvField)
  , cardTypeName
  , cvvLength
  )
import Hydrogen.Element.Compound.CreditCard.Format
  ( formatCardNumber
  , displayCardNumber
  , displayExpiry
  , displayCardholder
  , placeholderCvv
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // input field rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render card number input field.
renderCardNumberInput
  :: forall msg
   . { value :: String
     , cardType :: CardType
     , hasError :: Boolean
     , errorMsg :: Maybe String
     , disabled :: Boolean
     , onInput :: Maybe (String -> msg)
     , onFocus :: Maybe msg
     , onBlur :: Maybe msg
     }
  -> E.Element msg
renderCardNumberInput cfg =
  let
    formattedNumber = formatCardNumber cfg.value cfg.cardType
    inputAttrs =
      [ E.type_ "text"
      , E.value formattedNumber
      , E.placeholder "1234 5678 9012 3456"
      , E.attr "inputmode" "numeric"
      , E.attr "autocomplete" "cc-number"
      , E.attr "maxlength" "19"
      , E.ariaLabel "Card number"
      , E.style "width" "100%"
      , E.style "height" "40px"
      , E.style "padding-left" "40px"
      , E.style "padding-right" "48px"
      , E.style "border-radius" "6px"
      , E.style "border" (if cfg.hasError then "1px solid #ef4444" else "1px solid #e5e7eb")
      , E.style "font-size" "14px"
      , E.style "outline" "none"
      ] <> disabledAttrs cfg.disabled
        <> inputHandlerAttrs cfg.onInput
        <> focusHandlerAttrs cfg.onFocus
        <> blurHandlerAttrs cfg.onBlur
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "6px"
      ]
      [ renderFieldLabel "Card Number"
      , E.div_
          [ E.style "position" "relative" ]
          [ E.input_ inputAttrs
          , E.div_
              [ E.style "position" "absolute"
              , E.style "left" "12px"
              , E.style "top" "50%"
              , E.style "transform" "translateY(-50%)"
              ]
              [ renderCardIcon ]
          , E.div_
              [ E.style "position" "absolute"
              , E.style "right" "12px"
              , E.style "top" "50%"
              , E.style "transform" "translateY(-50%)"
              ]
              [ renderCardBrandLogo cfg.cardType ]
          ]
      , renderFieldError cfg.errorMsg
      ]

-- | Render expiry date input field.
renderExpiryInput
  :: forall msg
   . { value :: String
     , hasError :: Boolean
     , errorMsg :: Maybe String
     , disabled :: Boolean
     , onInput :: Maybe (String -> msg)
     , onFocus :: Maybe msg
     , onBlur :: Maybe msg
     }
  -> E.Element msg
renderExpiryInput cfg =
  let
    inputAttrs =
      [ E.type_ "text"
      , E.value cfg.value
      , E.placeholder "MM/YY"
      , E.attr "inputmode" "numeric"
      , E.attr "autocomplete" "cc-exp"
      , E.attr "maxlength" "5"
      , E.ariaLabel "Expiry date"
      , E.style "width" "100%"
      , E.style "height" "40px"
      , E.style "padding" "0 12px"
      , E.style "border-radius" "6px"
      , E.style "border" (if cfg.hasError then "1px solid #ef4444" else "1px solid #e5e7eb")
      , E.style "font-size" "14px"
      , E.style "outline" "none"
      ] <> disabledAttrs cfg.disabled
        <> inputHandlerAttrs cfg.onInput
        <> focusHandlerAttrs cfg.onFocus
        <> blurHandlerAttrs cfg.onBlur
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "6px"
      ]
      [ renderFieldLabel "Expiry Date"
      , E.input_ inputAttrs
      , renderFieldError cfg.errorMsg
      ]

-- | Render CVV input field.
renderCvvInput
  :: forall msg
   . { value :: String
     , cardType :: CardType
     , hasError :: Boolean
     , errorMsg :: Maybe String
     , disabled :: Boolean
     , onInput :: Maybe (String -> msg)
     , onFocus :: Maybe msg
     , onBlur :: Maybe msg
     }
  -> E.Element msg
renderCvvInput cfg =
  let
    maxLen = show (cvvLength cfg.cardType)
    placeholder = placeholderCvv cfg.cardType
    inputAttrs =
      [ E.type_ "password"
      , E.value cfg.value
      , E.placeholder placeholder
      , E.attr "inputmode" "numeric"
      , E.attr "autocomplete" "cc-csc"
      , E.attr "maxlength" maxLen
      , E.ariaLabel "Security code"
      , E.style "width" "100%"
      , E.style "height" "40px"
      , E.style "padding" "0 12px"
      , E.style "padding-right" "36px"
      , E.style "border-radius" "6px"
      , E.style "border" (if cfg.hasError then "1px solid #ef4444" else "1px solid #e5e7eb")
      , E.style "font-size" "14px"
      , E.style "outline" "none"
      ] <> disabledAttrs cfg.disabled
        <> inputHandlerAttrs cfg.onInput
        <> focusHandlerAttrs cfg.onFocus
        <> blurHandlerAttrs cfg.onBlur
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "6px"
      ]
      [ renderFieldLabel "CVV"
      , E.div_
          [ E.style "position" "relative" ]
          [ E.input_ inputAttrs
          , E.button_
              [ E.type_ "button"
              , E.ariaLabel "What is CVV?"
              , E.style "position" "absolute"
              , E.style "right" "8px"
              , E.style "top" "50%"
              , E.style "transform" "translateY(-50%)"
              , E.style "background" "none"
              , E.style "border" "none"
              , E.style "cursor" "pointer"
              , E.style "color" "#9ca3af"
              ]
              [ renderQuestionIcon ]
          ]
      , renderFieldError cfg.errorMsg
      ]

-- | Render cardholder name input field.
renderCardholderInput
  :: forall msg
   . { value :: String
     , hasError :: Boolean
     , errorMsg :: Maybe String
     , disabled :: Boolean
     , onInput :: Maybe (String -> msg)
     , onFocus :: Maybe msg
     , onBlur :: Maybe msg
     }
  -> E.Element msg
renderCardholderInput cfg =
  let
    inputAttrs =
      [ E.type_ "text"
      , E.value cfg.value
      , E.placeholder "John Doe"
      , E.attr "autocomplete" "cc-name"
      , E.ariaLabel "Cardholder name"
      , E.style "width" "100%"
      , E.style "height" "40px"
      , E.style "padding" "0 12px"
      , E.style "border-radius" "6px"
      , E.style "border" (if cfg.hasError then "1px solid #ef4444" else "1px solid #e5e7eb")
      , E.style "font-size" "14px"
      , E.style "outline" "none"
      ] <> disabledAttrs cfg.disabled
        <> inputHandlerAttrs cfg.onInput
        <> focusHandlerAttrs cfg.onFocus
        <> blurHandlerAttrs cfg.onBlur
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "6px"
      ]
      [ renderFieldLabel "Cardholder Name"
      , E.input_ inputAttrs
      , renderFieldError cfg.errorMsg
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // card preview rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render visual card preview.
renderCardPreview
  :: forall msg
   . { cardNumber :: String
     , expiryDate :: String
     , cvv :: String
     , cardholderName :: String
     , cardType :: CardType
     , focusedField :: CardField
     }
  -> E.Element msg
renderCardPreview cfg =
  let
    isCvvFocused = cfg.focusedField == CvvField
    transformStyle = if isCvvFocused then "rotateY(180deg)" else "rotateY(0deg)"
  in
    E.div_
      [ E.style "perspective" "1000px"
      , E.style "width" "320px"
      , E.style "height" "192px"
      ]
      [ E.div_
          [ E.style "position" "relative"
          , E.style "width" "100%"
          , E.style "height" "100%"
          , E.style "transform-style" "preserve-3d"
          , E.style "transition" "transform 0.5s"
          , E.style "transform" transformStyle
          ]
          [ renderCardFront cfg
          , renderCardBack cfg
          ]
      ]

-- | Render front of card preview.
renderCardFront
  :: forall msg r
   . { cardNumber :: String
     , expiryDate :: String
     , cardholderName :: String
     , cardType :: CardType
     | r
     }
  -> E.Element msg
renderCardFront cfg =
  let
    displayNumber = displayCardNumber cfg.cardNumber cfg.cardType
    displayExp = displayExpiry cfg.expiryDate
    displayName = displayCardholder cfg.cardholderName
    gradient = cardTypeGradientCss cfg.cardType
  in
    E.div_
      [ E.style "position" "absolute"
      , E.style "inset" "0"
      , E.style "border-radius" "12px"
      , E.style "padding" "24px"
      , E.style "color" "white"
      , E.style "background" gradient
      , E.style "backface-visibility" "hidden"
      , E.style "box-shadow" "0 10px 40px rgba(0,0,0,0.3)"
      ]
      [ -- Chip
        E.div_
          [ E.style "width" "48px"
          , E.style "height" "36px"
          , E.style "border-radius" "4px"
          , E.style "background" "linear-gradient(135deg, #ffd700 0%, #ffec8b 50%, #daa520 100%)"
          , E.style "margin-bottom" "24px"
          ]
          []
      -- Card number
      , E.div_
          [ E.style "font-size" "20px"
          , E.style "letter-spacing" "2px"
          , E.style "font-family" "monospace"
          , E.style "margin-bottom" "16px"
          ]
          [ E.text displayNumber ]
      -- Bottom row
      , E.div_
          [ E.style "display" "flex"
          , E.style "justify-content" "space-between"
          , E.style "align-items" "flex-end"
          ]
          [ -- Cardholder
            E.div_ []
              [ E.div_
                  [ E.style "font-size" "10px"
                  , E.style "opacity" "0.7"
                  , E.style "margin-bottom" "4px"
                  ]
                  [ E.text "CARD HOLDER" ]
              , E.div_
                  [ E.style "font-size" "14px"
                  , E.style "font-weight" "500"
                  , E.style "letter-spacing" "1px"
                  ]
                  [ E.text displayName ]
              ]
          -- Expiry
          , E.div_ []
              [ E.div_
                  [ E.style "font-size" "10px"
                  , E.style "opacity" "0.7"
                  , E.style "margin-bottom" "4px"
                  ]
                  [ E.text "EXPIRES" ]
              , E.div_
                  [ E.style "font-size" "14px"
                  , E.style "font-weight" "500"
                  ]
                  [ E.text displayExp ]
              ]
          -- Brand
          , E.span_
              [ E.style "font-size" "20px"
              , E.style "font-weight" "bold"
              , E.style "opacity" "0.9"
              ]
              [ E.text (cardTypeName cfg.cardType) ]
          ]
      ]

-- | Render back of card preview.
renderCardBack
  :: forall msg r
   . { cvv :: String
     , cardType :: CardType
     | r
     }
  -> E.Element msg
renderCardBack cfg =
  let
    displayCvv = if cfg.cvv == "" then "•••" else cfg.cvv
    gradient = cardTypeGradientCss cfg.cardType
  in
    E.div_
      [ E.style "position" "absolute"
      , E.style "inset" "0"
      , E.style "border-radius" "12px"
      , E.style "background" gradient
      , E.style "backface-visibility" "hidden"
      , E.style "transform" "rotateY(180deg)"
      , E.style "box-shadow" "0 10px 40px rgba(0,0,0,0.3)"
      ]
      [ -- Magnetic stripe
        E.div_
          [ E.style "width" "100%"
          , E.style "height" "48px"
          , E.style "background" "#000"
          , E.style "margin-top" "24px"
          ]
          []
      -- CVV area
      , E.div_
          [ E.style "padding" "24px" ]
          [ E.div_
              [ E.style "font-size" "10px"
              , E.style "color" "rgba(255,255,255,0.7)"
              , E.style "margin-bottom" "4px"
              ]
              [ E.text "CVV" ]
          , E.div_
              [ E.style "background" "rgba(255,255,255,0.9)"
              , E.style "border-radius" "4px"
              , E.style "padding" "8px 12px"
              , E.style "text-align" "right"
              , E.style "font-family" "monospace"
              , E.style "color" "#1f2937"
              ]
              [ E.text displayCvv ]
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic credit card icon.
renderCardIcon :: forall msg. E.Element msg
renderCardIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "20"
    , E.attr "height" "20"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.style "color" "#9ca3af"
    ]
    [ E.rect_
        [ E.attr "width" "20"
        , E.attr "height" "14"
        , E.attr "x" "2"
        , E.attr "y" "5"
        , E.attr "rx" "2"
        ]
    , E.line_
        [ E.attr "x1" "2"
        , E.attr "y1" "10"
        , E.attr "x2" "22"
        , E.attr "y2" "10"
        ]
    ]

-- | Card brand logo (text-based).
renderCardBrandLogo :: forall msg. CardType -> E.Element msg
renderCardBrandLogo cardType =
  E.span_
    [ E.style "font-size" "12px"
    , E.style "font-weight" "bold"
    , E.style "color" "#6b7280"
    ]
    [ E.text (cardTypeName cardType) ]

-- | Question mark icon for CVV help.
renderQuestionIcon :: forall msg. E.Element msg
renderQuestionIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "16"
    , E.attr "height" "16"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.circle_
        [ E.attr "cx" "12"
        , E.attr "cy" "12"
        , E.attr "r" "10"
        ]
    , E.path_
        [ E.attr "d" "M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3" ]
    , E.line_
        [ E.attr "x1" "12"
        , E.attr "y1" "17"
        , E.attr "x2" "12.01"
        , E.attr "y2" "17"
        ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render field label.
renderFieldLabel :: forall msg. String -> E.Element msg
renderFieldLabel labelText =
  E.label_
    [ E.style "font-size" "14px"
    , E.style "font-weight" "500"
    , E.style "color" "#374151"
    ]
    [ E.text labelText ]

-- | Render field error message.
renderFieldError :: forall msg. Maybe String -> E.Element msg
renderFieldError maybeError = case maybeError of
  Nothing -> E.empty
  Just msg ->
    E.div_
      [ E.style "font-size" "12px"
      , E.style "color" "#ef4444"
      ]
      [ E.text msg ]

-- | Render input wrapper with relative positioning.
renderInputWrapper
  :: forall msg
   . Array (E.Attribute msg)
  -> Array (E.Element msg)
  -> E.Element msg
renderInputWrapper attrs children =
  E.div_
    ([ E.style "position" "relative" ] <> attrs)
    children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build disabled attributes array.
disabledAttrs :: forall msg. Boolean -> Array (E.Attribute msg)
disabledAttrs isDisabled =
  if isDisabled
    then
      [ E.disabled true
      , E.style "opacity" "0.5"
      , E.style "cursor" "not-allowed"
      , E.style "background-color" "#f3f4f6"
      ]
    else []

-- | Build input handler attributes.
inputHandlerAttrs :: forall msg. Maybe (String -> msg) -> Array (E.Attribute msg)
inputHandlerAttrs maybeHandler = case maybeHandler of
  Nothing -> []
  Just handler -> [ E.onInput handler ]

-- | Build focus handler attributes.
focusHandlerAttrs :: forall msg. Maybe msg -> Array (E.Attribute msg)
focusHandlerAttrs maybeHandler = case maybeHandler of
  Nothing -> []
  Just handler -> [ E.onFocus handler ]

-- | Build blur handler attributes.
blurHandlerAttrs :: forall msg. Maybe msg -> Array (E.Attribute msg)
blurHandlerAttrs maybeHandler = case maybeHandler of
  Nothing -> []
  Just handler -> [ E.onBlur handler ]

-- | Get CSS gradient for card type.
cardTypeGradientCss :: CardType -> String
cardTypeGradientCss Visa = "linear-gradient(135deg, #1e40af 0%, #1e3a8a 100%)"
cardTypeGradientCss Mastercard = "linear-gradient(135deg, #dc2626 0%, #ea580c 100%)"
cardTypeGradientCss Amex = "linear-gradient(135deg, #374151 0%, #111827 100%)"
cardTypeGradientCss Discover = "linear-gradient(135deg, #f97316 0%, #ea580c 100%)"
cardTypeGradientCss DinersClub = "linear-gradient(135deg, #4b5563 0%, #1f2937 100%)"
cardTypeGradientCss JCB = "linear-gradient(135deg, #059669 0%, #047857 100%)"
cardTypeGradientCss UnionPay = "linear-gradient(135deg, #dc2626 0%, #991b1b 100%)"
cardTypeGradientCss Unknown = "linear-gradient(135deg, #4b5563 0%, #1f2937 100%)"
