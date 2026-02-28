-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // otpinput // digit
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Digit — Single digit input rendering.
-- |
-- | ## Design Philosophy
-- |
-- | Each OTP digit is rendered as an individual input element. This module
-- | handles the visual representation with Schema-native styling:
-- |
-- | - Border states (default, focused, filled, error, success)
-- | - Text display (digit, masked dot, placeholder)
-- | - Focus ring effects
-- | - Disabled state styling
-- |
-- | ## Dependencies
-- |
-- | - Types module for OTPDigit, OTPIndex, OTPState
-- | - Props module for OTPInputProps
-- | - Validation module for input patterns
-- | - Element module for rendering

module Hydrogen.Element.Compound.OTPInput.Digit
  ( -- * Digit Rendering
    renderDigit
  , renderDigitInput
  
  -- * Style Computation
  , getDigitBorderColor
  , getDigitBackgroundColor
  , getDigitBackgroundStyle
  , getDigitTextColor
  , getDefaultBorderColor
  , getDefaultTextColor
  , getFocusRingStyle
  , getDigitShadow
  , getDigitTransform
  , getTransitionStyle
  
  -- * State Helpers
  , isDigitFocused
  , isDigitFilled
  , getDigitDisplayValue
  ) where

import Prelude
  ( show
  , (==)
  , (<>)
  , (+)
  , not
  )

import Data.Maybe (Maybe(Nothing, Just))
import Data.String.CodeUnits as SCU

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.Gradient as Gradient
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Geometry.Transform as Transform
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Motion.Easing as Easing
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Typography.FontFamily as FontFamily

import Hydrogen.Element.Compound.OTPInput.Types
  ( OTPDigit(OTPDigit)
  , OTPIndex
  , OTPState(Idle, Entering, Verifying, Success, Error)
  , unwrapOTPIndex
  , unwrapDigitCount
  , getDigitAt
  , otpIndex
  )

import Hydrogen.Element.Compound.OTPInput.Props
  ( OTPInputProps
  )

import Hydrogen.Element.Compound.OTPInput.Validation
  ( getInputMode
  , getInputPattern
  , getAutoComplete
  )

import Hydrogen.Element.Compound.OTPInput.Animation
  ( computeDigitAnimationState
  , getAnimationDataAttrs
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // digit rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single OTP digit at the given index.
-- | This is the main entry point for digit rendering.
renderDigit :: forall msg. OTPInputProps msg -> Int -> E.Element msg
renderDigit props idx =
  let
    boundedIndex = otpIndex props.digitCount idx
    digit = getDigitAt boundedIndex props.value
    isFocused = isDigitFocused props boundedIndex
    hasFill = isDigitFilled digit
    displayValue = getDigitDisplayValue props.masked props.placeholderChar digit
  in
    renderDigitInput props boundedIndex digit isFocused hasFill displayValue

-- | Render the actual input element for a digit
renderDigitInput 
  :: forall msg
   . OTPInputProps msg 
  -> OTPIndex 
  -> OTPDigit 
  -> Boolean 
  -> Boolean 
  -> String 
  -> E.Element msg
renderDigitInput props idx digit isFocused hasFill displayValue =
  let
    idxInt = unwrapOTPIndex idx
    totalDigits = unwrapDigitCount props.digitCount
    
    -- Compute animation state and get pure animation data
    animState = computeDigitAnimationState props.state digit hasFill
    animationDataAttrs = getAnimationDataAttrs props animState
    
    -- Event handlers - only attach if provided
    inputHandler = case props.onDigitInput of
      Nothing -> []
      Just handler -> [ E.onInput (\value -> handler idx (getFirstChar value)) ]
    
    keyDownHandler = case props.onDigitKeyDown of
      Nothing -> []
      Just handler -> [ E.onKeyDown (\key -> handler idx key) ]
    
    focusHandler = case props.onDigitFocus of
      Nothing -> []
      Just handler -> [ E.onFocus (handler idx) ]
    
    blurHandler = case props.onDigitBlur of
      Nothing -> []
      Just handler -> [ E.onBlur (handler idx) ]
  in
    E.input_
      ( [ -- Core attributes
          E.type_ "text"
        , E.value displayValue
        , E.disabled props.disabled
        , E.attr "maxlength" "1"
        , E.attr "inputmode" (getInputMode props.inputType)
        , E.attr "pattern" (getInputPattern props.inputType)
        , E.attr "autocomplete" getAutoComplete
        , E.dataAttr "otp-index" (show idxInt)
        
        -- Accessibility
        , E.ariaLabel ("Digit " <> show (idxInt + 1) <> " of " <> show totalDigits)
        , E.role "textbox"
        
        -- Core styles
        , E.style "width" (getDigitWidth props)
        , E.style "height" (getDigitHeight props)
        , E.style "text-align" "center"
        , E.style "font-size" (getFontSize props)
        , E.style "font-weight" (getFontWeight props)
        , E.style "font-family" (getFontFamily props)
        , E.style "letter-spacing" (getLetterSpacing props)
        , E.style "border-style" "solid"
        , E.style "border-width" (getBorderWidth props)
        , E.style "border-radius" (getBorderRadius props)
        , E.style "outline" "none"
        , E.style "transition" (getTransitionStyle props)
        , E.style "caret-color" "transparent"
        
        -- Computed styles based on state
        , E.style "border-color" (getDigitBorderColor props hasFill isFocused)
        , E.style "background" (getDigitBackgroundStyle props isFocused)
        , E.style "color" (getDigitTextColor props hasFill)
        , E.style "box-shadow" (getDigitShadow props isFocused false)
        , E.style "transform" (getDigitTransform props isFocused false false)
        ]
        <> inputHandler
        <> keyDownHandler
        <> focusHandler
        <> blurHandler
        <> animationDataAttrs
        <> getFocusRingStyle props isFocused
        <> getDisabledStyles props
      )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // style computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get border color based on component state and digit state
-- | Priority: focus > error > success > filled > default
-- |
-- | All OTPState variants handled explicitly for exhaustiveness.
getDigitBorderColor :: forall msg. OTPInputProps msg -> Boolean -> Boolean -> String
getDigitBorderColor props hasFill isFocused =
  if isFocused
    then case props.focusBorderColor of
           Just c -> Color.toLegacyCss c
           Nothing -> "#3b82f6"  -- blue-500 default
    else case props.state of
      Error ->
        case props.errorBorderColor of
          Just c -> Color.toLegacyCss c
          Nothing -> "#ef4444"  -- red-500 default
      Success ->
        case props.successBorderColor of
          Just c -> Color.toLegacyCss c
          Nothing -> "#22c55e"  -- green-500 default
      Verifying ->
        case props.borderColor of
          Just c -> Color.toLegacyCss c
          Nothing -> "#e2e8f0"  -- slate-200 default
      Idle ->
        getDefaultBorderColor props hasFill
      Entering ->
        getDefaultBorderColor props hasFill

-- | Get default border color (filled vs empty)
getDefaultBorderColor :: forall msg. OTPInputProps msg -> Boolean -> String
getDefaultBorderColor props hasFill =
  if hasFill
    then case props.filledBorderColor of
           Just c -> Color.toLegacyCss c
           Nothing -> "#3b82f6"  -- blue-500 default
    else case props.borderColor of
           Just c -> Color.toLegacyCss c
           Nothing -> "#e2e8f0"  -- slate-200 default

-- | Get digit background color
getDigitBackgroundColor :: forall msg. OTPInputProps msg -> String
getDigitBackgroundColor props =
  case props.backgroundColor of
    Just c -> Color.toLegacyCss c
    Nothing -> "#ffffff"

-- | Get digit text color
-- |
-- | If hasFill is false and placeholderChar is set, uses placeholderColor.
-- | All OTPState variants handled explicitly for exhaustiveness.
getDigitTextColor :: forall msg. OTPInputProps msg -> Boolean -> String
getDigitTextColor props hasFill =
  -- If showing placeholder (no fill), use placeholder color
  if not hasFill
    then case props.placeholderColor of
      Just c -> Color.toLegacyCss c
      Nothing -> getDefaultTextColor props
    else case props.state of
      Error ->
        case props.errorTextColor of
          Just c -> Color.toLegacyCss c
          Nothing -> getDefaultTextColor props
      Success ->
        case props.successTextColor of
          Just c -> Color.toLegacyCss c
          Nothing -> getDefaultTextColor props
      Verifying ->
        getDefaultTextColor props
      Idle ->
        getDefaultTextColor props
      Entering ->
        getDefaultTextColor props

-- | Get default text color
getDefaultTextColor :: forall msg. OTPInputProps msg -> String
getDefaultTextColor props =
  case props.textColor of
    Just c -> Color.toLegacyCss c
    Nothing -> "#0f172a"  -- slate-900 default

-- | Get focus ring style attributes
getFocusRingStyle :: forall msg. OTPInputProps msg -> Boolean -> Array (E.Attribute msg)
getFocusRingStyle props isFocused =
  if isFocused
    then
      let ringColor = case props.focusBorderColor of
                        Just c -> Color.toLegacyCss c
                        Nothing -> "#3b82f6"
      in [ E.style "box-shadow" ("0 0 0 3px " <> ringColor <> "33") ]  -- 33 = 20% opacity
    else []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // state helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if this digit is currently focused
isDigitFocused :: forall msg. OTPInputProps msg -> OTPIndex -> Boolean
isDigitFocused props idx =
  case props.focusedIndex of
    Nothing -> false
    Just focusedIdx -> focusedIdx == idx

-- | Check if a digit has a value
isDigitFilled :: OTPDigit -> Boolean
isDigitFilled (OTPDigit Nothing) = false
isDigitFilled (OTPDigit (Just _)) = true

-- | Get display value for a digit (handles masking and placeholder)
getDigitDisplayValue :: Boolean -> Maybe Char -> OTPDigit -> String
getDigitDisplayValue _ placeholder (OTPDigit Nothing) = 
  case placeholder of
    Nothing -> ""
    Just p -> SCU.singleton p
getDigitDisplayValue masked _ (OTPDigit (Just c)) =
  if masked
    then "•"
    else SCU.singleton c

-- | Get first character from input value string
getFirstChar :: String -> Char
getFirstChar str =
  case SCU.uncons str of
    Nothing -> ' '
    Just { head } -> head

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // dimension helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get digit width CSS value
getDigitWidth :: forall msg. OTPInputProps msg -> String
getDigitWidth props =
  case props.digitWidth of
    Just w -> show w
    Nothing -> "48px"

-- | Get digit height CSS value
getDigitHeight :: forall msg. OTPInputProps msg -> String
getDigitHeight props =
  case props.digitHeight of
    Just h -> show h
    Nothing -> "56px"

-- | Get font size CSS value
getFontSize :: forall msg. OTPInputProps msg -> String
getFontSize props =
  case props.fontSize of
    Just s -> FontSize.toLegacyCss s
    Nothing -> "20px"

-- | Get font weight CSS value (using Schema.Typography.FontWeight)
getFontWeight :: forall msg. OTPInputProps msg -> String
getFontWeight props =
  case props.fontWeight of
    Just w -> FontWeight.toLegacyCss w
    Nothing -> "600"

-- | Get font family CSS value
getFontFamily :: forall msg. OTPInputProps msg -> String
getFontFamily props =
  case props.fontFamily of
    Just f -> FontFamily.toLegacyCss f
    Nothing -> "inherit"

-- | Get letter spacing CSS value
getLetterSpacing :: forall msg. OTPInputProps msg -> String
getLetterSpacing props =
  case props.letterSpacing of
    Just s -> show s
    Nothing -> "normal"

-- | Get border width CSS value
getBorderWidth :: forall msg. OTPInputProps msg -> String
getBorderWidth props =
  case props.borderWidth of
    Just w -> show w
    Nothing -> "2px"

-- | Get border radius CSS value
getBorderRadius :: forall msg. OTPInputProps msg -> String
getBorderRadius props =
  case props.borderRadius of
    Just r -> Geometry.toLegacyCss r
    Nothing -> "8px"

-- | Get disabled state styles
getDisabledStyles :: forall msg. OTPInputProps msg -> Array (E.Attribute msg)
getDisabledStyles props =
  if props.disabled
    then 
      [ E.style "opacity" "0.5"
      , E.style "cursor" "not-allowed"
      ]
    else [ E.style "cursor" props.cursorStyle ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // advanced rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get digit background style (solid color or gradient)
-- |
-- | Gradient takes precedence over solid color when both are provided.
getDigitBackgroundStyle :: forall msg. OTPInputProps msg -> Boolean -> String
getDigitBackgroundStyle props isFocused =
  -- Check for focus gradient first
  if isFocused
    then case props.focusBackgroundGradient of
           Just g -> Gradient.toLegacyCss g
           Nothing -> case props.focusBackgroundColor of
                        Just c -> Color.toLegacyCss c
                        Nothing -> getBackgroundFallback props
    else getBackgroundFallback props
  where
    getBackgroundFallback p = case p.backgroundGradient of
      Just g -> Gradient.toLegacyCss g
      Nothing -> getDigitBackgroundColor p

-- | Get digit shadow based on state
-- |
-- | All OTPState variants handled explicitly for exhaustiveness.
getDigitShadow :: forall msg. OTPInputProps msg -> Boolean -> Boolean -> String
getDigitShadow props isFocused isHovered =
  if isFocused
    then case props.focusShadow of
           Just s -> Shadow.layeredToLegacyCss s
           Nothing -> case props.shadow of
                        Just s -> Shadow.layeredToLegacyCss s
                        Nothing -> "none"
    else case props.state of
      Error ->
        case props.errorShadow of
          Just s -> Shadow.layeredToLegacyCss s
          Nothing -> "none"
      Success ->
        case props.successShadow of
          Just s -> Shadow.layeredToLegacyCss s
          Nothing -> "none"
      Verifying ->
        getDefaultShadow props isHovered
      Idle ->
        getDefaultShadow props isHovered
      Entering ->
        getDefaultShadow props isHovered
  where
    getDefaultShadow p hovered =
      if hovered
        then case p.hoverShadow of
               Just s -> Shadow.layeredToLegacyCss s
               Nothing -> case p.shadow of
                            Just s -> Shadow.layeredToLegacyCss s
                            Nothing -> "none"
        else case p.shadow of
               Just s -> Shadow.layeredToLegacyCss s
               Nothing -> "none"

-- | Get digit transform based on state
-- |
-- | All OTPState variants handled explicitly for exhaustiveness.
getDigitTransform :: forall msg. OTPInputProps msg -> Boolean -> Boolean -> Boolean -> String
getDigitTransform props isFocused isHovered isPressed =
  if isPressed
    then case props.pressScale of
           Just s -> Transform.scaleToLegacyCss s
           Nothing -> "scale(0.98)"
    else if isFocused
      then case props.focusScale of
             Just s -> Transform.scaleToLegacyCss s
             Nothing -> "scale(1)"
      else if isHovered
        then case props.hoverScale of
               Just s -> Transform.scaleToLegacyCss s
               Nothing -> "scale(1)"
        else "scale(1)"

-- | Get transition style using Schema temporal/easing atoms
getTransitionStyle :: forall msg. OTPInputProps msg -> String
getTransitionStyle props =
  let
    duration = show props.transitionDuration
    easing = Easing.toLegacyCssString props.transitionEasing
    transitionValue = 
      "border-color " <> duration <> " " <> easing <>
      ", background-color " <> duration <> " " <> easing <>
      ", box-shadow " <> duration <> " " <> easing <>
      ", transform " <> duration <> " " <> easing <>
      ", background " <> duration <> " " <> easing
  in
    transitionValue


