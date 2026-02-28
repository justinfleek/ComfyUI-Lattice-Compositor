-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // otpinput // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Props — Complete Schema-native property system.
-- |
-- | ## Design Philosophy
-- |
-- | Props are the bridge between user configuration and component rendering.
-- | Every visual property maps to a Schema pillar atom — no escape hatches.
-- |
-- | ## Schema Pillars Used
-- |
-- | | Pillar     | Atoms                                        |
-- | |------------|----------------------------------------------|
-- | | Color      | RGB, Gradient                                |
-- | | Dimension  | Pixel, Temporal (Milliseconds)               |
-- | | Geometry   | Radius, Transform (Scale)                    |
-- | | Typography | FontSize, FontWeight, FontFamily             |
-- | | Elevation  | Shadow (LayeredShadow)                       |
-- | | Motion     | Easing, Transition                           |
-- | | Attestation| UUID5 (instance identity)                    |
-- |
-- | ## Prop Modifier Pattern
-- |
-- | Components accept `Array (OTPInputProp msg)` which fold over `defaultProps`.

module Hydrogen.Element.Compound.OTPInput.Props
  ( -- * Props Record
    OTPInputProps
  , OTPInputProp
  , defaultProps
  
  -- * Content Props
  , digitCountProp
  , otpValueProp
  , otpInputTypeProp
  , maskedProp
  , disabledProp
  , stateProp
  , errorMessageProp
  , successMessageProp
  , helpTextProp
  , labelProp
  , focusedIndexProp
  , resendCooldownProp
  , resendRemainingProp
  , instanceIdProp
  
  -- * Color Atoms
  , backgroundColorProp
  , borderColorProp
  , focusBorderColorProp
  , hoverBorderColorProp
  , errorBorderColorProp
  , successBorderColorProp
  , filledBorderColorProp
  , textColorProp
  , placeholderColorProp
  , placeholderCharProp
  , errorTextColorProp
  , successTextColorProp
  , mutedTextColorProp
  , primaryColorProp
  , focusBackgroundColorProp
  , hoverBackgroundColorProp
  
  -- * Gradient Atoms
  , backgroundGradientProp
  , focusBackgroundGradientProp
  
  -- * Elevation Atoms (Shadows)
  , shadowProp
  , focusShadowProp
  , hoverShadowProp
  , errorShadowProp
  , successShadowProp
  
  -- * Geometry Atoms
  , borderRadiusProp
  , borderWidthProp
  , focusScaleProp
  , hoverScaleProp
  , pressScaleProp
  
  -- * Dimension Atoms
  , digitWidthProp
  , digitHeightProp
  , gapProp
  , separatorWidthProp
  
  -- * Typography Atoms
  , fontSizeProp
  , fontWeightProp
  , fontFamilyProp
  , letterSpacingProp
  
  -- * Behavior Props
  , onDigitChangeProp
  , onCompleteProp
  , onResendClickProp
  , onFocusProp
  , onBlurProp
  , onPasteProp
  , onDigitInputProp
  , onDigitDeleteProp
  , onDigitKeyDownProp
  , onDigitFocusProp
  , onDigitBlurProp
  , autoSubmitProp
  , autoFocusProp
  
  -- * Animation Props (Schema Temporal/Motion)
  , animationEnabledProp
  , reducedMotionProp
  , shakeDurationProp
  , pulseDurationProp
  , entryDurationProp
  , transitionDurationProp
  , transitionEasingProp
  , staggerDelayProp
  
  -- * Separator Props
  , separatorEnabledProp
  , separatorPositionsProp
  , separatorCharProp
  , separatorColorProp
  
  -- * Label and Behavior Props
  , labelColorProp
  , autoAdvanceProp
  
  -- * Cursor Props
  , cursorStyleProp
  ) where

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Element.Compound.OTPInput.Types
  ( OTPDigitCount
  , OTPInputType(Numeric)
  , OTPValue
  , OTPIndex
  , OTPState(Idle)
  , emptyOTP
  , digitCount
  )

import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.Gradient as Gradient
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Geometry.Transform as Transform
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Motion.Easing as Easing
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Typography.FontFamily as FontFamily
import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // props record
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete OTP input configuration using Schema atoms.
-- |
-- | All visual properties are typed Schema atoms. No strings for colors, sizes.
-- | Instance identity via UUID5 ensures uniqueness at billion-agent scale.
type OTPInputProps msg =
  { -- Content (bounded types from Types module)
    digitCount :: OTPDigitCount
  , value :: OTPValue
  , inputType :: OTPInputType
  , masked :: Boolean
  , disabled :: Boolean
  , state :: OTPState
  , errorMessage :: Maybe String
  , successMessage :: Maybe String
  , helpText :: Maybe String
  , label :: Maybe String
  , focusedIndex :: Maybe OTPIndex
  , resendCooldown :: Int
  , resendRemaining :: Int
  , instanceId :: Maybe UUID5.UUID5
  
  -- Color atoms (Schema.Color.RGB)
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , hoverBorderColor :: Maybe Color.RGB
  , errorBorderColor :: Maybe Color.RGB
  , successBorderColor :: Maybe Color.RGB
  , filledBorderColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , placeholderChar :: Maybe Char
  , errorTextColor :: Maybe Color.RGB
  , successTextColor :: Maybe Color.RGB
  , mutedTextColor :: Maybe Color.RGB
  , primaryColor :: Maybe Color.RGB
  , focusBackgroundColor :: Maybe Color.RGB
  , hoverBackgroundColor :: Maybe Color.RGB
  
  -- Gradient atoms (Schema.Color.Gradient)
  , backgroundGradient :: Maybe Gradient.Gradient
  , focusBackgroundGradient :: Maybe Gradient.Gradient
  
  -- Elevation atoms (Schema.Elevation.Shadow)
  , shadow :: Maybe Shadow.LayeredShadow
  , focusShadow :: Maybe Shadow.LayeredShadow
  , hoverShadow :: Maybe Shadow.LayeredShadow
  , errorShadow :: Maybe Shadow.LayeredShadow
  , successShadow :: Maybe Shadow.LayeredShadow
  
  -- Geometry atoms (Schema.Geometry)
  , borderRadius :: Maybe Geometry.Radius
  , borderWidth :: Maybe Device.Pixel
  , focusScale :: Maybe Transform.Scale
  , hoverScale :: Maybe Transform.Scale
  , pressScale :: Maybe Transform.Scale
  
  -- Dimension atoms (Schema.Dimension.Device)
  , digitWidth :: Maybe Device.Pixel
  , digitHeight :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  , separatorWidth :: Maybe Device.Pixel
  
  -- Typography atoms (Schema.Typography)
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe FontWeight.FontWeight
  , fontFamily :: Maybe FontFamily.FontFamily
  , letterSpacing :: Maybe Device.Pixel
  
  -- Behavior handlers
  , onDigitChange :: Maybe (OTPValue -> msg)
  , onComplete :: Maybe (OTPValue -> msg)
  , onResendClick :: Maybe msg
  , onFocus :: Maybe (OTPIndex -> msg)
  , onBlur :: Maybe (OTPIndex -> msg)
  , onPaste :: Maybe (String -> msg)
  
  -- Raw event handlers (more granular control)
  , onDigitInput :: Maybe (OTPIndex -> Char -> msg)
  , onDigitDelete :: Maybe (OTPIndex -> msg)
  , onDigitKeyDown :: Maybe (OTPIndex -> String -> msg)
  , onDigitFocus :: Maybe (OTPIndex -> msg)
  , onDigitBlur :: Maybe (OTPIndex -> msg)
  
  -- Behavior flags
  , autoSubmit :: Boolean
  , autoFocus :: Boolean
  
  -- Animation configuration (Schema.Dimension.Temporal, Schema.Motion.Easing)
  , animationEnabled :: Boolean
  , reducedMotion :: Boolean
  , shakeDuration :: Temporal.Milliseconds
  , pulseDuration :: Temporal.Milliseconds
  , entryDuration :: Temporal.Milliseconds
  , transitionDuration :: Temporal.Milliseconds
  , transitionEasing :: Easing.Easing
  , staggerDelay :: Temporal.Milliseconds
  
  -- Separator configuration (for XXX-XXX patterns)
  , separatorEnabled :: Boolean
  , separatorPositions :: Array Int
  , separatorChar :: Char
  , separatorColor :: Maybe Color.RGB
  
  -- Label and help text colors
  , labelColor :: Maybe Color.RGB
  
  -- Auto-advance behavior (focus moves to next digit automatically)
  , autoAdvance :: Boolean
  
  -- Cursor configuration
  , cursorStyle :: String
  }

-- | Property modifier function
type OTPInputProp msg = OTPInputProps msg -> OTPInputProps msg

-- | Default properties with sensible Schema values.
-- |
-- | Uses 6 digits (standard TOTP), empty value, numeric input.
-- | All durations use Schema.Dimension.Temporal.Milliseconds.
defaultProps :: forall msg. OTPInputProps msg
defaultProps =
  { -- Content
    digitCount: digitCount 6
  , value: emptyOTP (digitCount 6)
  , inputType: Numeric
  , masked: false
  , disabled: false
  , state: Idle
  , errorMessage: Nothing
  , successMessage: Nothing
  , helpText: Nothing
  , label: Nothing
  , focusedIndex: Nothing
  , resendCooldown: 60
  , resendRemaining: 0
  , instanceId: Nothing
  
  -- Colors (Nothing = use theme defaults at render time)
  , backgroundColor: Nothing
  , borderColor: Nothing
  , focusBorderColor: Nothing
  , hoverBorderColor: Nothing
  , errorBorderColor: Nothing
  , successBorderColor: Nothing
  , filledBorderColor: Nothing
  , textColor: Nothing
  , placeholderColor: Nothing
  , placeholderChar: Nothing
  , errorTextColor: Nothing
  , successTextColor: Nothing
  , mutedTextColor: Nothing
  , primaryColor: Nothing
  , focusBackgroundColor: Nothing
  , hoverBackgroundColor: Nothing
  
  -- Gradients
  , backgroundGradient: Nothing
  , focusBackgroundGradient: Nothing
  
  -- Shadows/Elevation
  , shadow: Nothing
  , focusShadow: Nothing
  , hoverShadow: Nothing
  , errorShadow: Nothing
  , successShadow: Nothing
  
  -- Geometry
  , borderRadius: Nothing
  , borderWidth: Nothing
  , focusScale: Nothing
  , hoverScale: Nothing
  , pressScale: Nothing
  
  -- Dimensions
  , digitWidth: Nothing
  , digitHeight: Nothing
  , gap: Nothing
  , separatorWidth: Nothing
  
  -- Typography
  , fontSize: Nothing
  , fontWeight: Nothing
  , fontFamily: Nothing
  , letterSpacing: Nothing
  
  -- Behavior
  , onDigitChange: Nothing
  , onComplete: Nothing
  , onResendClick: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , onPaste: Nothing
  , onDigitInput: Nothing
  , onDigitDelete: Nothing
  , onDigitKeyDown: Nothing
  , onDigitFocus: Nothing
  , onDigitBlur: Nothing
  , autoSubmit: false
  , autoFocus: false
  
  -- Animation (using proper Schema temporal types)
  , animationEnabled: true
  , reducedMotion: false
  , shakeDuration: Temporal.ms 500.0
  , pulseDuration: Temporal.ms 300.0
  , entryDuration: Temporal.ms 150.0
  , transitionDuration: Temporal.ms 150.0
  , transitionEasing: Easing.easeOut
  , staggerDelay: Temporal.ms 50.0
  
  -- Separator
  , separatorEnabled: false
  , separatorPositions: []
  , separatorChar: '-'
  , separatorColor: Nothing
  
  -- Label and help text colors
  , labelColor: Nothing
  
  -- Auto-advance (default true for typical OTP UX)
  , autoAdvance: true
  
  -- Cursor
  , cursorStyle: "text"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // content prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set number of OTP digits (4-8)
digitCountProp :: forall msg. OTPDigitCount -> OTPInputProp msg
digitCountProp n props = props { digitCount = n }

-- | Set current OTP value
otpValueProp :: forall msg. OTPValue -> OTPInputProp msg
otpValueProp v props = props { value = v }

-- | Set input type (numeric or alphanumeric)
otpInputTypeProp :: forall msg. OTPInputType -> OTPInputProp msg
otpInputTypeProp t props = props { inputType = t }

-- | Enable/disable input masking (dots instead of characters)
maskedProp :: forall msg. Boolean -> OTPInputProp msg
maskedProp m props = props { masked = m }

-- | Enable/disable the entire input
disabledProp :: forall msg. Boolean -> OTPInputProp msg
disabledProp d props = props { disabled = d }

-- | Set component state (Idle, Entering, Verifying, Success, Error)
stateProp :: forall msg. OTPState -> OTPInputProp msg
stateProp s props = props { state = s }

-- | Set error message text
errorMessageProp :: forall msg. String -> OTPInputProp msg
errorMessageProp m props = props { errorMessage = Just m }

-- | Set success message text
successMessageProp :: forall msg. String -> OTPInputProp msg
successMessageProp m props = props { successMessage = Just m }

-- | Set help text (e.g., "Code sent to ***1234")
helpTextProp :: forall msg. String -> OTPInputProp msg
helpTextProp t props = props { helpText = Just t }

-- | Set label text
labelProp :: forall msg. String -> OTPInputProp msg
labelProp l props = props { label = Just l }

-- | Set currently focused digit index
focusedIndexProp :: forall msg. OTPIndex -> OTPInputProp msg
focusedIndexProp i props = props { focusedIndex = Just i }

-- | Set resend cooldown duration in seconds
resendCooldownProp :: forall msg. Int -> OTPInputProp msg
resendCooldownProp c props = props { resendCooldown = c }

-- | Set remaining resend cooldown time in seconds
resendRemainingProp :: forall msg. Int -> OTPInputProp msg
resendRemainingProp r props = props { resendRemaining = r }

-- | Set instance ID (UUID5) for deterministic identity
instanceIdProp :: forall msg. UUID5.UUID5 -> OTPInputProp msg
instanceIdProp id props = props { instanceId = Just id }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // color prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set digit input background color
backgroundColorProp :: forall msg. Color.RGB -> OTPInputProp msg
backgroundColorProp c props = props { backgroundColor = Just c }

-- | Set default digit border color
borderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
borderColorProp c props = props { borderColor = Just c }

-- | Set focused digit border color
focusBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
focusBorderColorProp c props = props { focusBorderColor = Just c }

-- | Set hovered digit border color
hoverBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
hoverBorderColorProp c props = props { hoverBorderColor = Just c }

-- | Set error state border color
errorBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
errorBorderColorProp c props = props { errorBorderColor = Just c }

-- | Set success state border color
successBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
successBorderColorProp c props = props { successBorderColor = Just c }

-- | Set filled (has value) digit border color
filledBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
filledBorderColorProp c props = props { filledBorderColor = Just c }

-- | Set digit text color
textColorProp :: forall msg. Color.RGB -> OTPInputProp msg
textColorProp c props = props { textColor = Just c }

-- | Set placeholder/empty digit color
placeholderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
placeholderColorProp c props = props { placeholderColor = Just c }

-- | Set placeholder character (e.g., '-' or '•')
placeholderCharProp :: forall msg. Char -> OTPInputProp msg
placeholderCharProp c props = props { placeholderChar = Just c }

-- | Set error message text color
errorTextColorProp :: forall msg. Color.RGB -> OTPInputProp msg
errorTextColorProp c props = props { errorTextColor = Just c }

-- | Set success message text color
successTextColorProp :: forall msg. Color.RGB -> OTPInputProp msg
successTextColorProp c props = props { successTextColor = Just c }

-- | Set muted/secondary text color
mutedTextColorProp :: forall msg. Color.RGB -> OTPInputProp msg
mutedTextColorProp c props = props { mutedTextColor = Just c }

-- | Set primary/accent color
primaryColorProp :: forall msg. Color.RGB -> OTPInputProp msg
primaryColorProp c props = props { primaryColor = Just c }

-- | Set focused digit background color
focusBackgroundColorProp :: forall msg. Color.RGB -> OTPInputProp msg
focusBackgroundColorProp c props = props { focusBackgroundColor = Just c }

-- | Set hovered digit background color
hoverBackgroundColorProp :: forall msg. Color.RGB -> OTPInputProp msg
hoverBackgroundColorProp c props = props { hoverBackgroundColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // gradient prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background gradient (takes precedence over solid color)
backgroundGradientProp :: forall msg. Gradient.Gradient -> OTPInputProp msg
backgroundGradientProp g props = props { backgroundGradient = Just g }

-- | Set focused digit background gradient
focusBackgroundGradientProp :: forall msg. Gradient.Gradient -> OTPInputProp msg
focusBackgroundGradientProp g props = props { focusBackgroundGradient = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // elevation prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set digit box shadow
shadowProp :: forall msg. Shadow.LayeredShadow -> OTPInputProp msg
shadowProp s props = props { shadow = Just s }

-- | Set focused digit box shadow (focus ring effect)
focusShadowProp :: forall msg. Shadow.LayeredShadow -> OTPInputProp msg
focusShadowProp s props = props { focusShadow = Just s }

-- | Set hovered digit box shadow
hoverShadowProp :: forall msg. Shadow.LayeredShadow -> OTPInputProp msg
hoverShadowProp s props = props { hoverShadow = Just s }

-- | Set error state box shadow (red glow)
errorShadowProp :: forall msg. Shadow.LayeredShadow -> OTPInputProp msg
errorShadowProp s props = props { errorShadow = Just s }

-- | Set success state box shadow (green glow)
successShadowProp :: forall msg. Shadow.LayeredShadow -> OTPInputProp msg
successShadowProp s props = props { successShadow = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // geometry prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set digit border radius
borderRadiusProp :: forall msg. Geometry.Radius -> OTPInputProp msg
borderRadiusProp r props = props { borderRadius = Just r }

-- | Set digit border width
borderWidthProp :: forall msg. Device.Pixel -> OTPInputProp msg
borderWidthProp w props = props { borderWidth = Just w }

-- | Set focused digit scale transform
focusScaleProp :: forall msg. Transform.Scale -> OTPInputProp msg
focusScaleProp s props = props { focusScale = Just s }

-- | Set hovered digit scale transform
hoverScaleProp :: forall msg. Transform.Scale -> OTPInputProp msg
hoverScaleProp s props = props { hoverScale = Just s }

-- | Set pressed digit scale transform
pressScaleProp :: forall msg. Transform.Scale -> OTPInputProp msg
pressScaleProp s props = props { pressScale = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // dimension prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set digit input width
digitWidthProp :: forall msg. Device.Pixel -> OTPInputProp msg
digitWidthProp w props = props { digitWidth = Just w }

-- | Set digit input height
digitHeightProp :: forall msg. Device.Pixel -> OTPInputProp msg
digitHeightProp h props = props { digitHeight = Just h }

-- | Set gap between digit inputs
gapProp :: forall msg. Device.Pixel -> OTPInputProp msg
gapProp g props = props { gap = Just g }

-- | Set separator element width
separatorWidthProp :: forall msg. Device.Pixel -> OTPInputProp msg
separatorWidthProp w props = props { separatorWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // typography prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set digit font size
fontSizeProp :: forall msg. FontSize.FontSize -> OTPInputProp msg
fontSizeProp s props = props { fontSize = Just s }

-- | Set digit font weight (Schema.Typography.FontWeight)
fontWeightProp :: forall msg. FontWeight.FontWeight -> OTPInputProp msg
fontWeightProp w props = props { fontWeight = Just w }

-- | Set digit font family
fontFamilyProp :: forall msg. FontFamily.FontFamily -> OTPInputProp msg
fontFamilyProp f props = props { fontFamily = Just f }

-- | Set digit letter spacing
letterSpacingProp :: forall msg. Device.Pixel -> OTPInputProp msg
letterSpacingProp s props = props { letterSpacing = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // behavior prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set handler for OTP value changes
onDigitChangeProp :: forall msg. (OTPValue -> msg) -> OTPInputProp msg
onDigitChangeProp handler props = props { onDigitChange = Just handler }

-- | Set handler for OTP completion (all digits filled)
onCompleteProp :: forall msg. (OTPValue -> msg) -> OTPInputProp msg
onCompleteProp handler props = props { onComplete = Just handler }

-- | Set handler for resend button click
onResendClickProp :: forall msg. msg -> OTPInputProp msg
onResendClickProp handler props = props { onResendClick = Just handler }

-- | Set handler for digit focus
onFocusProp :: forall msg. (OTPIndex -> msg) -> OTPInputProp msg
onFocusProp handler props = props { onFocus = Just handler }

-- | Set handler for digit blur
onBlurProp :: forall msg. (OTPIndex -> msg) -> OTPInputProp msg
onBlurProp handler props = props { onBlur = Just handler }

-- | Set handler for paste events
onPasteProp :: forall msg. (String -> msg) -> OTPInputProp msg
onPasteProp handler props = props { onPaste = Just handler }

-- | Set handler for digit input (character entered)
-- | Called with (index, character) when a character is entered
onDigitInputProp :: forall msg. (OTPIndex -> Char -> msg) -> OTPInputProp msg
onDigitInputProp handler props = props { onDigitInput = Just handler }

-- | Set handler for digit delete (backspace)
-- | Called with index when backspace is pressed at that digit
onDigitDeleteProp :: forall msg. (OTPIndex -> msg) -> OTPInputProp msg
onDigitDeleteProp handler props = props { onDigitDelete = Just handler }

-- | Set handler for digit keydown (any key)
-- | Called with (index, keyCode) for any keypress
onDigitKeyDownProp :: forall msg. (OTPIndex -> String -> msg) -> OTPInputProp msg
onDigitKeyDownProp handler props = props { onDigitKeyDown = Just handler }

-- | Set handler for digit focus (explicit)
onDigitFocusProp :: forall msg. (OTPIndex -> msg) -> OTPInputProp msg
onDigitFocusProp handler props = props { onDigitFocus = Just handler }

-- | Set handler for digit blur (explicit)
onDigitBlurProp :: forall msg. (OTPIndex -> msg) -> OTPInputProp msg
onDigitBlurProp handler props = props { onDigitBlur = Just handler }

-- | Enable auto-submit on completion
autoSubmitProp :: forall msg. Boolean -> OTPInputProp msg
autoSubmitProp enabled props = props { autoSubmit = enabled }

-- | Enable auto-focus on mount
autoFocusProp :: forall msg. Boolean -> OTPInputProp msg
autoFocusProp enabled props = props { autoFocus = enabled }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // animation prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable/disable animations
animationEnabledProp :: forall msg. Boolean -> OTPInputProp msg
animationEnabledProp enabled props = props { animationEnabled = enabled }

-- | Enable reduced motion (respects prefers-reduced-motion)
reducedMotionProp :: forall msg. Boolean -> OTPInputProp msg
reducedMotionProp enabled props = props { reducedMotion = enabled }

-- | Set error shake animation duration (Schema Milliseconds)
shakeDurationProp :: forall msg. Temporal.Milliseconds -> OTPInputProp msg
shakeDurationProp duration props = props { shakeDuration = duration }

-- | Set success pulse animation duration (Schema Milliseconds)
pulseDurationProp :: forall msg. Temporal.Milliseconds -> OTPInputProp msg
pulseDurationProp duration props = props { pulseDuration = duration }

-- | Set digit entry animation duration (Schema Milliseconds)
entryDurationProp :: forall msg. Temporal.Milliseconds -> OTPInputProp msg
entryDurationProp duration props = props { entryDuration = duration }

-- | Set transition duration for state changes (Schema Milliseconds)
transitionDurationProp :: forall msg. Temporal.Milliseconds -> OTPInputProp msg
transitionDurationProp duration props = props { transitionDuration = duration }

-- | Set transition easing curve (Schema Motion.Easing)
transitionEasingProp :: forall msg. Easing.Easing -> OTPInputProp msg
transitionEasingProp easing props = props { transitionEasing = easing }

-- | Set stagger delay between digit animations (Schema Milliseconds)
staggerDelayProp :: forall msg. Temporal.Milliseconds -> OTPInputProp msg
staggerDelayProp delay props = props { staggerDelay = delay }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // separator prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable/disable separators (for XXX-XXX patterns)
separatorEnabledProp :: forall msg. Boolean -> OTPInputProp msg
separatorEnabledProp enabled props = props { separatorEnabled = enabled }

-- | Set separator positions (indices where separators appear)
-- | e.g., [3] for 6-digit OTP = XXX-XXX
separatorPositionsProp :: forall msg. Array Int -> OTPInputProp msg
separatorPositionsProp positions props = props { separatorPositions = positions }

-- | Set separator character
separatorCharProp :: forall msg. Char -> OTPInputProp msg
separatorCharProp c props = props { separatorChar = c }

-- | Set separator color (Schema Color.RGB)
separatorColorProp :: forall msg. Color.RGB -> OTPInputProp msg
separatorColorProp c props = props { separatorColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // label and text prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set label color (Schema Color.RGB)
labelColorProp :: forall msg. Color.RGB -> OTPInputProp msg
labelColorProp c props = props { labelColor = Just c }

-- | Enable/disable auto-advance behavior
-- |
-- | When true (default), focus automatically advances to next digit after entry.
autoAdvanceProp :: forall msg. Boolean -> OTPInputProp msg
autoAdvanceProp enabled props = props { autoAdvance = enabled }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // cursor prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set cursor style (text, pointer, not-allowed)
cursorStyleProp :: forall msg. String -> OTPInputProp msg
cursorStyleProp style props = props { cursorStyle = style }
