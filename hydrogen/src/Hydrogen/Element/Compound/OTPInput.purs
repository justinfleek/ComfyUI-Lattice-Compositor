-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // otp-input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput — Schema-native one-time password input component.
-- |
-- | ## Leader Module
-- |
-- | This module re-exports the complete OTPInput component from submodules:
-- |
-- | - **Types** — Bounded, security-conscious types for OTP handling
-- | - **Props** — Schema-native property system
-- | - **Validation** — Input validation and character filtering
-- | - **Digit** — Single digit rendering
-- | - **Animation** — CSS animation styles
-- | - **Accessibility** — ARIA attributes and a11y patterns
-- | - **Render** — Main composition and rendering
-- |
-- | ## Design Philosophy
-- |
-- | This component renders a row of single-character inputs for OTP/PIN entry.
-- | All visual properties are Schema atoms — no Tailwind, no CSS strings.
-- |
-- | ## Security Philosophy
-- |
-- | OTP values are security-critical. The Types module ensures:
-- | - Bounded digit counts (4-8)
-- | - Validated characters on construction
-- | - No partial functions
-- | - Masked display by default in Show instances
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.OTPInput as OTP
-- |
-- | -- Basic 6-digit OTP
-- | OTP.otpInput
-- |   [ OTP.digitCountProp (OTP.digitCount 6)
-- |   , OTP.otpValueProp (OTP.emptyOTP (OTP.digitCount 6))
-- |   , OTP.onDigitChangeProp HandleChange
-- |   ]
-- |
-- | -- With brand colors
-- | OTP.otpInput
-- |   [ OTP.digitCountProp (OTP.digitCount 4)
-- |   , OTP.borderColorProp brand.inputBorder
-- |   , OTP.focusBorderColorProp brand.primaryColor
-- |   , OTP.borderRadiusProp brand.inputRadius
-- |   ]
-- | ```

module Hydrogen.Element.Compound.OTPInput
  ( -- * Components (from Render)
    module Render
  
  -- * Types (from Types)
  , module Types
  
  -- * Props (from Props)
  , module Props
  
  -- * Validation (from Validation)
  , module Validation
  
  -- * Digit Rendering (from Digit)
  , module Digit
  
  -- * Animation (from Animation)
  , module Animation
  
  -- * Accessibility (from Accessibility)
  , module Accessibility
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.OTPInput.Types
  ( OTPInputType(Numeric, Alphanumeric)
  , OTPDigitCount(OTPDigitCount)
  , OTPValue(OTPValue)
  , OTPDigit(OTPDigit)
  , OTPIndex(OTPIndex)
  , OTPState(Idle, Entering, Verifying, Success, Error)
  , OTPFocusState(Unfocused, Focused)
  , DigitAnimationState(DigitIdle, DigitEntering, DigitFilled, DigitError, DigitSuccess)
  , OTPMsg(DigitInput, DigitDelete, DigitFocus, DigitBlur, PasteDetected, Completed, ResendClicked, ClearError)
  , digitCount
  , otpValue
  , emptyOTP
  , otpDigit
  , otpIndex
  , unwrapDigitCount
  , unwrapOTPValue
  , unwrapOTPDigit
  , unwrapOTPIndex
  , otpLength
  , isOTPComplete
  , getDigitAt
  , getMaskedValue
  , setDigitAt
  , appendDigit
  , deleteLastDigit
  , clearOTP
  , minDigits
  , maxDigits
  ) as Types

import Hydrogen.Element.Compound.OTPInput.Props
  ( OTPInputProps
  , OTPInputProp
  , defaultProps
  , digitCountProp
  , otpValueProp
  , otpInputTypeProp
  , maskedProp
  , disabledProp
  , stateProp
  , errorMessageProp
  , focusedIndexProp
  , resendCooldownProp
  , resendRemainingProp
  , backgroundColorProp
  , borderColorProp
  , focusBorderColorProp
  , errorBorderColorProp
  , successBorderColorProp
  , filledBorderColorProp
  , textColorProp
  , placeholderColorProp
  , errorTextColorProp
  , successTextColorProp
  , mutedTextColorProp
  , primaryColorProp
  , borderRadiusProp
  , borderWidthProp
  , digitWidthProp
  , digitHeightProp
  , gapProp
  , fontSizeProp
  , fontWeightProp
  , onDigitChangeProp
  , onCompleteProp
  , onResendClickProp
  , onFocusProp
  , onBlurProp
  , onPasteProp
  , animationEnabledProp
  , shakeDurationProp
  , pulseDurationProp
  , entryDurationProp
  -- New props
  , separatorEnabledProp
  , separatorPositionsProp
  , separatorCharProp
  , separatorColorProp
  , labelColorProp
  , autoAdvanceProp
  , reducedMotionProp
  , transitionDurationProp
  , transitionEasingProp
  , staggerDelayProp
  , cursorStyleProp
  ) as Props

import Hydrogen.Element.Compound.OTPInput.Validation
  ( validateChar
  , isValidDigit
  , isValidAlphanumeric
  , normalizeChar
  , validateString
  , sanitizeString
  , filterValidChars
  , validatePaste
  , extractValidOTP
  , getInputMode
  , getInputPattern
  , getAutoComplete
  ) as Validation

import Hydrogen.Element.Compound.OTPInput.Digit
  ( renderDigit
  , renderDigitInput
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
  , isDigitFocused
  , isDigitFilled
  , getDigitDisplayValue
  ) as Digit

import Hydrogen.Element.Compound.OTPInput.Animation
  ( OTPAnimation(OTPAnimation)
  , OTPAnimationProperty(TranslateX, TranslateY, Scale, ScaleX, ScaleY, Opacity, Rotate)
  , OTPKeyframe(OTPKeyframe)
  , OTPIterationCount(Once, Times, Infinite)
  , OTPFillMode(FillNone, FillForwards, FillBackwards, FillBoth)
  , shakeAnimation
  , pulseAnimation
  , entryAnimation
  , loadingAnimation
  , getAnimation
  , getAnimationData
  , getAnimationDataAttrs
  , computeDigitAnimationState
  , shouldAnimate
  , animationProperty
  , animationKeyframes
  , animationDuration
  , animationEasing
  , animationIterations
  , animationFillMode
  ) as Animation

import Hydrogen.Element.Compound.OTPInput.Accessibility
  ( getContainerA11yAttrs
  , getGroupLabel
  , getDigitA11yAttrs
  , getDigitLabel
  , getStateA11yAttrs
  , getErrorA11yAttrs
  , getSuccessA11yAttrs
  , getLiveRegionAttrs
  , getAnnouncementText
  , getErrorMessageId
  , getDigitId
  , getGroupId
  -- New exports
  , getReducedMotionAttrs
  , getMotionSafeStyles
  , getKeyboardHintText
  , getNavigationInstructions
  , getFocusTrapAttrs
  , getTimerA11yAttrs
  , getExpirationAnnouncementText
  , getAutoAdvanceHintText
  , getAutoAdvanceAttrs
  , getScreenReaderInstructions
  , getHelpTextId
  , getSuccessMessageId
  ) as Accessibility

import Hydrogen.Element.Compound.OTPInput.Render
  ( otpInput
  , otpInputWithResend
  , renderDigitsRow
  , renderDigitsWithSeparator
  , renderSeparator
  , renderLabel
  , renderHelpText
  , renderErrorMessage
  , renderSuccessMessage
  , renderResendSection
  , renderLiveRegion
  , renderScreenReaderHint
  , generateInstanceId
  ) as Render
