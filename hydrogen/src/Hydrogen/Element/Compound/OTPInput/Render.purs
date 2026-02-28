-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // otpinput // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Render — Main composition of the OTP input component.
-- |
-- | ## Composition Architecture
-- |
-- | This module composes all submodules into the final renderable component:
-- |
-- | ```
-- | otpInput
-- |   └── Container (accessibility, layout)
-- |       └── Digits Row (gap, centering)
-- |           └── Digit Inputs (validation, styling, animation data)
-- |       └── Error Message (conditional)
-- |       └── Resend Section (optional)
-- |       └── Live Region (screen reader announcements)
-- | ```
-- |
-- | ## Animation Architecture
-- |
-- | Animations are described as **pure data** (OTPAnimation type) and attached
-- | to digit elements. The Target layer (DOM, WebGL) interprets this data to
-- | produce actual motion. NO CSS STRINGS. NO STYLE INJECTION.
-- |
-- | ## Dependencies
-- |
-- | - Types for all OTP types
-- | - Props for configuration
-- | - Digit for individual digit rendering
-- | - Animation for pure animation data types
-- | - Accessibility for ARIA attributes
-- | - Validation for input patterns

module Hydrogen.Element.Compound.OTPInput.Render
  ( -- * Main Components
    otpInput
  , otpInputWithResend
  
  -- * Sub-Components
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
  
  -- * Instance ID Generation
  , generateInstanceId
  ) where

import Prelude
  ( show
  , (>)
  , (<>)
  , (-)
  , map
  )

import Data.Array (foldl, head, range)
import Data.String.CodeUnits as SCU
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color

import Hydrogen.Element.Compound.OTPInput.Types
  ( OTPState(Idle, Entering, Verifying, Success, Error)
  , unwrapDigitCount
  )

import Hydrogen.Element.Compound.OTPInput.Props
  ( OTPInputProps
  , OTPInputProp
  , defaultProps
  )

import Hydrogen.Element.Compound.OTPInput.Digit
  ( renderDigit
  )

import Hydrogen.Element.Compound.OTPInput.Accessibility
  ( getContainerA11yAttrs
  , getLiveRegionAttrs
  , getAnnouncementText
  , getErrorMessageId
  , getHelpTextId
  , getSuccessMessageId
  , getScreenReaderInstructions
  , getReducedMotionAttrs
  )

-- Animation module provides pure data types for animation.
-- Animations are attached to elements as data, NOT injected as CSS.
-- The Target layer (DOM, WebGL) interprets animation data.

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the complete OTP input component.
-- |
-- | Composes:
-- | - Label (optional)
-- | - Help text / screen reader instructions
-- | - Accessibility container
-- | - Digit inputs with optional separators
-- | - Success / Error message (conditional)
-- | - Animation keyframe styles
-- | - Live region for announcements
otpInput :: forall msg. Array (OTPInputProp msg) -> E.Element msg
otpInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    instanceId = generateInstanceId props
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "flex-direction" "column"
        , E.style "gap" "8px"
        , E.style "align-items" "center"
        ]
        <> getContainerA11yAttrs instanceId props.digitCount props.state props.errorMessage
        <> getReducedMotionAttrs props.reducedMotion
      )
      [ -- Label (if provided)
        renderLabel props
      
      -- Screen reader instructions (visually hidden)
      , renderScreenReaderHint props instanceId
      
      -- Digits row (with or without separator)
      , renderDigitsWithSeparator props
      
      -- Help text (if provided and not in error/success state)
      , renderHelpText props instanceId
      
      -- Success message (if in success state)
      , renderSuccessMessage props instanceId
      
      -- Error message (if present)
      , renderErrorMessage props instanceId
      
      -- Live region for screen reader announcements
      , renderLiveRegion props
      ]

-- | Render OTP input with resend button section
otpInputWithResend :: forall msg. Array (OTPInputProp msg) -> E.Element msg
otpInputWithResend propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    instanceId = generateInstanceId props
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "flex-direction" "column"
        , E.style "gap" "16px"
        , E.style "align-items" "center"
        ]
        <> getContainerA11yAttrs instanceId props.digitCount props.state props.errorMessage
        <> getReducedMotionAttrs props.reducedMotion
      )
      [ renderLabel props
      , renderScreenReaderHint props instanceId
      , renderDigitsWithSeparator props
      , renderHelpText props instanceId
      , renderSuccessMessage props instanceId
      , renderErrorMessage props instanceId
      , renderResendSection props
      , renderLiveRegion props
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // sub-components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the row of digit inputs (simple, no separators)
renderDigitsRow :: forall msg. OTPInputProps msg -> E.Element msg
renderDigitsRow props =
  let
    count = unwrapDigitCount props.digitCount
    indices = range 0 (count - 1)
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "gap" (getGapValue props)
      , E.style "justify-content" "center"
      ]
      (map (renderDigit props) indices)

-- | Render digits with separator based on separatorEnabled and separatorPositions.
-- |
-- | If separatorEnabled is true and separatorPositions has entries, renders
-- | visual separators between digit groups at the specified positions.
renderDigitsWithSeparator :: forall msg. OTPInputProps msg -> E.Element msg
renderDigitsWithSeparator props =
  if props.separatorEnabled
    then case head props.separatorPositions of
      Nothing -> renderDigitsRow props  -- No positions, fallback
      Just sepIdx ->
        let
          count = unwrapDigitCount props.digitCount
          firstGroup = range 0 (sepIdx - 1)
          secondGroup = range sepIdx (count - 1)
        in
          E.div_
            [ E.style "display" "flex"
            , E.style "gap" (getGapValue props)
            , E.style "justify-content" "center"
            , E.style "align-items" "center"
            ]
            [ -- First group of digits
              E.div_
                [ E.style "display" "flex"
                , E.style "gap" (getGapValue props)
                ]
                (map (renderDigit props) firstGroup)
            
            -- Separator
            , renderSeparator props
            
            -- Second group of digits
            , E.div_
                [ E.style "display" "flex"
                , E.style "gap" (getGapValue props)
                ]
                (map (renderDigit props) secondGroup)
            ]
    else renderDigitsRow props

-- | Render visual separator between digit groups.
-- |
-- | Uses separatorChar from props (Char type).
renderSeparator :: forall msg. OTPInputProps msg -> E.Element msg
renderSeparator props =
  let
    -- Convert Char to String for display
    sepChar = SCU.singleton props.separatorChar
    
    sepColor = case props.separatorColor of
      Nothing -> getMutedTextColor props
      Just c -> Color.toLegacyCss c
  in
    E.span_
      [ E.style "font-size" "20px"
      , E.style "font-weight" "300"
      , E.style "color" sepColor
      , E.style "padding" "0 4px"
      , E.style "user-select" "none"
      , E.ariaHidden true  -- Decorative, hide from screen readers
      ]
      [ E.text sepChar ]

-- | Render label above the OTP input.
-- |
-- | Shows only if label prop is provided.
renderLabel :: forall msg. OTPInputProps msg -> E.Element msg
renderLabel props =
  case props.label of
    Nothing -> E.empty
    Just labelText ->
      let
        labelColor = case props.labelColor of
          Nothing -> "#0f172a"  -- slate-900
          Just c -> Color.toLegacyCss c
      in
        E.label_
          [ E.style "font-size" "14px"
          , E.style "font-weight" "500"
          , E.style "color" labelColor
          , E.style "margin-bottom" "4px"
          , E.style "display" "block"
          , E.style "text-align" "center"
          ]
          [ E.text labelText ]

-- | Render help text below the OTP input.
-- |
-- | Shows only if helpText prop is provided and not in error/success state.
renderHelpText :: forall msg. OTPInputProps msg -> String -> E.Element msg
renderHelpText props instanceId =
  case props.helpText of
    Nothing -> E.empty
    Just helpStr ->
      -- Don't show help text in error or success states
      case props.state of
        Error -> E.empty
        Success -> E.empty
        Idle -> renderHelpTextElement props instanceId helpStr
        Entering -> renderHelpTextElement props instanceId helpStr
        Verifying -> renderHelpTextElement props instanceId helpStr

-- | Render the actual help text element
renderHelpTextElement 
  :: forall msg 
   . OTPInputProps msg 
  -> String 
  -> String 
  -> E.Element msg
renderHelpTextElement props instanceId helpStr =
  let
    helpColor = getMutedTextColor props
  in
    E.div_
      [ E.attr "id" (getHelpTextId instanceId)
      , E.style "font-size" "13px"
      , E.style "color" helpColor
      , E.style "text-align" "center"
      , E.style "margin-top" "4px"
      ]
      [ E.text helpStr ]

-- | Render success message when verification succeeds.
-- |
-- | Shows only in Success state.
renderSuccessMessage :: forall msg. OTPInputProps msg -> String -> E.Element msg
renderSuccessMessage props instanceId =
  case props.state of
    Success ->
      let
        msg = case props.successMessage of
          Nothing -> "Code verified successfully"
          Just m -> m
        
        successColor = case props.successTextColor of
          Nothing -> "#22c55e"  -- green-500
          Just c -> Color.toLegacyCss c
      in
        E.div_
          [ E.attr "id" (getSuccessMessageId instanceId)
          , E.role "status"
          , E.ariaLive "polite"
          , E.style "font-size" "14px"
          , E.style "color" successColor
          , E.style "text-align" "center"
          , E.style "margin-top" "8px"
          ]
          [ E.text msg ]
    Idle -> E.empty
    Entering -> E.empty
    Verifying -> E.empty
    Error -> E.empty

-- | Render screen reader instructions (visually hidden).
-- |
-- | Provides comprehensive instructions for assistive technology users.
renderScreenReaderHint :: forall msg. OTPInputProps msg -> String -> E.Element msg
renderScreenReaderHint props instanceId =
  let
    -- Determine if there's a timer/expiration
    hasExpiration = props.resendRemaining > 0
    
    instructions = getScreenReaderInstructions 
      props.digitCount 
      props.autoAdvance 
      hasExpiration
  in
    E.div_
      [ E.attr "id" (instanceId <> "-instructions")
      -- Visually hidden but accessible to screen readers
      , E.style "position" "absolute"
      , E.style "width" "1px"
      , E.style "height" "1px"
      , E.style "margin" "-1px"
      , E.style "padding" "0"
      , E.style "overflow" "hidden"
      , E.style "clip" "rect(0, 0, 0, 0)"
      , E.style "white-space" "nowrap"
      , E.style "border" "0"
      ]
      [ E.text instructions ]

-- | Render error message element (hidden if no error)
renderErrorMessage :: forall msg. OTPInputProps msg -> String -> E.Element msg
renderErrorMessage props instanceId =
  case props.errorMessage of
    Nothing -> E.empty
    Just msg ->
      E.div_
        [ E.attr "id" (getErrorMessageId instanceId)
        , E.role "alert"
        , E.style "font-size" "14px"
        , E.style "color" (getErrorTextColor props)
        , E.style "text-align" "center"
        , E.style "margin-top" "8px"
        ]
        [ E.text msg ]

-- | Render resend section (countdown or button)
renderResendSection :: forall msg. OTPInputProps msg -> E.Element msg
renderResendSection props =
  E.div_
    [ E.style "text-align" "center"
    , E.style "margin-top" "8px"
    ]
    [ if props.resendRemaining > 0
        then renderResendCountdown props
        else renderResendButton props
    ]

-- | Render resend countdown text
renderResendCountdown :: forall msg. OTPInputProps msg -> E.Element msg
renderResendCountdown props =
  E.span_
    [ E.style "font-size" "14px"
    , E.style "color" (getMutedTextColor props)
    ]
    [ E.text ("Resend code in " <> show props.resendRemaining <> "s") ]

-- | Render resend button
renderResendButton :: forall msg. OTPInputProps msg -> E.Element msg
renderResendButton props =
  E.button_
    ( [ E.type_ "button"
      , E.style "font-size" "14px"
      , E.style "color" (getPrimaryColor props)
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "text-decoration" "underline"
      , E.style "padding" "0"
      ]
      <> case props.onResendClick of
           Just handler -> [ E.onClick handler ]
           Nothing -> []
    )
    [ E.text "Resend code" ]

-- | Render live region for screen reader announcements
renderLiveRegion :: forall msg. OTPInputProps msg -> E.Element msg
renderLiveRegion props =
  let announcement = getAnnouncementText props.state props.errorMessage
  in
    E.div_
      ( [ E.style "position" "absolute"
        , E.style "width" "1px"
        , E.style "height" "1px"
        , E.style "margin" "-1px"
        , E.style "padding" "0"
        , E.style "overflow" "hidden"
        , E.style "clip" "rect(0, 0, 0, 0)"
        , E.style "white-space" "nowrap"
        , E.style "border" "0"
        ]
        <> getLiveRegionAttrs props.state
      )
      [ E.text announcement ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a stable instance ID for accessibility relationships
generateInstanceId :: forall msg. OTPInputProps msg -> String
generateInstanceId props =
  "otp-" <> show (unwrapDigitCount props.digitCount)

-- | Get gap value from props
getGapValue :: forall msg. OTPInputProps msg -> String
getGapValue props =
  case props.gap of
    Just g -> show g
    Nothing -> "8px"

-- | Get error text color
getErrorTextColor :: forall msg. OTPInputProps msg -> String
getErrorTextColor props =
  case props.errorTextColor of
    Just c -> Color.toLegacyCss c
    Nothing -> "#ef4444"

-- | Get muted text color
getMutedTextColor :: forall msg. OTPInputProps msg -> String
getMutedTextColor props =
  case props.mutedTextColor of
    Just c -> Color.toLegacyCss c
    Nothing -> "#64748b"

-- | Get primary color
getPrimaryColor :: forall msg. OTPInputProps msg -> String
getPrimaryColor props =
  case props.primaryColor of
    Just c -> Color.toLegacyCss c
    Nothing -> "#3b82f6"
