-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // element // otpinput // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Accessibility — ARIA attributes and a11y patterns.
-- |
-- | ## Accessibility Philosophy
-- |
-- | OTP inputs present unique accessibility challenges:
-- |
-- | 1. **Multiple inputs for single value** — Screen readers need to understand
-- |    these are parts of a single code
-- | 2. **Auto-advance** — Focus moves automatically which can be disorienting
-- | 3. **Time limits** — OTP codes expire, creating pressure
-- | 4. **Error feedback** — Must be announced to screen readers
-- |
-- | ## ARIA Implementation
-- |
-- | - Container has `role="group"` with descriptive `aria-label`
-- | - Each digit has `aria-label` indicating position
-- | - Error states use `aria-invalid` and `aria-describedby`
-- | - Live regions announce state changes
-- |
-- | ## Dependencies
-- |
-- | - Types module for OTPState, OTPIndex, OTPDigitCount
-- | - Element module for attribute generation

module Hydrogen.Element.Compound.OTPInput.Accessibility
  ( -- * Container Accessibility
    getContainerA11yAttrs
  , getGroupLabel
  
  -- * Digit Accessibility
  , getDigitA11yAttrs
  , getDigitLabel
  
  -- * State Announcements
  , getStateA11yAttrs
  , getErrorA11yAttrs
  , getSuccessA11yAttrs
  
  -- * Live Region Helpers
  , getLiveRegionAttrs
  , getAnnouncementText
  
  -- * IDs for ARIA relationships
  , getErrorMessageId
  , getDigitId
  , getGroupId
  
  -- * Reduced Motion Support
  , getReducedMotionAttrs
  , getMotionSafeStyles
  
  -- * Keyboard Navigation Hints
  , getKeyboardHintText
  , getNavigationInstructions
  , getFocusTrapAttrs
  
  -- * Timer/Expiration Support
  , getTimerA11yAttrs
  , getExpirationAnnouncementText
  
  -- * Auto-Advance Behavior
  , getAutoAdvanceHintText
  , getAutoAdvanceAttrs
  
  -- * Screen Reader Instructions
  , getScreenReaderInstructions
  , getHelpTextId
  , getSuccessMessageId
  ) where

import Prelude
  ( show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , otherwise
  )

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.OTPInput.Types
  ( OTPState(Idle, Entering, Verifying, Success, Error)
  , OTPIndex
  , OTPDigitCount
  , unwrapOTPIndex
  , unwrapDigitCount
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // container accessibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get accessibility attributes for the OTP container
getContainerA11yAttrs 
  :: forall msg 
   . String              -- ^ Component instance ID
  -> OTPDigitCount 
  -> OTPState 
  -> Maybe String        -- ^ Error message if any
  -> Array (E.Attribute msg)
getContainerA11yAttrs instanceId digitCount state errorMsg =
  [ E.role "group"
  , E.ariaLabel (getGroupLabel digitCount)
  , E.attr "id" (getGroupId instanceId)
  ]
  <> getStateA11yAttrs state errorMsg instanceId

-- | Generate descriptive label for the OTP input group
getGroupLabel :: OTPDigitCount -> String
getGroupLabel count =
  "One-time password input with " <> show (unwrapDigitCount count) <> " digits"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // digit accessibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get accessibility attributes for a single digit input
getDigitA11yAttrs 
  :: forall msg 
   . String              -- ^ Component instance ID
  -> OTPIndex 
  -> OTPDigitCount 
  -> OTPState 
  -> Maybe String        -- ^ Error message if any
  -> Array (E.Attribute msg)
getDigitA11yAttrs instanceId idx digitCount state errorMsg =
  let
    -- Base attributes always present
    baseAttrs =
      [ E.ariaLabel (getDigitLabel idx digitCount)
      , E.attr "id" (getDigitId instanceId idx)
      ]
    
    -- Error-related attributes when in error state
    errorAttrs = case state of
      Error -> 
        [ E.attr "aria-invalid" "true"
        , E.ariaDescribedBy (getErrorMessageId instanceId)
        ]
        <> case errorMsg of
             Nothing -> []
             Just msg -> [ E.attr "title" msg ]  -- Tooltip with error message
      Idle -> []
      Entering -> []
      Verifying -> 
        [ E.attr "aria-busy" "true" ]
      Success -> 
        [ E.ariaDescribedBy (getSuccessMessageId instanceId) ]
  in
    baseAttrs <> errorAttrs

-- | Generate descriptive label for a digit input
getDigitLabel :: OTPIndex -> OTPDigitCount -> String
getDigitLabel idx count =
  "Digit " <> show (unwrapOTPIndex idx + 1) <> " of " <> show (unwrapDigitCount count)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // state announcements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get state-related accessibility attributes
-- |
-- | All OTPState variants handled explicitly for exhaustiveness.
getStateA11yAttrs 
  :: forall msg 
   . OTPState 
  -> Maybe String   -- ^ Error message
  -> String         -- ^ Instance ID
  -> Array (E.Attribute msg)
getStateA11yAttrs state errorMsg instanceId =
  case state of
    Idle -> []
    Entering -> []
    Verifying ->
      [ E.attr "aria-busy" "true"
      , E.ariaLive "polite"
      ]
    Success -> []
    Error ->
      getErrorA11yAttrs errorMsg instanceId

-- | Get error-specific accessibility attributes
getErrorA11yAttrs 
  :: forall msg 
   . Maybe String   -- ^ Error message
  -> String         -- ^ Instance ID
  -> Array (E.Attribute msg)
getErrorA11yAttrs errorMsg instanceId =
  case errorMsg of
    Nothing -> []
    Just _ ->
      [ E.attr "aria-invalid" "true"
      , E.ariaDescribedBy (getErrorMessageId instanceId)
      ]

-- | Get success-specific accessibility attributes
getSuccessA11yAttrs :: forall msg. Array (E.Attribute msg)
getSuccessA11yAttrs = []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // live region helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get attributes for a live region that announces state changes
getLiveRegionAttrs :: forall msg. OTPState -> Array (E.Attribute msg)
getLiveRegionAttrs state =
  case state of
    Idle -> 
      [ E.ariaLive "polite"
      , E.ariaAtomic "true"
      ]
    Entering ->
      [ E.ariaLive "polite"
      , E.ariaAtomic "true"
      ]
    Verifying ->
      [ E.ariaLive "assertive"
      , E.ariaAtomic "true"
      ]
    Success ->
      [ E.ariaLive "assertive"
      , E.ariaAtomic "true"
      ]
    Error ->
      [ E.ariaLive "assertive"
      , E.ariaAtomic "true"
      ]

-- | Get announcement text for screen readers
-- |
-- | All OTPState variants handled explicitly for exhaustiveness.
getAnnouncementText :: OTPState -> Maybe String -> String
getAnnouncementText state errorMsg =
  case state of
    Idle -> ""
    Entering -> ""
    Verifying -> "Verifying code, please wait"
    Success -> "Code verified successfully"
    Error ->
      case errorMsg of
        Nothing -> "Code verification failed"
        Just msg -> msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // ids for aria relationships
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate error message element ID
getErrorMessageId :: String -> String
getErrorMessageId instanceId = instanceId <> "-error"

-- | Generate digit input element ID
getDigitId :: String -> OTPIndex -> String
getDigitId instanceId idx = 
  instanceId <> "-digit-" <> show (unwrapOTPIndex idx)

-- | Generate group element ID
getGroupId :: String -> String
getGroupId instanceId = instanceId <> "-group"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // reduced motion support
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get accessibility attributes for reduced motion preference.
-- |
-- | When reduced motion is enabled, animations should be minimized or removed.
-- | This provides visual feedback to users that their preference is respected.
getReducedMotionAttrs :: forall msg. Boolean -> Array (E.Attribute msg)
getReducedMotionAttrs reducedMotion =
  if reducedMotion
    then 
      [ E.dataAttr "reduced-motion" "true"
      , E.dataAttr "animation-disabled" "true"
      ]
    else 
      [ E.dataAttr "reduced-motion" "false" ]

-- | Get inline styles that respect reduced motion preference.
-- |
-- | Returns a transition style string based on whether reduced motion is enabled.
-- | With reduced motion: instant transitions (0ms)
-- | Without: normal transition duration
getMotionSafeStyles :: Boolean -> Int -> String
getMotionSafeStyles reducedMotion durationMs =
  if reducedMotion
    then "0ms"
    else show durationMs <> "ms"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // keyboard navigation hints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get keyboard hint text for screen readers.
-- |
-- | Explains the keyboard navigation pattern for the OTP input.
getKeyboardHintText :: OTPDigitCount -> String
getKeyboardHintText count =
  "Use arrow keys to navigate between " <> show (unwrapDigitCount count) 
  <> " digit fields. Press Backspace to clear and move to previous digit. "
  <> "Press Tab to move to next form field."

-- | Get full navigation instructions for help text.
-- |
-- | Comprehensive instructions for screen reader users.
getNavigationInstructions :: OTPDigitCount -> Boolean -> String
getNavigationInstructions count autoAdvance =
  let
    baseInstructions = 
      "Enter your " <> show (unwrapDigitCount count) <> "-digit verification code. "
    
    navigationHint = 
      "Use Left and Right arrow keys to move between digits. "
      <> "Backspace clears the current digit and moves to the previous field. "
    
    autoAdvanceHint = 
      if autoAdvance
        then "After entering a digit, focus automatically moves to the next field. "
        else ""
    
    submitHint = 
      "When all digits are entered, the code will be verified automatically."
  in
    baseInstructions <> navigationHint <> autoAdvanceHint <> submitHint

-- | Get focus trap attributes for keyboard navigation.
-- |
-- | Ensures keyboard focus stays within the OTP input until complete or escaped.
getFocusTrapAttrs :: forall msg. Boolean -> Array (E.Attribute msg)
getFocusTrapAttrs trapFocus =
  if trapFocus
    then 
      [ E.dataAttr "focus-trap" "true"
      , E.attr "tabindex" "-1"
      ]
    else 
      [ E.dataAttr "focus-trap" "false" ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // timer/expiration support
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get accessibility attributes for timer/countdown display.
-- |
-- | OTP codes often have expiration timers. These need to be accessible.
getTimerA11yAttrs :: forall msg. Int -> Array (E.Attribute msg)
getTimerA11yAttrs secondsRemaining =
  [ E.role "timer"
  , E.ariaLive (if secondsRemaining <= 30 then "assertive" else "polite")
  , E.ariaAtomic "true"
  , E.ariaLabel ("Time remaining: " <> formatTimeRemaining secondsRemaining)
  ]

-- | Get expiration announcement text for screen readers.
-- |
-- | Generates appropriate announcement based on time remaining.
getExpirationAnnouncementText :: Int -> String
getExpirationAnnouncementText secondsRemaining
  | secondsRemaining <= 0 = "Code has expired. Please request a new code."
  | secondsRemaining <= 10 = "Warning: Code expires in " <> show secondsRemaining <> " seconds."
  | secondsRemaining <= 30 = "Code expires in " <> show secondsRemaining <> " seconds."
  | secondsRemaining <= 60 = "Code expires in less than one minute."
  | otherwise = 
      let minutes = secondsRemaining / 60
      in "Code expires in approximately " <> show minutes <> " minutes."

-- | Format time remaining as human-readable string.
formatTimeRemaining :: Int -> String
formatTimeRemaining seconds
  | seconds <= 0 = "expired"
  | seconds < 60 = show seconds <> " seconds"
  | otherwise =
      let 
        mins = seconds / 60
        secs = seconds - (mins * 60)
      in
        show mins <> " minutes and " <> show secs <> " seconds"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // auto-advance behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get hint text explaining auto-advance behavior.
-- |
-- | Screen readers should announce this behavior to set user expectations.
getAutoAdvanceHintText :: Boolean -> String
getAutoAdvanceHintText autoAdvance =
  if autoAdvance
    then "Focus will automatically move to the next digit after entry."
    else "Press Tab or Right Arrow to move to the next digit."

-- | Get accessibility attributes for auto-advance behavior.
-- |
-- | Indicates to assistive technology that focus management is automatic.
getAutoAdvanceAttrs :: forall msg. Boolean -> Array (E.Attribute msg)
getAutoAdvanceAttrs autoAdvance =
  [ E.dataAttr "auto-advance" (if autoAdvance then "true" else "false")
  , E.attr "aria-owns" ""  -- Will be populated with digit IDs
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // screen reader instructions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get comprehensive screen reader instructions element content.
-- |
-- | This text is visually hidden but announced to screen readers.
getScreenReaderInstructions :: OTPDigitCount -> Boolean -> Boolean -> String
getScreenReaderInstructions digitCount autoAdvance hasExpiration =
  let
    intro = 
      "Verification code entry. "
    
    digitInfo = 
      "Enter your " <> show (unwrapDigitCount digitCount) <> "-digit code. "
    
    navigationInfo = 
      "Use arrow keys to navigate between digits. "
      <> "Backspace clears current digit and moves back. "
    
    autoAdvanceInfo = 
      if autoAdvance
        then "Focus advances automatically after each digit. "
        else ""
    
    expirationInfo = 
      if hasExpiration
        then "This code has a time limit. Listen for expiration warnings. "
        else ""
    
    completionInfo = 
      "When complete, verification begins automatically."
  in
    intro <> digitInfo <> navigationInfo <> autoAdvanceInfo <> expirationInfo <> completionInfo

-- | Generate help text element ID
getHelpTextId :: String -> String
getHelpTextId instanceId = instanceId <> "-help"

-- | Generate success message element ID
getSuccessMessageId :: String -> String
getSuccessMessageId instanceId = instanceId <> "-success"
