-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // tour // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour state management
-- |
-- | This module provides the TourState type and TourMsg sum type for managing
-- | product tour state following the Elm architecture pattern:
-- |
-- | ```
-- | State × Msg → State × [Cmd]
-- | view :: State → Element Msg
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.State as Tour
-- |
-- | initialState :: Tour.TourState MyMsg
-- | initialState = Tour.initTour (T.mkTourId "onboarding") mySteps
-- |
-- | handleMsg :: Tour.TourMsg MyMsg -> AppState -> AppState
-- | handleMsg msg state = state { tour = Tour.update msg state.tour }
-- | ```
module Hydrogen.Tour.State
  ( -- * Tour State
    TourState
  , initTour
  , tourId
  , currentStep
  , currentStepIndex
  , totalSteps
  , progress
  , phase
  , steps
  , canGoNext
  , canGoPrev
  , isFirstStep
  , isLastStep
    -- * Tour Messages
  , TourMsg(..)
    -- * Tour Configuration
  , TourConfig
  , defaultConfig
  , withOverlayColor
  , withOverlayOpacity
  , withKeyboardNav
  , withCloseOnOverlay
  , withCloseOnEscape
    -- * Dismiss Reason
  , DismissReason(..)
  ) where

import Prelude

import Data.Array (index, length)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Show.Generic (genericShow)
import Hydrogen.Tour.Step (Step)
import Hydrogen.Tour.Types (Milliseconds, Progress, StepId, TourId, TourPhase(TourActive, TourCompleted, TourDismissed, TourInactive, TourPaused, TourSkipped), mkProgress)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // tour state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete state for a product tour
-- |
-- | The tour state is the single source of truth for the tour's current
-- | condition. It tracks:
-- | - Which phase the tour is in (inactive, active, completed, etc.)
-- | - All step definitions
-- | - Configuration options
-- | - Step visit history (for analytics)
type TourState msg =
  { id :: TourId
    -- ^ Unique tour identifier
  , phase :: TourPhase
    -- ^ Current lifecycle phase
  , steps :: Array (Step msg)
    -- ^ All step definitions
  , config :: TourConfig
    -- ^ Tour behavior configuration
  , visitedSteps :: Array Int
    -- ^ Indices of steps that have been shown (for analytics)
  }

-- | Initialize a tour state
-- |
-- | Creates a tour in the inactive phase, ready to be started.
initTour :: forall msg. TourId -> Array (Step msg) -> TourState msg
initTour id stepsArray =
  { id
  , phase: TourInactive
  , steps: stepsArray
  , config: defaultConfig
  , visitedSteps: []
  }

-- | Get the tour ID
tourId :: forall msg. TourState msg -> TourId
tourId state = state.id

-- | Get the current step (if active)
currentStep :: forall msg. TourState msg -> Maybe (Step msg)
currentStep state = case state.phase of
  TourActive idx -> index state.steps idx
  TourPaused idx -> index state.steps idx
  _ -> Nothing

-- | Get the current step index (0-based)
currentStepIndex :: forall msg. TourState msg -> Maybe Int
currentStepIndex state = case state.phase of
  TourActive idx -> Just idx
  TourPaused idx -> Just idx
  _ -> Nothing

-- | Get the total number of steps
totalSteps :: forall msg. TourState msg -> Int
totalSteps state = length state.steps

-- | Get progress through the tour (for progress indicators)
progress :: forall msg. TourState msg -> Maybe Progress
progress state = case currentStepIndex state of
  Just idx -> Just (mkProgress (idx + 1) (totalSteps state))
  Nothing -> Nothing

-- | Get the current phase
phase :: forall msg. TourState msg -> TourPhase
phase state = state.phase

-- | Get all steps
steps :: forall msg. TourState msg -> Array (Step msg)
steps state = state.steps

-- | Check if we can advance to the next step
canGoNext :: forall msg. TourState msg -> Boolean
canGoNext state = case state.phase of
  TourActive idx -> idx < length state.steps - 1
  _ -> false

-- | Check if we can go to the previous step
canGoPrev :: forall msg. TourState msg -> Boolean
canGoPrev state = case state.phase of
  TourActive idx -> idx > 0
  _ -> false

-- | Check if we're on the first step
isFirstStep :: forall msg. TourState msg -> Boolean
isFirstStep state = case state.phase of
  TourActive idx -> idx == 0
  _ -> false

-- | Check if we're on the last step
isLastStep :: forall msg. TourState msg -> Boolean
isLastStep state = case state.phase of
  TourActive idx -> idx == length state.steps - 1
  _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // tour messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | All possible tour events
-- |
-- | These messages represent every action that can affect tour state.
-- | The update function pattern-matches on these to produce state transitions.
data TourMsg msg
  -- Lifecycle
  = StartTour
    -- ^ Begin the tour from step 0
  | PauseTour
    -- ^ Pause the tour (e.g., waiting for user action)
  | ResumeTour
    -- ^ Resume from paused state
  | SkipTour
    -- ^ User wants to skip the remaining tour
  | CompleteTour
    -- ^ Tour completed successfully
  | DismissTour DismissReason
    -- ^ User dismissed the tour
  
  -- Navigation
  | NextStep
    -- ^ Advance to the next step
  | PrevStep
    -- ^ Go to the previous step
  | GoToStep Int
    -- ^ Jump to a specific step index
  | GoToStepById StepId
    -- ^ Jump to a step by its ID
  | Restart
    -- ^ Restart the tour from the beginning
  
  -- Timing
  | SnoozeTour Milliseconds
    -- ^ Defer the tour for later
  
  -- Target resolution
  | TargetResolved Int
    -- ^ Target element found for step
  | TargetNotFound Int
    -- ^ Target element not found
  
  -- Custom actions
  | CustomAction msg
    -- ^ Application-specific action

derive instance functorTourMsg :: Functor TourMsg
derive instance genericTourMsg :: Generic (TourMsg msg) _

instance showTourMsg :: Show msg => Show (TourMsg msg) where
  show = genericShow

-- | Reason for tour dismissal (for analytics)
data DismissReason
  = ClickedClose
    -- ^ User clicked the close button
  | PressedEscape
    -- ^ User pressed Escape key
  | ClickedOverlay
    -- ^ User clicked the overlay background
  | NavigatedAway
    -- ^ User navigated to a different page
  | Timeout
    -- ^ Tour timed out (if auto-dismiss is enabled)

derive instance eqDismissReason :: Eq DismissReason
derive instance genericDismissReason :: Generic DismissReason _

instance showDismissReason :: Show DismissReason where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // tour configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration options for tour behavior
type TourConfig =
  { overlayColor :: String
    -- ^ CSS color for the overlay (e.g., "rgba(0,0,0,0.75)")
  , overlayOpacity :: Number
    -- ^ Overlay opacity (0.0 to 1.0)
  , keyboardNavEnabled :: Boolean
    -- ^ Allow arrow key navigation
  , closeOnOverlayClick :: Boolean
    -- ^ Dismiss tour when clicking overlay
  , closeOnEscape :: Boolean
    -- ^ Dismiss tour on Escape key
  , showProgress :: Boolean
    -- ^ Display progress indicator
  }

-- | Default tour configuration
defaultConfig :: TourConfig
defaultConfig =
  { overlayColor: "rgba(0, 0, 0, 0.75)"
  , overlayOpacity: 0.75
  , keyboardNavEnabled: true
  , closeOnOverlayClick: false
  , closeOnEscape: true
  , showProgress: true
  }

-- | Set overlay color
withOverlayColor :: String -> TourConfig -> TourConfig
withOverlayColor color cfg = cfg { overlayColor = color }

-- | Set overlay opacity
withOverlayOpacity :: Number -> TourConfig -> TourConfig
withOverlayOpacity opacity cfg = cfg { overlayOpacity = opacity }

-- | Enable/disable keyboard navigation
withKeyboardNav :: Boolean -> TourConfig -> TourConfig
withKeyboardNav enabled cfg = cfg { keyboardNavEnabled = enabled }

-- | Enable/disable close on overlay click
withCloseOnOverlay :: Boolean -> TourConfig -> TourConfig
withCloseOnOverlay enabled cfg = cfg { closeOnOverlayClick = enabled }

-- | Enable/disable close on Escape
withCloseOnEscape :: Boolean -> TourConfig -> TourConfig
withCloseOnEscape enabled cfg = cfg { closeOnEscape = enabled }
