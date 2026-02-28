-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // tour // msg
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour Msg — Message ADT for tour state changes.
-- |
-- | ## Architecture
-- |
-- | TourMsg defines all possible interactions with a tour:
-- | - Navigation (next, prev, goto, skip)
-- | - Lifecycle (start, pause, resume, complete)
-- | - User interactions (click, keyboard, gesture)
-- | - System events (target found, scroll complete)
-- |
-- | These messages are the ONLY way to change tour state.
-- | The update function handles each message deterministically.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Tour.Msg (TourMsg(..))
-- |
-- | handleTour :: TourMsg -> State -> State
-- | handleTour msg state = case msg of
-- |   NextStep -> advanceStep state
-- |   PrevStep -> retreatStep state
-- |   GoToStep idx -> jumpToStep idx state
-- |   ...
-- | ```

module Hydrogen.Element.Compound.Tour.Msg
  ( -- * Tour Messages
    TourMsg
      ( -- Navigation
        NextStep
      , PrevStep
      , GoToStep
      , FirstStep
      , LastStep
      , SkipTour
      , SkipToEnd
        -- Lifecycle
      , StartTour
      , PauseTour
      , ResumeTour
      , CompleteTour
      , RestartTour
      , ResetTour
        -- Target events
      , TargetFound
      , TargetLost
      , TargetReady
      , TargetTimeout
        -- Scroll events
      , ScrollStart
      , ScrollComplete
      , ScrollError
        -- Highlight events
      , HighlightShow
      , HighlightHide
      , HighlightClick
      , OverlayClick
        -- Tooltip events
      , TooltipShow
      , TooltipHide
      , TooltipFocus
      , TooltipBlur
        -- Interaction events
      , TaskComplete
      , ChecklistItemToggle
      , InputChange
      , HotspotClick
        -- Keyboard events
      , KeyDown
      , FocusTrap
        -- Gesture events
      , SwipeLeft
      , SwipeRight
      , PinchZoom
        -- Persistence events
      , ProgressLoaded
      , ProgressSaved
      , ProgressCleared
        -- Analytics events
      , TrackView
      , TrackInteraction
      , TrackComplete
        -- Error events
      , TourError
      , Recover
      )
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Element.Compound.Tour.Types (StepId, StepIndex)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // tour msg
-- ═════════════════════════════════════════════════════════════════════════════

-- | All possible messages for tour state changes.
-- |
-- | The tour runtime produces these messages in response to:
-- | - User interactions (clicks, keyboard, gestures)
-- | - System events (DOM mutations, scroll, resize)
-- | - Timer events (autoplay, timeouts)
-- | - External triggers (API calls, feature flags)
data TourMsg
  -- ═══════════════════════════════════════════════════════════════════════════
  -- NAVIGATION
  -- ═══════════════════════════════════════════════════════════════════════════
  
  -- | Advance to the next step
  = NextStep
  
  -- | Go back to the previous step
  | PrevStep
  
  -- | Jump to a specific step by index
  | GoToStep StepIndex
  
  -- | Jump to the first step
  | FirstStep
  
  -- | Jump to the last step
  | LastStep
  
  -- | Skip the tour entirely (user chose not to continue)
  | SkipTour
  
  -- | Skip remaining steps and go to completion
  | SkipToEnd
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- LIFECYCLE
  -- ═══════════════════════════════════════════════════════════════════════════
  
  -- | Start the tour from the beginning
  | StartTour
  
  -- | Pause the tour (hide UI, maintain state)
  | PauseTour
  
  -- | Resume a paused tour
  | ResumeTour
  
  -- | Complete the tour successfully
  | CompleteTour
  
  -- | Restart the tour from the beginning
  | RestartTour
  
  -- | Reset tour state (clear progress, start fresh)
  | ResetTour
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- TARGET EVENTS
  -- ═══════════════════════════════════════════════════════════════════════════
  
  -- | Target element was found in DOM
  | TargetFound StepId
  
  -- | Target element was removed from DOM
  | TargetLost StepId
  
  -- | Target element is ready (visible, interactive)
  | TargetReady StepId
  
  -- | Timeout waiting for target element
  | TargetTimeout StepId
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- SCROLL EVENTS
  -- ═══════════════════════════════════════════════════════════════════════════
  
  -- | Started scrolling to target
  | ScrollStart
  
  -- | Finished scrolling to target
  | ScrollComplete
  
  -- | Error during scroll (target not reachable)
  | ScrollError String
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- HIGHLIGHT EVENTS
  -- ═══════════════════════════════════════════════════════════════════════════
  
  -- | Highlight overlay is now visible
  | HighlightShow
  
  -- | Highlight overlay was hidden
  | HighlightHide
  
  -- | User clicked on highlighted target
  | HighlightClick
  
  -- | User clicked on overlay (outside target)
  | OverlayClick
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- TOOLTIP EVENTS
  -- ═══════════════════════════════════════════════════════════════════════════
  
  -- | Tooltip is now visible
  | TooltipShow
  
  -- | Tooltip was hidden
  | TooltipHide
  
  -- | Tooltip received keyboard focus
  | TooltipFocus
  
  -- | Tooltip lost keyboard focus
  | TooltipBlur
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- INTERACTION EVENTS
  -- ═══════════════════════════════════════════════════════════════════════════
  
  -- | User completed required task for current step
  | TaskComplete StepId
  
  -- | User toggled a checklist item
  | ChecklistItemToggle StepId String Boolean
  
  -- | User changed input value
  | InputChange StepId String
  
  -- | User clicked a hotspot
  | HotspotClick StepId String
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- KEYBOARD EVENTS
  -- ═══════════════════════════════════════════════════════════════════════════
  
  -- | Key was pressed (for custom handling)
  | KeyDown String
  
  -- | Focus was trapped/released
  | FocusTrap Boolean
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- GESTURE EVENTS
  -- ═══════════════════════════════════════════════════════════════════════════
  
  -- | User swiped left (prev step)
  | SwipeLeft
  
  -- | User swiped right (next step)
  | SwipeRight
  
  -- | User pinched to zoom
  | PinchZoom Number
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- PERSISTENCE EVENTS
  -- ═══════════════════════════════════════════════════════════════════════════
  
  -- | Progress was loaded from storage
  | ProgressLoaded StepIndex
  
  -- | Progress was saved to storage
  | ProgressSaved
  
  -- | Progress was cleared from storage
  | ProgressCleared
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- ANALYTICS EVENTS
  -- ═══════════════════════════════════════════════════════════════════════════
  
  -- | Track step view
  | TrackView StepId
  
  -- | Track user interaction
  | TrackInteraction StepId String
  
  -- | Track tour completion
  | TrackComplete Boolean  -- ^ True = completed, False = skipped
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- ERROR EVENTS
  -- ═══════════════════════════════════════════════════════════════════════════
  
  -- | An error occurred during tour
  | TourError String
  
  -- | Attempt to recover from error
  | Recover

derive instance eqTourMsg :: Eq TourMsg

instance showTourMsg :: Show TourMsg where
  show NextStep = "NextStep"
  show PrevStep = "PrevStep"
  show (GoToStep idx) = "GoToStep(" <> show idx <> ")"
  show FirstStep = "FirstStep"
  show LastStep = "LastStep"
  show SkipTour = "SkipTour"
  show SkipToEnd = "SkipToEnd"
  show StartTour = "StartTour"
  show PauseTour = "PauseTour"
  show ResumeTour = "ResumeTour"
  show CompleteTour = "CompleteTour"
  show RestartTour = "RestartTour"
  show ResetTour = "ResetTour"
  show (TargetFound sid) = "TargetFound(" <> show sid <> ")"
  show (TargetLost sid) = "TargetLost(" <> show sid <> ")"
  show (TargetReady sid) = "TargetReady(" <> show sid <> ")"
  show (TargetTimeout sid) = "TargetTimeout(" <> show sid <> ")"
  show ScrollStart = "ScrollStart"
  show ScrollComplete = "ScrollComplete"
  show (ScrollError e) = "ScrollError(" <> e <> ")"
  show HighlightShow = "HighlightShow"
  show HighlightHide = "HighlightHide"
  show HighlightClick = "HighlightClick"
  show OverlayClick = "OverlayClick"
  show TooltipShow = "TooltipShow"
  show TooltipHide = "TooltipHide"
  show TooltipFocus = "TooltipFocus"
  show TooltipBlur = "TooltipBlur"
  show (TaskComplete sid) = "TaskComplete(" <> show sid <> ")"
  show (ChecklistItemToggle sid itemId checked) = 
    "ChecklistItemToggle(" <> show sid <> ", " <> itemId <> ", " <> show checked <> ")"
  show (InputChange sid val) = "InputChange(" <> show sid <> ", " <> val <> ")"
  show (HotspotClick sid spot) = "HotspotClick(" <> show sid <> ", " <> spot <> ")"
  show (KeyDown key) = "KeyDown(" <> key <> ")"
  show (FocusTrap trapped) = "FocusTrap(" <> show trapped <> ")"
  show SwipeLeft = "SwipeLeft"
  show SwipeRight = "SwipeRight"
  show (PinchZoom scale) = "PinchZoom(" <> show scale <> ")"
  show (ProgressLoaded idx) = "ProgressLoaded(" <> show idx <> ")"
  show ProgressSaved = "ProgressSaved"
  show ProgressCleared = "ProgressCleared"
  show (TrackView sid) = "TrackView(" <> show sid <> ")"
  show (TrackInteraction sid action) = "TrackInteraction(" <> show sid <> ", " <> action <> ")"
  show (TrackComplete completed) = "TrackComplete(" <> show completed <> ")"
  show (TourError err) = "TourError(" <> err <> ")"
  show Recover = "Recover"
