-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // tour // msg
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Message Algebra for Product Tours
-- |
-- | This module provides the complete message vocabulary for tour events.
-- | All possible tour actions are represented as a bounded ADT, enabling:
-- | - Complete pattern matching (no missing cases)
-- | - Deterministic behavior
-- | - Serializable event log
-- |
-- | ## Architecture
-- |
-- | The tour follows the Elm architecture:
-- | ```
-- | State × Msg → State × [Cmd]
-- | view :: State → Element Msg
-- | ```
-- |
-- | All messages are pure data. Side effects are expressed as Cmd values
-- | that the runtime interprets.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Msg as Msg
-- |
-- | handleMsg :: Msg.TourMsg MyAppMsg -> AppState -> { state :: AppState, cmds :: Array Cmd }
-- | handleMsg msg state = case msg of
-- |   Msg.NextStep -> advanceToNextStep state
-- |   Msg.PrevStep -> goToPrevStep state
-- |   Msg.CustomAction appMsg -> handleAppMsg appMsg state
-- |   ...
-- | ```
module Hydrogen.Tour.Msg
  ( -- * Tour Messages
    TourMsg(..)
    -- * Lifecycle Messages
  , LifecycleMsg(..)
    -- * Navigation Messages
  , NavigationMsg(..)
    -- * Target Messages
  , TargetMsg(..)
    -- * Animation Messages
  , AnimationMsg(..)
    -- * Interaction Messages
  , InteractionMsg(..)
  , SwipeDir(..)
    -- * Dismiss Reasons
  , DismissReason(..)
    -- * Snooze Duration
  , SnoozeDuration(..)
  , snoozeToMs
    -- * Event Metadata
  , EventMeta
  , EventSource(..)
  , withTimestamp
  , withSource
    -- * Message Helpers
  , isLifecycleMsg
  , isNavigationMsg
  , isTargetMsg
  , isAnimationMsg
  , isInteractionMsg
  , msgCategory
  , MsgCategory(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Show.Generic (genericShow)
import Hydrogen.Tour.Target (ResolutionError, TargetRect)
import Hydrogen.Tour.Types (Milliseconds(Milliseconds), StepId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // tour messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | All possible tour events
-- |
-- | This is the complete vocabulary of actions that can affect tour state.
-- | The ADT is designed for:
-- | - Pattern matching in update functions
-- | - Serialization for analytics/replay
-- | - Type-safe message handling
data TourMsg msg
  -- Lifecycle
  = Lifecycle LifecycleMsg
    -- ^ Tour lifecycle events
  
  -- Navigation
  | Navigation NavigationMsg
    -- ^ Step navigation events
  
  -- Target Resolution
  | Target TargetMsg
    -- ^ Target element events
  
  -- Animation
  | Animation AnimationMsg
    -- ^ Animation lifecycle events
  
  -- User Interaction
  | Interaction InteractionMsg
    -- ^ Direct user interaction
  
  -- Custom Application Message
  | CustomAction msg
    -- ^ Application-specific action

derive instance functorTourMsg :: Functor TourMsg
derive instance genericTourMsg :: Generic (TourMsg msg) _

instance showTourMsg :: Show msg => Show (TourMsg msg) where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // lifecycle messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tour lifecycle events
-- |
-- | These messages control the overall tour state machine:
-- | Inactive → Active → Completed/Dismissed/Skipped
data LifecycleMsg
  = StartTour
    -- ^ Begin the tour from step 0
  | StartTourAt StepId
    -- ^ Begin at specific step
  | PauseTour
    -- ^ Pause (e.g., waiting for user action)
  | ResumeTour
    -- ^ Resume from paused state
  | CompleteTour
    -- ^ User completed all steps
  | SkipTour
    -- ^ User wants to skip remaining steps
  | DismissTour DismissReason
    -- ^ User dismissed the tour
  | SnoozeTour SnoozeDuration
    -- ^ Defer for later
  | RestartTour
    -- ^ Start over from beginning
  | ResetTour
    -- ^ Clear all state (including persistence)

derive instance eqLifecycleMsg :: Eq LifecycleMsg
derive instance genericLifecycleMsg :: Generic LifecycleMsg _

instance showLifecycleMsg :: Show LifecycleMsg where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // navigation messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Step navigation events
-- |
-- | Control which step is currently active.
data NavigationMsg
  = NextStep
    -- ^ Advance to next step
  | PrevStep
    -- ^ Go to previous step
  | GoToStep Int
    -- ^ Jump to step by index (0-based)
  | GoToStepById StepId
    -- ^ Jump to step by ID
  | FirstStep
    -- ^ Go to first step
  | LastStep
    -- ^ Go to last step
  | JumpForward Int
    -- ^ Jump N steps forward
  | JumpBackward Int
    -- ^ Jump N steps backward

derive instance eqNavigationMsg :: Eq NavigationMsg
derive instance genericNavigationMsg :: Generic NavigationMsg _

instance showNavigationMsg :: Show NavigationMsg where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // target messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Target element events
-- |
-- | Handle target resolution and observation.
data TargetMsg
  = ResolveTarget Int
    -- ^ Request resolution for step N
  | TargetResolved Int TargetRect
    -- ^ Target found with bounds
  | TargetNotFound Int ResolutionError
    -- ^ Target resolution failed
  | TargetMoved Int TargetRect
    -- ^ Target position changed (mutation observed)
  | TargetRemoved Int
    -- ^ Target element was removed from DOM
  | TargetVisible Int
    -- ^ Target scrolled into view
  | TargetHidden Int
    -- ^ Target scrolled out of view
  | RefreshTarget Int
    -- ^ Force re-resolution

derive instance eqTargetMsg :: Eq TargetMsg
derive instance genericTargetMsg :: Generic TargetMsg _

instance showTargetMsg :: Show TargetMsg where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // animation messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation lifecycle events
-- |
-- | Track animation state for coordination.
data AnimationMsg
  = EnterAnimationStart
    -- ^ Tooltip enter animation started
  | EnterAnimationComplete
    -- ^ Tooltip enter animation complete
  | ExitAnimationStart
    -- ^ Tooltip exit animation started
  | ExitAnimationComplete
    -- ^ Tooltip exit animation complete
  | MorphAnimationStart
    -- ^ Spotlight morph started
  | MorphAnimationComplete
    -- ^ Spotlight morph complete
  | PulseAnimationCycle Int
    -- ^ Pulse animation completed cycle N

derive instance eqAnimationMsg :: Eq AnimationMsg
derive instance genericAnimationMsg :: Generic AnimationMsg _

instance showAnimationMsg :: Show AnimationMsg where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // interaction messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direct user interaction events
-- |
-- | Raw user inputs translated to messages.
data InteractionMsg
  = ClickedNext
    -- ^ Clicked next button
  | ClickedPrev
    -- ^ Clicked previous button
  | ClickedSkip
    -- ^ Clicked skip button
  | ClickedClose
    -- ^ Clicked close button
  | ClickedComplete
    -- ^ Clicked complete/done button
  | ClickedOverlay
    -- ^ Clicked overlay backdrop
  | ClickedProgressDot Int
    -- ^ Clicked progress dot N
  | PressedKey String
    -- ^ Keyboard key pressed
  | SwipedDirection SwipeDir
    -- ^ Swipe gesture detected
  | FocusedTooltip
    -- ^ Tooltip received focus
  | BlurredTooltip
    -- ^ Tooltip lost focus
  | HoveredTarget
    -- ^ Mouse entered target
  | UnhoveredTarget
    -- ^ Mouse left target

derive instance eqInteractionMsg :: Eq InteractionMsg
derive instance genericInteractionMsg :: Generic InteractionMsg _

instance showInteractionMsg :: Show InteractionMsg where
  show = genericShow

-- | Swipe direction
data SwipeDir
  = SwipedLeft
  | SwipedRight
  | SwipedUp
  | SwipedDown

derive instance eqSwipeDir :: Eq SwipeDir
derive instance genericSwipeDir :: Generic SwipeDir _

instance showSwipeDir :: Show SwipeDir where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // dismiss reasons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Why the tour was dismissed
-- |
-- | Used for analytics and to customize post-dismissal behavior.
data DismissReason
  = ReasonClickedClose
    -- ^ User clicked the X button
  | ReasonPressedEscape
    -- ^ User pressed Escape key
  | ReasonClickedOverlay
    -- ^ User clicked the overlay background
  | ReasonClickedSkip
    -- ^ User clicked "Skip tour"
  | ReasonNavigatedAway
    -- ^ User navigated to different page
  | ReasonSessionTimeout
    -- ^ Session timed out
  | ReasonExternalAction
    -- ^ Dismissed by external code
  | ReasonConditionUnmet
    -- ^ Step condition no longer met

derive instance eqDismissReason :: Eq DismissReason
derive instance ordDismissReason :: Ord DismissReason
derive instance genericDismissReason :: Generic DismissReason _

instance showDismissReason :: Show DismissReason where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // snooze duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Snooze duration presets
-- |
-- | Bounded options for "remind me later".
data SnoozeDuration
  = SnoozeOneHour
  | SnoozeFourHours
  | SnoozeOneDay
  | SnoozeOneWeek
  | SnoozeCustom Milliseconds

derive instance eqSnoozeDuration :: Eq SnoozeDuration
derive instance genericSnoozeDuration :: Generic SnoozeDuration _

instance showSnoozeDuration :: Show SnoozeDuration where
  show = genericShow

-- | Convert snooze duration to milliseconds
snoozeToMs :: SnoozeDuration -> Milliseconds
snoozeToMs = case _ of
  SnoozeOneHour -> Milliseconds (60 * 60 * 1000)
  SnoozeFourHours -> Milliseconds (4 * 60 * 60 * 1000)
  SnoozeOneDay -> Milliseconds (24 * 60 * 60 * 1000)
  SnoozeOneWeek -> Milliseconds (7 * 24 * 60 * 60 * 1000)
  SnoozeCustom ms -> ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // event metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Event metadata for analytics/logging
type EventMeta =
  { timestamp :: Maybe Number
    -- ^ Unix timestamp (ms)
  , source :: Maybe EventSource
    -- ^ Where the event originated
  , sessionId :: Maybe String
    -- ^ Session identifier
  , stepIndex :: Maybe Int
    -- ^ Current step when event occurred
  }

-- | Event source
data EventSource
  = SourceUser
    -- ^ Direct user action
  | SourceKeyboard
    -- ^ Keyboard shortcut
  | SourceTimer
    -- ^ Timer/scheduler
  | SourceExternal
    -- ^ External API call
  | SourceInternal
    -- ^ Internal state machine

derive instance eqEventSource :: Eq EventSource
derive instance genericEventSource :: Generic EventSource _

instance showEventSource :: Show EventSource where
  show = genericShow

-- | Add timestamp to metadata
withTimestamp :: Number -> EventMeta -> EventMeta
withTimestamp ts meta = meta { timestamp = Just ts }

-- | Add source to metadata
withSource :: EventSource -> EventMeta -> EventMeta
withSource src meta = meta { source = Just src }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // message helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Message category
data MsgCategory
  = CategoryLifecycle
  | CategoryNavigation
  | CategoryTarget
  | CategoryAnimation
  | CategoryInteraction
  | CategoryCustom

derive instance eqMsgCategory :: Eq MsgCategory
derive instance genericMsgCategory :: Generic MsgCategory _

instance showMsgCategory :: Show MsgCategory where
  show = genericShow

-- | Check if message is lifecycle
isLifecycleMsg :: forall msg. TourMsg msg -> Boolean
isLifecycleMsg = case _ of
  Lifecycle _ -> true
  _ -> false

-- | Check if message is navigation
isNavigationMsg :: forall msg. TourMsg msg -> Boolean
isNavigationMsg = case _ of
  Navigation _ -> true
  _ -> false

-- | Check if message is target-related
isTargetMsg :: forall msg. TourMsg msg -> Boolean
isTargetMsg = case _ of
  Target _ -> true
  _ -> false

-- | Check if message is animation-related
isAnimationMsg :: forall msg. TourMsg msg -> Boolean
isAnimationMsg = case _ of
  Animation _ -> true
  _ -> false

-- | Check if message is interaction
isInteractionMsg :: forall msg. TourMsg msg -> Boolean
isInteractionMsg = case _ of
  Interaction _ -> true
  _ -> false

-- | Get message category
msgCategory :: forall msg. TourMsg msg -> MsgCategory
msgCategory = case _ of
  Lifecycle _ -> CategoryLifecycle
  Navigation _ -> CategoryNavigation
  Target _ -> CategoryTarget
  Animation _ -> CategoryAnimation
  Interaction _ -> CategoryInteraction
  CustomAction _ -> CategoryCustom
