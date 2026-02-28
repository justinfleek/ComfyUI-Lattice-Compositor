-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // tour // update
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour state update function
-- |
-- | Implements the Elm-style update function for tour state transitions.
-- | All state changes flow through this function, making the tour behavior
-- | predictable and testable.
-- |
-- | ```
-- | State × Msg → State × [Cmd]
-- | ```
-- |
-- | ## State Transitions
-- |
-- | ```
-- | TourInactive
-- |     │ StartTour
-- |     ▼
-- | TourActive(0)
-- |     │ NextStep
-- |     ▼
-- | TourActive(n)
-- |     │ NextStep (at last)
-- |     ▼
-- | TourCompleted
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Update as Tour
-- |
-- | -- In your update function
-- | handleAction :: Action -> H.HalogenM State Action () o m Unit
-- | handleAction = case _ of
-- |   TourAction tourMsg -> do
-- |     result <- Tour.update tourMsg <$> H.gets _.tour
-- |     H.modify_ _ { tour = result.state }
-- |     traverse_ handleTourCmd result.cmds
-- | ```
module Hydrogen.Tour.Update
  ( -- * Update Function
    update
  , UpdateResult
    -- * Commands
  , TourCmd(..)
  , AnalyticsEvent(..)
    -- * Helpers
  , findStepByIdIndex
  ) where

import Prelude

import Data.Array (findIndex, length, snoc)
import Data.Maybe (Maybe(Just), fromMaybe)
import Hydrogen.Tour.State
  ( DismissReason
  , TourMsg
      ( StartTour
      , PauseTour
      , ResumeTour
      , SkipTour
      , CompleteTour
      , DismissTour
      , NextStep
      , PrevStep
      , GoToStep
      , GoToStepById
      , Restart
      , SnoozeTour
      , TargetResolved
      , TargetNotFound
      , CustomAction
      )
  , TourState
  )
import Hydrogen.Tour.Step (Step, stepId)
import Hydrogen.Tour.Types (Milliseconds(Milliseconds), StepId, TourPhase(TourActive, TourCompleted, TourDismissed, TourInactive, TourPaused, TourSkipped))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Commands produced by the update function
-- |
-- | These represent side effects that should be performed after state updates.
-- | The runtime (or calling code) is responsible for executing these.
data TourCmd :: Type -> Type
data TourCmd msg
  = ScrollToStep Int
    -- ^ Scroll the step's target element into view
  | ResolveTarget Int
    -- ^ Find and verify the target element exists
  | PersistCompletion
    -- ^ Save that this tour was completed
  | PersistDismissal
    -- ^ Save that this tour was dismissed
  | PersistSnooze Int
    -- ^ Save snooze with expiry timestamp
  | EmitAnalytics AnalyticsEvent
    -- ^ Send analytics event
  | FocusStep Int
    -- ^ Move focus to the step's tooltip
  | RestoreFocus
    -- ^ Return focus to element that had it before tour
  | ScheduleResume Int
    -- ^ Schedule tour resume after N milliseconds

derive instance functorTourCmd :: Functor TourCmd

-- | Analytics events for tracking
data AnalyticsEvent
  = AnalyticsTourStarted
  | AnalyticsTourCompleted
  | AnalyticsTourSkipped Int
  | AnalyticsTourDismissed Int DismissReason
  | AnalyticsStepViewed Int
  | AnalyticsStepCompleted Int
  | AnalyticsTourSnoozed Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // update function
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of an update operation
type UpdateResult msg =
  { state :: TourState msg
  , cmds :: Array (TourCmd msg)
  }

-- | Pure update function for tour state
-- |
-- | Given a message and current state, produces a new state and any commands
-- | that should be executed. This is the heart of the Elm architecture pattern.
update :: forall msg. TourMsg msg -> TourState msg -> UpdateResult msg
update msg state = case msg of
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Lifecycle
  -- ═══════════════════════════════════════════════════════════════════════════
  
  StartTour ->
    case state.phase of
      TourInactive ->
        if length state.steps > 0
        then
          { state: state
              { phase = TourActive 0
              , visitedSteps = [0]
              }
          , cmds: 
              [ EmitAnalytics AnalyticsTourStarted
              , ResolveTarget 0
              , ScrollToStep 0
              , FocusStep 0
              ]
          }
        else noChange state
      _ -> noChange state
  
  PauseTour ->
    case state.phase of
      TourActive idx ->
        { state: state { phase = TourPaused idx }
        , cmds: []
        }
      _ -> noChange state
  
  ResumeTour ->
    case state.phase of
      TourPaused idx ->
        { state: state { phase = TourActive idx }
        , cmds: [FocusStep idx]
        }
      _ -> noChange state
  
  SkipTour ->
    case state.phase of
      TourActive idx ->
        { state: state { phase = TourSkipped idx }
        , cmds: 
            [ EmitAnalytics (AnalyticsTourSkipped idx)
            , PersistDismissal
            , RestoreFocus
            ]
        }
      TourPaused idx ->
        { state: state { phase = TourSkipped idx }
        , cmds: 
            [ EmitAnalytics (AnalyticsTourSkipped idx)
            , PersistDismissal
            , RestoreFocus
            ]
        }
      _ -> noChange state
  
  CompleteTour ->
    case state.phase of
      TourActive idx ->
        { state: state { phase = TourCompleted }
        , cmds: 
            [ EmitAnalytics (AnalyticsStepCompleted idx)
            , EmitAnalytics AnalyticsTourCompleted
            , PersistCompletion
            , RestoreFocus
            ]
        }
      _ -> noChange state
  
  DismissTour reason ->
    case state.phase of
      TourActive idx ->
        { state: state { phase = TourDismissed idx }
        , cmds: 
            [ EmitAnalytics (AnalyticsTourDismissed idx reason)
            , PersistDismissal
            , RestoreFocus
            ]
        }
      TourPaused idx ->
        { state: state { phase = TourDismissed idx }
        , cmds: 
            [ EmitAnalytics (AnalyticsTourDismissed idx reason)
            , PersistDismissal
            , RestoreFocus
            ]
        }
      _ -> noChange state
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Navigation
  -- ═══════════════════════════════════════════════════════════════════════════
  
  NextStep ->
    case state.phase of
      TourActive idx ->
        let nextIdx = idx + 1
        in if nextIdx < length state.steps
           then advanceToStep nextIdx idx state
           else update CompleteTour state
      _ -> noChange state
  
  PrevStep ->
    case state.phase of
      TourActive idx ->
        if idx > 0
        then advanceToStep (idx - 1) idx state
        else noChange state
      _ -> noChange state
  
  GoToStep targetIdx ->
    case state.phase of
      TourActive idx ->
        if targetIdx >= 0 && targetIdx < length state.steps && targetIdx /= idx
        then advanceToStep targetIdx idx state
        else noChange state
      _ -> noChange state
  
  GoToStepById targetId ->
    case state.phase of
      TourActive idx ->
        case findStepByIdIndex targetId state.steps of
          Just targetIdx | targetIdx /= idx -> advanceToStep targetIdx idx state
          _ -> noChange state
      _ -> noChange state
  
  Restart ->
    case state.phase of
      TourCompleted -> update StartTour (state { phase = TourInactive, visitedSteps = [] })
      TourSkipped _ -> update StartTour (state { phase = TourInactive, visitedSteps = [] })
      TourDismissed _ -> update StartTour (state { phase = TourInactive, visitedSteps = [] })
      TourActive _ -> update (GoToStep 0) state
      _ -> noChange state
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Timing
  -- ═══════════════════════════════════════════════════════════════════════════
  
  SnoozeTour (ms) ->
    case state.phase of
      TourActive idx ->
        { state: state { phase = TourPaused idx }
        , cmds: 
            [ EmitAnalytics (AnalyticsTourSnoozed idx)
            , PersistSnooze (unwrapMs ms)
            , RestoreFocus
            ]
        }
      _ -> noChange state
    where
    -- Extract milliseconds as Int
    unwrapMs :: Milliseconds -> Int
    unwrapMs (Milliseconds n) = n
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Target Resolution
  -- ═══════════════════════════════════════════════════════════════════════════
  
  TargetResolved _idx ->
    -- Target found, no state change needed
    noChange state
  
  TargetNotFound idx ->
    -- Graceful degradation: skip to next step
    case state.phase of
      TourActive currentIdx | currentIdx == idx ->
        if idx + 1 < length state.steps
        then advanceToStep (idx + 1) idx state
        else update CompleteTour state
      _ -> noChange state
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Custom Actions
  -- ═══════════════════════════════════════════════════════════════════════════
  
  CustomAction _ ->
    -- Custom actions are handled by the parent component
    -- The tour state doesn't change, but the message is propagated
    noChange state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | No state change, no commands
noChange :: forall msg. TourState msg -> UpdateResult msg
noChange state = { state, cmds: [] }

-- | Advance to a new step with proper tracking
advanceToStep :: forall msg. Int -> Int -> TourState msg -> UpdateResult msg
advanceToStep targetIdx currentIdx state =
  { state: state
      { phase = TourActive targetIdx
      , visitedSteps = 
          if alreadyVisited targetIdx state.visitedSteps
          then state.visitedSteps
          else snoc state.visitedSteps targetIdx
      }
  , cmds:
      [ EmitAnalytics (AnalyticsStepCompleted currentIdx)
      , EmitAnalytics (AnalyticsStepViewed targetIdx)
      , ResolveTarget targetIdx
      , ScrollToStep targetIdx
      , FocusStep targetIdx
      ]
  }

-- | Check if a step has been visited
alreadyVisited :: Int -> Array Int -> Boolean
alreadyVisited idx visited = fromMaybe false (findIndex (_ == idx) visited <#> const true)

-- | Find a step's index by its ID
findStepByIdIndex :: forall msg. StepId -> Array (Step msg) -> Maybe Int
findStepByIdIndex targetId stepsArray = findIndex (\s -> stepId s == targetId) stepsArray
