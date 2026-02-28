# Product Tour State Machine Specification

## Round 2: State Machine & Message Architecture

**Author**: Claude Opus 4.5  
**Date**: 2026-02-24  
**Status**: Specification Draft

---

## 1. State Diagram

### Complete State Enumeration

The tour state machine has **14 distinct states** organized into 4 categories:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              PRE-TOUR STATES                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────┐      LoadTour      ┌─────────────┐     TargetsReady          │
│   │  Idle   │ ─────────────────► │   Loading   │ ─────────────────┐        │
│   └─────────┘                    └─────────────┘                  │        │
│        │                               │                          ▼        │
│        │ StartTour                     │ LoadError         ┌─────────┐     │
│        │ (immediate)                   ▼                   │  Ready  │     │
│        │                        ┌─────────────┐            └─────────┘     │
│        └───────────────────────►│  InitError  │                  │         │
│                                 └─────────────┘                  │         │
│                                                                  │ Start   │
└──────────────────────────────────────────────────────────────────┼─────────┘
                                                                   │
┌──────────────────────────────────────────────────────────────────┼─────────┐
│                              ACTIVE STATES                       │         │
├──────────────────────────────────────────────────────────────────┼─────────┤
│                                                                  ▼         │
│   ┌────────────────┐                                    ┌──────────────┐   │
│   │ EnteringStep n │◄────────────────────────────────── │ Active(n=0)  │   │
│   └────────────────┘                                    └──────────────┘   │
│          │                                                     │ ▲         │
│          │ AnimationComplete                                   │ │         │
│          ▼                                                     │ │         │
│   ┌────────────────┐     RequiresAction      ┌───────────────┐ │ │         │
│   │   Showing n    │ ───────────────────────►│  WaitingFor   │ │ │         │
│   └────────────────┘                         │  n, Action    │ │ │         │
│          │                                   └───────────────┘ │ │         │
│          │ Next/Prev/GoTo                          │           │ │         │
│          ▼                                         │ ActionMet │ │         │
│   ┌────────────────┐                               │           │ │         │
│   │  ExitingStep n │                               ▼           │ │         │
│   └────────────────┘◄──────────────────────────────────────────┘ │         │
│          │                                                       │         │
│          │ AnimationComplete                                     │         │
│          └───────────────────────────────────────────────────────┘         │
│                              (→ EnteringStep n+1)                          │
└────────────────────────────────────────────────────────────────────────────┘

┌────────────────────────────────────────────────────────────────────────────┐
│                              PAUSE STATES                                  │
├────────────────────────────────────────────────────────────────────────────┤
│                                                                            │
│   ┌────────────────┐      ┌───────────────────┐      ┌─────────────────┐   │
│   │  UserPaused n  │      │  TargetHidden n   │      │  WindowBlurred  │   │
│   └────────────────┘      └───────────────────┘      │       n         │   │
│          ▲                        ▲                  └─────────────────┘   │
│          │                        │                          ▲             │
│          │ Pause                  │ TargetLost               │ Blur       │
│          │                        │                          │             │
│   ┌──────┴────────────────────────┴──────────────────────────┴───────┐     │
│   │                         Any Active State                          │     │
│   └───────────────────────────────────────────────────────────────────┘     │
│          │                        │                          │             │
│          │ Resume                 │ TargetFound              │ Focus      │
│          ▼                        ▼                          ▼             │
│   ┌──────────────────────────────────────────────────────────────────┐     │
│   │                    Previous Active State (restored)               │     │
│   └──────────────────────────────────────────────────────────────────┘     │
│                                                                            │
└────────────────────────────────────────────────────────────────────────────┘

┌────────────────────────────────────────────────────────────────────────────┐
│                              TERMINAL STATES                               │
├────────────────────────────────────────────────────────────────────────────┤
│                                                                            │
│   ┌─────────────┐     ┌──────────────────┐     ┌────────────────────────┐  │
│   │  Completed  │     │  Skipped { at }  │     │  Abandoned { at, why } │  │
│   └─────────────┘     └──────────────────┘     └────────────────────────┘  │
│                                                                            │
│   ┌─────────────────────────────────────────────────────────────────────┐  │
│   │                        Error { kind, at, context }                  │  │
│   └─────────────────────────────────────────────────────────────────────┘  │
│                                                                            │
└────────────────────────────────────────────────────────────────────────────┘
```

### PureScript Type Definitions

```purescript
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // tour // phase // refined
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Refined tour phase with explicit sub-states
-- |
-- | This type encodes ALL possible states a tour can be in, eliminating
-- | impossible state combinations at the type level.
data TourPhaseRefined
  -- Pre-tour states
  = PhaseIdle
      -- ^ Tour defined but not started
  | PhaseLoading LoadingContext
      -- ^ Loading tour assets or resolving targets
  | PhaseReady
      -- ^ All prerequisites met, ready to start
  | PhaseInitError InitErrorKind
      -- ^ Failed to initialize (terminal unless retry succeeds)
  
  -- Active states
  | PhaseEnteringStep StepContext AnimationState
      -- ^ Transitioning into a step (spotlight morphing, tooltip entering)
  | PhaseShowing StepContext
      -- ^ Step fully visible and interactive
  | PhaseWaitingFor StepContext WaitCondition
      -- ^ Step visible, waiting for user action
  | PhaseExitingStep StepContext ExitTarget AnimationState
      -- ^ Transitioning out of a step
  
  -- Pause states
  | PhasePausedByUser StepContext PauseReason
      -- ^ User explicitly paused
  | PhasePausedTargetHidden StepContext TargetLostContext
      -- ^ Target element became invisible/removed
  | PhasePausedWindowBlurred StepContext
      -- ^ Window lost focus
  
  -- Terminal states
  | PhaseCompleted CompletionContext
      -- ^ All steps finished successfully
  | PhaseSkipped SkipContext
      -- ^ User chose to skip remaining steps
  | PhaseAbandoned AbandonContext
      -- ^ Tour ended unexpectedly
  | PhaseError TourErrorKind
      -- ^ Unrecoverable error state

derive instance eqTourPhaseRefined :: Eq TourPhaseRefined
derive instance genericTourPhaseRefined :: Generic TourPhaseRefined _

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // context // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Context for a step being displayed
type StepContext =
  { stepIndex :: StepIndex
  , stepId :: StepId
  , enteredAt :: Timestamp
  , targetRect :: Maybe TargetRect
  , tooltipRect :: Maybe TooltipRect
  }

-- | Bounded step index (prevents off-by-one errors)
newtype StepIndex = StepIndex Int

derive instance eqStepIndex :: Eq StepIndex
derive instance ordStepIndex :: Ord StepIndex

-- | Smart constructor that validates bounds
mkStepIndex :: Int -> Int -> Maybe StepIndex
mkStepIndex idx totalSteps
  | idx >= 0 && idx < totalSteps = Just (StepIndex idx)
  | otherwise = Nothing

-- | Loading context tracks what we're waiting for
type LoadingContext =
  { startedAt :: Timestamp
  , targets :: Array TargetResolutionState
  , assetsLoaded :: Boolean
  , storageChecked :: Boolean
  }

-- | Target resolution tracking
data TargetResolutionState
  = TargetPending StepIndex
  | TargetResolved StepIndex TargetRect
  | TargetNotFound StepIndex
  | TargetMultiple StepIndex Int  -- Found N > 1 matches

-- | Animation state for transitions
type AnimationState =
  { progress :: AnimationProgress
  , startedAt :: Timestamp
  , duration :: Milliseconds
  }

-- | Animation progress (bounded 0.0 to 1.0)
newtype AnimationProgress = AnimationProgress Number

mkAnimationProgress :: Number -> AnimationProgress
mkAnimationProgress n = AnimationProgress (clamp 0.0 1.0 n)

-- | What the step is waiting for
data WaitCondition
  = WaitForClick Target
      -- ^ User must click a specific element
  | WaitForInput TestId String
      -- ^ User must enter text matching pattern
  | WaitForNavigation Route
      -- ^ User must navigate to a route
  | WaitForCustom String (Effect Boolean)
      -- ^ Custom predicate check
  | WaitForTimeout Milliseconds
      -- ^ Auto-advance after delay

-- | Where we're transitioning to after exit
data ExitTarget
  = ExitToNext StepIndex
  | ExitToPrev StepIndex
  | ExitToStep StepIndex
  | ExitToComplete
  | ExitToSkip
  | ExitToDismiss DismissReason

-- | Why the target was lost
type TargetLostContext =
  { lostAt :: Timestamp
  , lastKnownRect :: TargetRect
  , searchAttempts :: Int
  , retryStrategy :: RetryStrategy
  }

data RetryStrategy
  = RetryWithBackoff { attempts :: Int, maxAttempts :: Int, nextDelay :: Milliseconds }
  | RetryUntilTimeout { deadline :: Timestamp }
  | NoRetry

-- | Completion tracking
type CompletionContext =
  { completedAt :: Timestamp
  , totalDuration :: Milliseconds
  , stepsCompleted :: Int
  , interactionsCount :: Int
  }

-- | Skip tracking
type SkipContext =
  { skippedAt :: Timestamp
  , atStep :: StepIndex
  , stepsRemaining :: Int
  , reason :: Maybe String
  }

-- | Abandonment tracking
type AbandonContext =
  { abandonedAt :: Timestamp
  , atStep :: StepIndex
  , reason :: AbandonReason
  }

data AbandonReason
  = AbandonNavigatedAway Route
  | AbandonPageUnload
  | AbandonSessionTimeout
  | AbandonMaxRetriesExceeded
  | AbandonForceClosed

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // error // types
-- ═══════════════════════════════════════════════════════════════════════════════

data InitErrorKind
  = InitNoStepsDefined
  | InitStorageUnavailable
  | InitAlreadyRunning TourId
  | InitBlocked BlockReason

data BlockReason
  = BlockedByCompletion
  | BlockedByDismissal
  | BlockedBySnooze Timestamp  -- Expiry time
  | BlockedByAnotherTour TourId

data TourErrorKind
  = ErrorTargetNeverFound StepIndex
  | ErrorPlacementFailed StepIndex PlacementError
  | ErrorStorageFull
  | ErrorNetworkFailure String
  | ErrorTimeout TimeoutContext
  | ErrorInvariantViolation String

data PlacementError
  = PlacementNoSpace
  | PlacementViewportTooSmall
  | PlacementTargetOffscreen

type TimeoutContext =
  { operation :: String
  , elapsed :: Milliseconds
  , limit :: Milliseconds
  }
```

---

## 2. Message Types

### Complete Message Algebra

The message type is organized into **6 categories** with explicit payload types:

```purescript
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // tour // msg // algebra
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete message algebra for product tours
-- |
-- | Every possible event that can affect tour state is represented here.
-- | The type parameter `msg` allows embedding custom application messages.
data TourMsgRefined msg
  -- ═══════════════════════════════════════════════════════════════════════════
  -- User Messages (direct user interaction)
  -- ═══════════════════════════════════════════════════════════════════════════
  = UserClicked ClickContext
      -- ^ User clicked somewhere
  | UserKeyPressed KeyContext
      -- ^ User pressed a key
  | UserGesture GestureContext
      -- ^ Touch/pointer gesture
  | UserScrolled ScrollContext
      -- ^ User scrolled the page
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- System Messages (environment/runtime events)
  -- ═══════════════════════════════════════════════════════════════════════════
  | SysTargetFound StepIndex TargetRect
      -- ^ Target element located
  | SysTargetLost StepIndex TargetLostReason
      -- ^ Target element no longer available
  | SysTargetMoved StepIndex TargetRect
      -- ^ Target element position changed
  | SysViewportChanged ViewportRect
      -- ^ Window resize or orientation change
  | SysWindowFocused
      -- ^ Window gained focus
  | SysWindowBlurred
      -- ^ Window lost focus
  | SysVisibilityChanged VisibilityState
      -- ^ Document visibility changed
  | SysRouteChanged Route Route
      -- ^ Navigation occurred (from, to)
  | SysAnimationFrame Timestamp
      -- ^ Animation frame tick
  | SysTimeout TimeoutId
      -- ^ A scheduled timeout fired
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Navigation Messages (tour flow control)
  -- ═══════════════════════════════════════════════════════════════════════════
  | NavNext
      -- ^ Advance to next step
  | NavPrev
      -- ^ Go to previous step
  | NavGoTo StepIndex
      -- ^ Jump to specific step
  | NavGoToById StepId
      -- ^ Jump to step by ID
  | NavSkip
      -- ^ Skip remaining tour
  | NavClose
      -- ^ Close tour (dismiss)
  | NavRestart
      -- ^ Restart from beginning
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Lifecycle Messages (tour state changes)
  -- ═══════════════════════════════════════════════════════════════════════════
  | LifeStart
      -- ^ Begin the tour
  | LifeStartFrom StepIndex
      -- ^ Begin at specific step (e.g., resume)
  | LifePause PauseReason
      -- ^ Pause the tour
  | LifeResume
      -- ^ Resume from pause
  | LifeComplete
      -- ^ Mark tour as completed
  | LifeSnooze Milliseconds
      -- ^ Defer tour for later
  | LifeReset
      -- ^ Reset all tour state
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Error Messages (failure events)
  -- ═══════════════════════════════════════════════════════════════════════════
  | ErrTargetNotFound StepIndex SearchContext
      -- ^ Could not find target element
  | ErrPlacementFailed StepIndex PlacementError
      -- ^ Could not position tooltip
  | ErrTimeout TimeoutContext
      -- ^ Operation timed out
  | ErrStorageFailed StorageErrorKind
      -- ^ localStorage operation failed
  | ErrNetworkFailed String
      -- ^ Network request failed
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Internal Messages (state machine internals)
  -- ═══════════════════════════════════════════════════════════════════════════
  | InternalAnimationComplete AnimationId
      -- ^ An animation finished
  | InternalRetryTarget StepIndex Int
      -- ^ Retry target resolution (with attempt count)
  | InternalWaitConditionMet WaitCondition
      -- ^ A wait condition was satisfied
  | InternalStorageLoaded TourStorageState
      -- ^ Storage state loaded
  | InternalTick Timestamp
      -- ^ Internal clock tick
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Custom Messages (application-specific)
  -- ═══════════════════════════════════════════════════════════════════════════
  | CustomAction msg
      -- ^ Application-specific message

derive instance functorTourMsgRefined :: Functor TourMsgRefined

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // message // context
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Click event context
type ClickContext =
  { target :: ClickTarget
  , position :: Point2D
  , button :: MouseButton
  , modifiers :: ModifierKeys
  , timestamp :: Timestamp
  }

data ClickTarget
  = ClickedOverlay
  | ClickedTooltip TooltipRegion
  | ClickedTarget
  | ClickedOutside

data TooltipRegion
  = TooltipBody
  | TooltipHeader
  | TooltipCloseButton
  | TooltipButton Int
  | TooltipProgressDot Int

data MouseButton = LeftButton | MiddleButton | RightButton

type ModifierKeys =
  { shift :: Boolean
  , ctrl :: Boolean
  , alt :: Boolean
  , meta :: Boolean
  }

-- | Keyboard event context
type KeyContext =
  { key :: Key
  , code :: KeyCode
  , modifiers :: ModifierKeys
  , repeat :: Boolean
  , timestamp :: Timestamp
  }

data Key
  = KeyArrowLeft
  | KeyArrowRight
  | KeyArrowUp
  | KeyArrowDown
  | KeyEscape
  | KeyEnter
  | KeySpace
  | KeyTab
  | KeyChar Char
  | KeyFunction Int  -- F1-F12
  | KeyOther String

-- | Gesture context
type GestureContext =
  { kind :: GestureKind
  , position :: Point2D
  , delta :: Maybe Point2D
  , velocity :: Maybe Number
  , timestamp :: Timestamp
  }

data GestureKind
  = GestureTap
  | GestureDoubleTap
  | GestureLongPress
  | GestureSwipeLeft
  | GestureSwipeRight
  | GestureSwipeUp
  | GestureSwipeDown
  | GesturePinch Number  -- Scale factor
  | GesturePan Point2D   -- Delta

-- | Scroll context
type ScrollContext =
  { deltaX :: Number
  , deltaY :: Number
  , scrollTop :: Number
  , scrollLeft :: Number
  , timestamp :: Timestamp
  }

-- | Why target was lost
data TargetLostReason
  = TargetRemoved
  | TargetHidden
  | TargetScrolledOut
  | TargetDetached
  | TargetReplacedByOther

-- | Storage error kinds
data StorageErrorKind
  = StorageQuotaExceeded
  | StorageAccessDenied
  | StorageCorrupted String
  | StorageUnavailable

-- | Pause reasons
data PauseReason
  = PausedManually
  | PausedForAction
  | PausedForNavigation
  | PausedTargetLost
  | PausedWindowBlurred
  | PausedDocumentHidden

-- | Search context for target resolution
type SearchContext =
  { selector :: String
  , searchMethod :: SearchMethod
  , attempts :: Int
  , elapsed :: Milliseconds
  }

data SearchMethod
  = SearchBySelector
  | SearchByTestId
  | SearchByAriaRole
  | SearchByCustom

-- | Animation identifiers
newtype AnimationId = AnimationId String

derive instance eqAnimationId :: Eq AnimationId
derive instance ordAnimationId :: Ord AnimationId

-- | Timeout identifiers
newtype TimeoutId = TimeoutId String

derive instance eqTimeoutId :: Eq TimeoutId
derive instance ordTimeoutId :: Ord TimeoutId

-- | Document visibility
data VisibilityState
  = Visible
  | Hidden
  | Prerender
```

---

## 3. Edge Cases

### 3.1 Target Element Removed During Tour

```purescript
-- | Handle target removal with exponential backoff retry
handleTargetLost :: StepIndex -> TourState msg -> UpdateResult msg
handleTargetLost idx state = case state.phase of
  PhaseShowing ctx | ctx.stepIndex == idx ->
    let 
      retryCtx = 
        { lostAt: state.now
        , lastKnownRect: fromMaybe emptyRect ctx.targetRect
        , searchAttempts: 0
        , retryStrategy: RetryWithBackoff 
            { attempts: 0
            , maxAttempts: 5
            , nextDelay: Milliseconds 100
            }
        }
    in
      { state: state { phase = PhasePausedTargetHidden ctx retryCtx }
      , cmds:
          [ ScheduleRetry idx 0 (Milliseconds 100)
          , EmitAnalytics (AnalyticsTargetLost idx)
          ]
      }
  
  PhasePausedTargetHidden ctx retryCtx | ctx.stepIndex == idx ->
    case retryCtx.retryStrategy of
      RetryWithBackoff { attempts, maxAttempts, nextDelay } ->
        if attempts >= maxAttempts
        then
          -- Max retries exceeded: skip to next step or error
          handleMaxRetriesExceeded idx state
        else
          -- Continue waiting, retry is already scheduled
          noChange state
      
      RetryUntilTimeout { deadline } ->
        if state.now >= deadline
        then handleMaxRetriesExceeded idx state
        else noChange state
      
      NoRetry ->
        handleMaxRetriesExceeded idx state
  
  _ -> noChange state

handleMaxRetriesExceeded :: StepIndex -> TourState msg -> UpdateResult msg
handleMaxRetriesExceeded idx state =
  let 
    nextIdx = stepIndexValue idx + 1
    totalSteps = length state.steps
  in
    if nextIdx < totalSteps
    then
      -- Skip to next step
      { state: state { phase = PhaseEnteringStep (mkStepContext nextIdx) initialAnimation }
      , cmds:
          [ EmitAnalytics (AnalyticsStepSkippedTargetMissing idx)
          , ResolveTarget nextIdx
          , FocusStep nextIdx
          ]
      }
    else
      -- No more steps, complete with warning
      { state: state 
          { phase = PhaseCompleted 
              { completedAt: state.now
              , totalDuration: state.now - state.startedAt
              , stepsCompleted: stepIndexValue idx
              , interactionsCount: state.interactionCount
              }
          }
      , cmds:
          [ EmitAnalytics (AnalyticsTourCompletedWithSkips 1)
          , PersistCompletion
          , RestoreFocus
          ]
      }
```

### 3.2 Target Element Moves During Step

```purescript
-- | Handle target position changes
handleTargetMoved :: StepIndex -> TargetRect -> TourState msg -> UpdateResult msg
handleTargetMoved idx newRect state = case state.phase of
  PhaseShowing ctx | ctx.stepIndex == idx ->
    let
      oldRect = ctx.targetRect
      movement = rectDistance oldRect (Just newRect)
    in
      if movement > significantMovementThreshold
      then
        -- Significant movement: reposition tooltip
        { state: state 
            { phase = PhaseShowing (ctx { targetRect = Just newRect })
            }
        , cmds:
            [ RepositionTooltip idx newRect
            , UpdateSpotlight idx newRect
            ]
        }
      else
        -- Minor movement: just update state
        { state: state 
            { phase = PhaseShowing (ctx { targetRect = Just newRect })
            }
        , cmds: []
        }
  
  _ -> noChange state
  where
  significantMovementThreshold = Pixel 10
  
  rectDistance :: Maybe TargetRect -> Maybe TargetRect -> Pixel
  rectDistance (Just r1) (Just r2) = 
    Pixel $ round $ sqrt 
      ((toNumber (r2.x - r1.x)) `pow` 2.0 + 
       (toNumber (r2.y - r1.y)) `pow` 2.0)
  rectDistance _ _ = Pixel 0
```

### 3.3 Window Resize During Step

```purescript
-- | Handle viewport changes
handleViewportChanged :: ViewportRect -> TourState msg -> UpdateResult msg
handleViewportChanged viewport state = case state.phase of
  PhaseShowing ctx ->
    let
      -- Check if target is still visible
      targetVisible = case ctx.targetRect of
        Just rect -> rectIntersects rect viewport
        Nothing -> true
      
      -- Check if tooltip needs repositioning
      tooltipNeedsReposition = case ctx.tooltipRect of
        Just rect -> not (rectContains viewport rect)
        Nothing -> false
    in
      { state: state { viewport = viewport }
      , cmds: 
          (if not targetVisible 
           then [ScrollToStep (stepIndexValue ctx.stepIndex)]
           else [])
          <>
          (if tooltipNeedsReposition
           then [RecalculatePlacement (stepIndexValue ctx.stepIndex)]
           else [])
      }
  
  -- During animation, store new viewport and recalculate after
  PhaseEnteringStep ctx anim ->
    { state: state { viewport = viewport, pendingReposition = true }
    , cmds: []
    }
  
  _ -> 
    { state: state { viewport = viewport }
    , cmds: []
    }
```

### 3.4 User Navigates Away and Returns

```purescript
-- | Handle route changes
handleRouteChanged :: Route -> Route -> TourState msg -> UpdateResult msg
handleRouteChanged fromRoute toRoute state = case state.phase of
  PhaseShowing ctx ->
    let
      currentStep = index state.steps (stepIndexValue ctx.stepIndex)
      targetOnNewRoute = case currentStep of
        Just step -> stepTargetRoute step == Just toRoute
        Nothing -> false
    in
      if targetOnNewRoute
      then
        -- Target might be on new route, try to find it
        { state: state { phase = PhasePausedByUser ctx PausedForNavigation }
        , cmds:
            [ Delay 100.0 (InternalRetryTarget ctx.stepIndex 0)
            ]
        }
      else
        -- Target definitely not on new route, pause tour
        { state: state 
            { phase = PhasePausedByUser ctx PausedForNavigation
            , pausedRoute = Just toRoute
            }
        , cmds:
            [ ShowPausedIndicator
            , EmitAnalytics (AnalyticsNavigatedDuringTour ctx.stepIndex fromRoute toRoute)
            ]
        }
  
  PhasePausedByUser ctx PausedForNavigation ->
    case state.pausedRoute of
      Just expectedRoute | toRoute == expectedRoute ->
        -- User returned to paused route
        { state: state { pausedRoute = Nothing }
        , cmds:
            [ Delay 300.0 LifeResume
            , ResolveTarget (stepIndexValue ctx.stepIndex)
            ]
        }
      _ ->
        noChange state
  
  _ -> noChange state

-- | Store in TourState for resume capability
type TourStateExtended msg =
  { -- ... existing fields ...
  , pausedRoute :: Maybe Route
  , pausedStepIndex :: Maybe StepIndex
  }
```

### 3.5 Multiple Tours Competing

```purescript
-- | Tour priority system
newtype TourPriority = TourPriority Int

derive instance eqTourPriority :: Eq TourPriority
derive instance ordTourPriority :: Ord TourPriority

data TourPriorityLevel
  = Critical    -- Must show (onboarding, security)
  | High        -- Important feature introduction
  | Normal      -- Standard tours
  | Low         -- Nice-to-have tips
  | Background  -- Only when nothing else active

tourPriorityToInt :: TourPriorityLevel -> Int
tourPriorityToInt = case _ of
  Critical -> 100
  High -> 75
  Normal -> 50
  Low -> 25
  Background -> 0

-- | Tour queue manager (lives outside individual tour state)
type TourQueueState =
  { activeTour :: Maybe TourId
  , queuedTours :: Array QueuedTour
  , blockedTours :: Array BlockedTour
  }

type QueuedTour =
  { tourId :: TourId
  , priority :: TourPriority
  , queuedAt :: Timestamp
  , expiresAt :: Maybe Timestamp
  }

type BlockedTour =
  { tourId :: TourId
  , reason :: BlockReason
  , blockedAt :: Timestamp
  }

-- | Attempt to start a tour (may queue or block)
requestTourStart :: TourId -> TourPriority -> TourQueueState -> RequestResult
requestTourStart tourId priority queue = case queue.activeTour of
  Nothing ->
    -- No tour active, start immediately
    StartImmediately
  
  Just activeId ->
    let activePriority = lookupTourPriority activeId queue
    in
      if priority > activePriority
      then
        -- Higher priority: interrupt current tour
        InterruptAndStart { interruptedTour: activeId }
      else
        -- Lower priority: queue for later
        QueueForLater { position: calculateQueuePosition priority queue }

data RequestResult
  = StartImmediately
  | InterruptAndStart { interruptedTour :: TourId }
  | QueueForLater { position :: Int }
  | Blocked BlockReason
```

### 3.6 Nested Tours (Tour Within Tour)

```purescript
-- | Nested tour support via tour stack
type TourStack =
  { current :: TourState msg
  , suspended :: Array SuspendedTour
  }

type SuspendedTour =
  { state :: TourState msg
  , suspendedAt :: Timestamp
  , reason :: SuspendReason
  }

data SuspendReason
  = SuspendedForNestedTour TourId
  | SuspendedForUserAction
  | SuspendedForNavigation

-- | Push a nested tour onto the stack
pushNestedTour :: TourState msg -> TourStack -> TourStack
pushNestedTour nested stack =
  { current: nested
  , suspended: snoc stack.suspended
      { state: stack.current
      , suspendedAt: nested.startedAt
      , reason: SuspendedForNestedTour (tourId nested)
      }
  }

-- | Pop back to parent tour
popToParentTour :: TourStack -> Maybe TourStack
popToParentTour stack = case unsnoc stack.suspended of
  Just { init, last } ->
    Just { current: last.state, suspended: init }
  Nothing ->
    Nothing
```

### 3.7 Network Failure During Server Persistence

```purescript
-- | Persistence with retry and local fallback
data PersistenceStrategy
  = PersistLocalOnly
  | PersistLocalThenSync
  | PersistSyncRequired

type PersistenceResult =
  { local :: PersistenceStatus
  , remote :: PersistenceStatus
  }

data PersistenceStatus
  = PersistSuccess
  | PersistFailed PersistenceError
  | PersistPending
  | PersistNotAttempted

data PersistenceError
  = LocalStorageFull
  | LocalStorageUnavailable
  | NetworkTimeout
  | NetworkError String
  | ServerError Int String

-- | Persist completion with graceful degradation
persistCompletion :: TourId -> CompletionContext -> Effect PersistenceResult
persistCompletion tourId ctx = do
  -- Always attempt local first
  localResult <- attemptLocalPersist tourId ctx
  
  case localResult of
    PersistFailed LocalStorageFull ->
      -- Try to clear old data and retry
      clearOldTourData
      retryLocalResult <- attemptLocalPersist tourId ctx
      
      -- Attempt remote regardless of local result
      remoteResult <- attemptRemotePersist tourId ctx
      pure { local: retryLocalResult, remote: remoteResult }
    
    _ -> do
      -- Attempt remote sync
      remoteResult <- attemptRemotePersist tourId ctx
      pure { local: localResult, remote: remoteResult }

-- | Handle persistence failure in update
handlePersistenceFailure :: PersistenceResult -> TourState msg -> UpdateResult msg
handlePersistenceFailure result state =
  case result.local, result.remote of
    PersistSuccess, _ ->
      -- Local succeeded, remote can retry later
      noChange state
    
    PersistFailed err, _ ->
      -- Local failed, add to retry queue
      { state: state 
          { pendingPersistence = snoc state.pendingPersistence
              { tourId: state.id
              , action: PersistCompletionAction
              , attempts: 1
              , lastError: err
              }
          }
      , cmds: [ SchedulePersistenceRetry (Milliseconds 5000) ]
      }
    
    _, _ -> noChange state
```

### 3.8 LocalStorage Full

```purescript
-- | Storage quota management
type StorageQuotaInfo =
  { used :: Int
  , total :: Int
  , available :: Int
  }

-- | Handle quota exceeded error
handleStorageQuotaExceeded :: TourState msg -> UpdateResult msg
handleStorageQuotaExceeded state =
  { state: state { storageWarning = Just StorageQuotaExceeded }
  , cmds:
      [ ClearOldestTourData 5  -- Clear 5 oldest entries
      , RetryLastStorage
      , LogWarning "Storage quota exceeded, cleared old tour data"
      ]
  }

-- | Calculate storage cleanup priority
type StorageEntry =
  { key :: String
  , size :: Int
  , lastAccessed :: Timestamp
  , priority :: CleanupPriority
  }

data CleanupPriority
  = CanDeleteImmediately  -- Expired snoozes
  | CanDeleteSoon         -- Old completed tours
  | PreferToKeep          -- Recent completions
  | NeverDelete           -- Current session data

-- | Identify entries safe to clean
identifyCleanupCandidates :: Array StorageEntry -> Array StorageEntry
identifyCleanupCandidates entries =
  filter (\e -> e.priority == CanDeleteImmediately || e.priority == CanDeleteSoon)
    $ sortBy (comparing _.lastAccessed)
    $ entries
```

### 3.9 Animation Interrupted

```purescript
-- | Animation state with interruption handling
data AnimationLifecycle
  = AnimationRunning AnimationState
  | AnimationCompleted
  | AnimationInterrupted InterruptReason

data InterruptReason
  = InterruptedByUserAction
  | InterruptedByNavigation
  | InterruptedByNewAnimation AnimationId
  | InterruptedByTimeout

-- | Handle animation interruption
handleAnimationInterrupted :: AnimationId -> InterruptReason -> TourState msg -> UpdateResult msg
handleAnimationInterrupted animId reason state = case state.phase of
  PhaseEnteringStep ctx anim ->
    -- Complete the step entry immediately
    { state: state { phase = PhaseShowing ctx }
    , cmds:
        [ CancelAnimation animId
        , SnapToFinalPosition ctx.stepIndex
        , EmitAnalytics (AnalyticsAnimationSkipped animId)
        ]
    }
  
  PhaseExitingStep ctx target anim ->
    -- Complete the transition immediately
    case target of
      ExitToNext nextIdx ->
        { state: state { phase = PhaseEnteringStep (mkStepContext nextIdx) initialAnimation }
        , cmds:
            [ CancelAnimation animId
            , ResolveTarget nextIdx
            ]
        }
      
      ExitToComplete ->
        { state: state { phase = PhaseCompleted (mkCompletionContext ctx state) }
        , cmds:
            [ CancelAnimation animId
            , PersistCompletion
            , RestoreFocus
            ]
        }
      
      _ -> noChange state
  
  _ -> noChange state

-- | Snap animations to final state
snapToFinalPosition :: StepIndex -> Cmd msg
snapToFinalPosition idx = Batch
  [ SetSpotlightOpacity 0.0
  , SetTooltipOpacity 1.0
  , SetTooltipPosition (finalTooltipPosition idx)
  , SetSpotlightRect (finalSpotlightRect idx)
  ]
```

---

## 4. Command Effects

### Complete Effect Taxonomy

```purescript
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // tour // cmd // effects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | All possible tour commands (effects)
data TourCmd msg
  -- ═══════════════════════════════════════════════════════════════════════════
  -- DOM Effects
  -- ═══════════════════════════════════════════════════════════════════════════
  = DomScrollToElement StepIndex ScrollOptions
      -- ^ Scroll target element into view
  | DomScrollToPosition Point2D ScrollOptions
      -- ^ Scroll to absolute position
  | DomFocusElement FocusTarget
      -- ^ Move focus to element
  | DomBlurElement String
      -- ^ Remove focus from element
  | DomSetAttribute String String String
      -- ^ Set attribute on element (id, attr, value)
  | DomAddClass String String
      -- ^ Add class to element
  | DomRemoveClass String String
      -- ^ Remove class from element
  | DomLockScroll Boolean
      -- ^ Enable/disable page scroll
  | DomSetInert String Boolean
      -- ^ Set inert attribute (for accessibility)
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Spotlight Effects
  -- ═══════════════════════════════════════════════════════════════════════════
  | SpotlightShow StepIndex HighlightConfig
      -- ^ Show spotlight around target
  | SpotlightHide
      -- ^ Hide spotlight
  | SpotlightMorph StepIndex StepIndex Milliseconds
      -- ^ Animate spotlight between targets
  | SpotlightUpdateRect TargetRect
      -- ^ Update spotlight position
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Tooltip Effects
  -- ═══════════════════════════════════════════════════════════════════════════
  | TooltipShow StepIndex PlacementConfig
      -- ^ Show tooltip for step
  | TooltipHide
      -- ^ Hide tooltip
  | TooltipReposition PlacementConfig
      -- ^ Recalculate tooltip position
  | TooltipAnimate TooltipAnimationType Milliseconds
      -- ^ Animate tooltip
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Storage Effects
  -- ═══════════════════════════════════════════════════════════════════════════
  | StorageMarkCompleted TourId Timestamp
      -- ^ Persist completion
  | StorageMarkDismissed TourId Timestamp DismissReason
      -- ^ Persist dismissal
  | StorageSetSnooze TourId Timestamp
      -- ^ Persist snooze expiry
  | StorageClearSnooze TourId
      -- ^ Clear snooze
  | StorageSaveProgress TourId StepIndex
      -- ^ Save current progress (for resume)
  | StorageClear TourId
      -- ^ Clear all data for tour
  | StorageLoadState TourId (Maybe TourStorageState -> msg)
      -- ^ Load stored state
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Analytics Effects
  -- ═══════════════════════════════════════════════════════════════════════════
  | AnalyticsTrack AnalyticsEvent
      -- ^ Track analytics event
  | AnalyticsIdentify UserId
      -- ^ Identify user for analytics
  | AnalyticsFlush
      -- ^ Flush analytics queue
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Timer Effects
  -- ═══════════════════════════════════════════════════════════════════════════
  | TimerDelay Milliseconds msg
      -- ^ Dispatch message after delay
  | TimerInterval Milliseconds msg TimerId
      -- ^ Dispatch message repeatedly
  | TimerCancel TimerId
      -- ^ Cancel a timer
  | TimerRequestAnimationFrame (Timestamp -> msg)
      -- ^ Request animation frame
  | TimerCancelAnimationFrame AnimationFrameId
      -- ^ Cancel animation frame request
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Target Resolution Effects
  -- ═══════════════════════════════════════════════════════════════════════════
  | TargetResolve StepIndex Target (TargetResult -> msg)
      -- ^ Find and measure target element
  | TargetObserve StepIndex Target
      -- ^ Start observing target for changes
  | TargetStopObserving StepIndex
      -- ^ Stop observing target
  | TargetMeasure String (TargetRect -> msg)
      -- ^ Measure element dimensions
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Accessibility Effects
  -- ═══════════════════════════════════════════════════════════════════════════
  | A11yAnnounce String AnnouncementPriority
      -- ^ Screen reader announcement
  | A11yTrapFocus String
      -- ^ Trap focus within element
  | A11yReleaseFocus
      -- ^ Release focus trap
  | A11yUpdateLiveRegion String
      -- ^ Update ARIA live region
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Batching
  -- ═══════════════════════════════════════════════════════════════════════════
  | CmdNone
      -- ^ No effect
  | CmdBatch (Array (TourCmd msg))
      -- ^ Execute multiple commands

derive instance functorTourCmd :: Functor TourCmd

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // effect // subtypes
-- ═══════════════════════════════════════════════════════════════════════════════

type ScrollOptions =
  { behavior :: ScrollBehavior
  , block :: ScrollAlignment
  , inline :: ScrollAlignment
  }

data ScrollAlignment
  = AlignStart
  | AlignCenter
  | AlignEnd
  | AlignNearest

data FocusTarget
  = FocusTooltip StepIndex
  | FocusFirstButton StepIndex
  | FocusCloseButton
  | FocusElement String
  | FocusPrevious  -- Restore previous focus

data TooltipAnimationType
  = AnimateEnter
  | AnimateExit
  | AnimateShift  -- Position change

data TargetResult
  = TargetFound TargetRect
  | TargetNotFoundResult
  | TargetMultipleFound Int

newtype TimerId = TimerId String
newtype AnimationFrameId = AnimationFrameId Int

data AnnouncementPriority
  = Polite
  | Assertive

-- | Comprehensive analytics events
data AnalyticsEvent
  = TourStarted TourId
  | TourCompleted TourId CompletionContext
  | TourSkipped TourId SkipContext
  | TourDismissed TourId DismissReason StepIndex
  | TourSnoozed TourId Milliseconds StepIndex
  | TourResumed TourId StepIndex
  | TourErrored TourId TourErrorKind
  | StepViewed TourId StepIndex StepId
  | StepCompleted TourId StepIndex Milliseconds
  | StepSkipped TourId StepIndex
  | ButtonClicked TourId StepIndex ButtonId
  | TargetLost TourId StepIndex
  | TargetRecovered TourId StepIndex Milliseconds
  | AnimationSkipped TourId AnimationId
  | NavigationDuringTour TourId StepIndex Route Route
```

---

## 5. Undo/Redo and History Management

### History Model

```purescript
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // tour // history
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | History entry for undo/redo
type HistoryEntry =
  { stepIndex :: StepIndex
  , visitedAt :: Timestamp
  , action :: NavigationAction
  , context :: HistoryContext
  }

data NavigationAction
  = NavForward        -- User clicked Next
  | NavBackward       -- User clicked Prev
  | NavJumped         -- User jumped via progress dots
  | NavBranched       -- User took a branch path
  | NavAutoAdvanced   -- Step auto-advanced

type HistoryContext =
  { timeSpent :: Milliseconds
      -- ^ Time spent on the step
  , interactionsOnStep :: Int
      -- ^ Number of interactions (clicks, etc.)
  , scrollPositionBefore :: Point2D
      -- ^ Scroll position when entering step
  , focusedElementBefore :: Maybe String
      -- ^ What had focus
  }

-- | History stack with bounded size
type TourHistory =
  { entries :: Array HistoryEntry
  , maxSize :: Int
  , currentIndex :: Int  -- Points to current position in history
  }

defaultMaxHistorySize :: Int
defaultMaxHistorySize = 50

-- | Create empty history
emptyHistory :: TourHistory
emptyHistory =
  { entries: []
  , maxSize: defaultMaxHistorySize
  , currentIndex: -1
  }

-- | Push new entry, truncating if necessary
pushHistory :: HistoryEntry -> TourHistory -> TourHistory
pushHistory entry history =
  let
    -- If we're not at the end, truncate forward history (like typical undo/redo)
    truncated = take (history.currentIndex + 1) history.entries
    -- Add new entry
    withNew = snoc truncated entry
    -- Trim if over max size (remove oldest)
    trimmed = 
      if length withNew > history.maxSize
      then drop (length withNew - history.maxSize) withNew
      else withNew
  in
    { entries: trimmed
    , maxSize: history.maxSize
    , currentIndex: length trimmed - 1
    }

-- | Check if we can go back
canGoBack :: TourHistory -> Boolean
canGoBack history = history.currentIndex > 0

-- | Check if we can go forward (after going back)
canGoForward :: TourHistory -> Boolean
canGoForward history = history.currentIndex < length history.entries - 1

-- | Go back in history
goBack :: TourHistory -> Maybe { history :: TourHistory, entry :: HistoryEntry }
goBack history =
  if canGoBack history
  then
    let newIndex = history.currentIndex - 1
    in case index history.entries newIndex of
      Just entry ->
        Just 
          { history: history { currentIndex = newIndex }
          , entry: entry
          }
      Nothing -> Nothing
  else Nothing

-- | Go forward in history
goForward :: TourHistory -> Maybe { history :: TourHistory, entry :: HistoryEntry }
goForward history =
  if canGoForward history
  then
    let newIndex = history.currentIndex + 1
    in case index history.entries newIndex of
      Just entry ->
        Just 
          { history: history { currentIndex = newIndex }
          , entry: entry
          }
      Nothing -> Nothing
  else Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // branch // history
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Branch point in tour (for non-linear tours)
type BranchPoint =
  { stepIndex :: StepIndex
  , branchId :: BranchId
  , chosenPath :: PathId
  , availablePaths :: Array PathId
  , chosenAt :: Timestamp
  }

newtype BranchId = BranchId String
newtype PathId = PathId String

-- | Extended history with branch tracking
type BranchHistory =
  { mainHistory :: TourHistory
  , branches :: Array BranchPoint
  }

-- | When going back past a branch point
handleBranchBacktrack :: BranchPoint -> TourState msg -> UpdateResult msg
handleBranchBacktrack branch state =
  -- Offer choice: revisit same path or try different path?
  { state: state 
      { phase = PhaseWaitingFor 
          (mkStepContext branch.stepIndex)
          (WaitForBranchChoice branch.availablePaths)
      }
  , cmds:
      [ ShowBranchChoiceUI branch
      ]
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // restoration // logic
-- ═══════════════════════════════════════════════════════════════════════════════

-- | What gets restored when going back
type RestorationContext =
  { stepToRestore :: StepIndex
  , scrollPosition :: Maybe Point2D
  , focusTarget :: Maybe String
  , formState :: Maybe FormSnapshot
  }

-- | Snapshot form state for restoration
type FormSnapshot =
  { inputs :: Array { id :: String, value :: String }
  , selections :: Array { id :: String, selected :: Array Int }
  , checkboxes :: Array { id :: String, checked :: Boolean }
  }

-- | Handle "Back" navigation
handleNavBack :: TourState msg -> UpdateResult msg
handleNavBack state = case goBack state.history of
  Nothing ->
    -- Can't go back further
    noChange state
  
  Just { history, entry } ->
    -- Build restoration context
    let
      restoration =
        { stepToRestore: entry.stepIndex
        , scrollPosition: Just entry.context.scrollPositionBefore
        , focusTarget: entry.context.focusedElementBefore
        , formState: Nothing  -- Could store form state if needed
        }
    in
      { state: state 
          { history = history
          , phase = PhaseExitingStep 
              (currentStepContext state)
              (ExitToPrev entry.stepIndex)
              initialAnimation
          }
      , cmds:
          [ EmitAnalytics (AnalyticsNavBack (currentStepIndex state) entry.stepIndex)
          , CmdBatch
              [ case restoration.scrollPosition of
                  Just pos -> DomScrollToPosition pos { behavior: Smooth, block: AlignCenter, inline: AlignNearest }
                  Nothing -> CmdNone
              , case restoration.focusTarget of
                  Just target -> DomFocusElement (FocusElement target)
                  Nothing -> CmdNone
              ]
          ]
      }

-- | History depth limits
type HistoryLimits =
  { maxStepsBack :: Int
      -- ^ How many steps user can go back (default: all visited)
  , preserveFormState :: Boolean
      -- ^ Whether to snapshot form state
  , preserveScrollPosition :: Boolean
      -- ^ Whether to restore scroll position
  }

defaultHistoryLimits :: HistoryLimits
defaultHistoryLimits =
  { maxStepsBack: 999  -- Effectively unlimited
  , preserveFormState: false  -- Off by default (can be expensive)
  , preserveScrollPosition: true
  }
```

---

## 6. State Transition Validation

### Lawful State Transitions

```purescript
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // transition // laws
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Valid transitions from each state
-- |
-- | This function encodes the state machine's transition table.
-- | If a transition is not listed here, it is INVALID.
validTransitions :: TourPhaseRefined -> Array TourPhaseRefined
validTransitions = case _ of
  -- Pre-tour states
  PhaseIdle ->
    [ PhaseLoading mempty
    , PhaseReady
    , PhaseInitError InitNoStepsDefined
    ]
  
  PhaseLoading _ ->
    [ PhaseReady
    , PhaseInitError InitStorageUnavailable
    ]
  
  PhaseReady ->
    [ PhaseEnteringStep mempty mempty  -- Start tour
    , PhaseIdle  -- Cancel before start
    ]
  
  PhaseInitError _ ->
    [ PhaseIdle  -- Reset and retry
    ]
  
  -- Active states
  PhaseEnteringStep _ _ ->
    [ PhaseShowing mempty  -- Animation complete
    , PhasePausedTargetHidden mempty mempty  -- Target lost during enter
    , PhasePausedWindowBlurred mempty  -- Window lost focus
    , PhaseError (ErrorTargetNeverFound (StepIndex 0))  -- Target never found
    ]
  
  PhaseShowing _ ->
    [ PhaseExitingStep mempty (ExitToNext (StepIndex 0)) mempty  -- Navigate
    , PhaseWaitingFor mempty (WaitForClick NoTarget)  -- Wait for action
    , PhasePausedByUser mempty PausedManually  -- User pause
    , PhasePausedTargetHidden mempty mempty  -- Target lost
    , PhasePausedWindowBlurred mempty  -- Focus lost
    , PhaseSkipped mempty  -- User skipped
    , PhaseAbandoned mempty  -- Navigated away
    , PhaseCompleted mempty  -- Tour finished
    ]
  
  PhaseWaitingFor _ _ ->
    [ PhaseShowing mempty  -- Condition met, return to showing
    , PhaseExitingStep mempty (ExitToNext (StepIndex 0)) mempty  -- Condition met + advance
    , PhasePausedByUser mempty PausedManually
    , PhaseSkipped mempty
    , PhaseAbandoned mempty
    ]
  
  PhaseExitingStep _ _ _ ->
    [ PhaseEnteringStep mempty mempty  -- Entering next step
    , PhaseCompleted mempty  -- Was last step
    , PhaseSkipped mempty  -- User skipped during exit
    , PhaseAbandoned mempty  -- Navigated away during exit
    ]
  
  -- Pause states (can resume to previous active state)
  PhasePausedByUser _ _ ->
    [ PhaseShowing mempty  -- Resume
    , PhaseSkipped mempty  -- User skipped while paused
    , PhaseAbandoned mempty  -- User left
    ]
  
  PhasePausedTargetHidden _ _ ->
    [ PhaseShowing mempty  -- Target found again
    , PhaseExitingStep mempty (ExitToNext (StepIndex 0)) mempty  -- Skip to next
    , PhaseError (ErrorTargetNeverFound (StepIndex 0))  -- Max retries exceeded
    ]
  
  PhasePausedWindowBlurred _ ->
    [ PhaseShowing mempty  -- Window focused again
    , PhaseAbandoned mempty  -- User never returned
    ]
  
  -- Terminal states (no valid outgoing transitions)
  PhaseCompleted _ -> []
  PhaseSkipped _ -> []
  PhaseAbandoned _ -> []
  PhaseError _ -> []

-- | Check if a transition is valid
isValidTransition :: TourPhaseRefined -> TourPhaseRefined -> Boolean
isValidTransition from to =
  any (phaseMatches to) (validTransitions from)

-- | Phase pattern matching (ignores payload)
phaseMatches :: TourPhaseRefined -> TourPhaseRefined -> Boolean
phaseMatches a b = phaseTag a == phaseTag b

-- | Get phase tag for matching
phaseTag :: TourPhaseRefined -> String
phaseTag = case _ of
  PhaseIdle -> "Idle"
  PhaseLoading _ -> "Loading"
  PhaseReady -> "Ready"
  PhaseInitError _ -> "InitError"
  PhaseEnteringStep _ _ -> "EnteringStep"
  PhaseShowing _ -> "Showing"
  PhaseWaitingFor _ _ -> "WaitingFor"
  PhaseExitingStep _ _ _ -> "ExitingStep"
  PhasePausedByUser _ _ -> "PausedByUser"
  PhasePausedTargetHidden _ _ -> "PausedTargetHidden"
  PhasePausedWindowBlurred _ -> "PausedWindowBlurred"
  PhaseCompleted _ -> "Completed"
  PhaseSkipped _ -> "Skipped"
  PhaseAbandoned _ -> "Abandoned"
  PhaseError _ -> "Error"

-- | Assert transition validity (for testing/debugging)
assertValidTransition 
  :: forall m
   . MonadThrow Error m
  => TourPhaseRefined 
  -> TourPhaseRefined 
  -> m Unit
assertValidTransition from to =
  unless (isValidTransition from to) $
    throwError $ error $ 
      "Invalid state transition: " <> phaseTag from <> " -> " <> phaseTag to
```

---

## 7. Complete State Type

```purescript
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // complete // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete tour state with all tracking
type TourStateComplete msg =
  { -- Identity
    id :: TourId
  , version :: Int  -- For optimistic updates
  
  -- Phase (the core state machine)
  , phase :: TourPhaseRefined
  
  -- Step definitions
  , steps :: Array (Step msg)
  , totalSteps :: Int
  
  -- Configuration
  , config :: TourConfig
  
  -- Timing
  , startedAt :: Maybe Timestamp
  , now :: Timestamp
  
  -- History
  , history :: TourHistory
  , visitedSteps :: Set StepIndex
  
  -- Target tracking
  , targetStates :: Map StepIndex TargetResolutionState
  , activeObservers :: Set StepIndex
  
  -- Animation state
  , activeAnimations :: Map AnimationId AnimationState
  , pendingAnimations :: Array AnimationId
  
  -- Persistence
  , pendingPersistence :: Array PendingPersistAction
  , storageState :: Maybe TourStorageState
  
  -- Viewport
  , viewport :: ViewportRect
  , scrollPosition :: Point2D
  
  -- Focus management
  , previousFocus :: Maybe String
  , currentFocus :: Maybe String
  
  -- Analytics
  , interactionCount :: Int
  , eventsQueue :: Array AnalyticsEvent
  
  -- Error recovery
  , errorCount :: Int
  , lastError :: Maybe TourErrorKind
  
  -- Nested tours
  , parentTour :: Maybe TourId
  , childTour :: Maybe TourId
  }

-- | Initialize complete tour state
initTourComplete 
  :: forall msg
   . TourId 
  -> Array (Step msg) 
  -> TourConfig 
  -> Timestamp
  -> TourStateComplete msg
initTourComplete tourId stepsArray config now =
  { id: tourId
  , version: 0
  , phase: PhaseIdle
  , steps: stepsArray
  , totalSteps: length stepsArray
  , config: config
  , startedAt: Nothing
  , now: now
  , history: emptyHistory
  , visitedSteps: Set.empty
  , targetStates: Map.empty
  , activeObservers: Set.empty
  , activeAnimations: Map.empty
  , pendingAnimations: []
  , pendingPersistence: []
  , storageState: Nothing
  , viewport: defaultViewport
  , scrollPosition: { x: 0.0, y: 0.0 }
  , previousFocus: Nothing
  , currentFocus: Nothing
  , interactionCount: 0
  , eventsQueue: []
  , errorCount: 0
  , lastError: Nothing
  , parentTour: Nothing
  , childTour: Nothing
  }
```

---

## Summary

This specification defines a **bulletproof state machine** with:

1. **14 distinct states** covering all phases of tour lifecycle
2. **6 message categories** with complete payloads
3. **9 edge case handlers** with graceful degradation
4. **8 effect categories** for all side effects
5. **History management** with undo/redo and branch support
6. **Transition validation** ensuring only legal state changes

The design follows Hydrogen's principles:
- All types are bounded where possible
- No impossible states representable
- Effects are pure data (commands)
- State transitions are explicit and validated
- Edge cases handled deterministically

This specification can be directly implemented in PureScript following the existing `Hydrogen.Tour.*` module structure.
