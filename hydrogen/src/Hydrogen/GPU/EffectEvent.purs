-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // gpu // effect-event
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | EffectEvent — Triggers, Events, and State Snapshots for Effects
-- |
-- | ## Design Philosophy
-- |
-- | Hyper-responsive UIs need predictable event handling:
-- |
-- | - **Triggers**: Conditions that start effects (hover, focus, scroll, time)
-- | - **Events**: Discrete happenings during effect lifecycle
-- | - **Snapshots**: Serializable state for undo/save/replay
-- |
-- | ## Why This Matters at Billion-Agent Scale
-- |
-- | With billions of agents, effects must be:
-- | 1. **Deterministic**: Same trigger → same effect (always)
-- | 2. **Serializable**: State can be saved, replayed, debugged
-- | 3. **Composable**: Triggers combine with boolean algebra
-- | 4. **UUID5 identified**: Same effect config → same identity
-- |
-- | ## Architecture
-- |
-- | ```
-- | Trigger → EffectEvent → StateTransition → Snapshot
-- |    ↓          ↓              ↓              ↓
-- |  Input     Emitted       Applied        Saved/Undo
-- | ```
-- |
-- | All pure data. No callbacks. No side effects.
-- | The runtime interprets these at 60/120fps.

module Hydrogen.GPU.EffectEvent
  ( -- * Triggers
    EffectTrigger(..)
  , TriggerCondition(..)
  , TriggerCombinator(..)
  , MouseTrigger(..)
  , KeyboardTrigger(..)
  , FocusTrigger(..)
  , Modifier(..)
  , TimeTrigger(..)
  , ScrollTrigger(..)
  , ScrollDir(..)
  , ViewportTrigger(..)
  , Orientation(..)
  , AnimationTrigger(..)
  , AnimPhase(..)
  
  -- * Event Supporting Types
  , AnimDirection(..)
  , SwipeDirection(..)
  , SnapshotDiff
  
  -- * Events
  , EffectEvent(..)
  , EffectLifecycle(..)
  , AnimationEvent(..)
  , InteractionEvent(..)
  
  -- * Snapshots
  , EffectSnapshot(..)
  , FrameSnapshot(..)
  , AnimationSnapshot(..)
  , SpringSnapshot(..)
  , RenderSnapshot(..)
  
  -- * State Transitions
  , StateTransition(..)
  , TransitionResult(..)
  
  -- * Trigger Evaluation
  , evaluateTrigger
  , evaluateTriggerWithTime
  , evaluateTimeTrigger
  , triggerAnd
  , triggerOr
  , triggerNot
  , triggerAll
  , triggerAny
  , isConditionMet
  , isConditionNotMet
  
  -- * Snapshot Operations
  , createSnapshot
  , restoreSnapshot
  , diffSnapshots
  , snapshotId
  
  -- * Event Construction
  , effectStarted
  , effectUpdated
  , effectCompleted
  , effectCancelled
  , animationTick
  , interactionOccurred
  
  -- * Presets
  , onHover
  , onFocus
  , onActive
  , onVisible
  , onScroll
  , afterDelay
  , atProgress
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , not
  , (<>)
  , (-)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (>=)
  , (<=)
  , ($)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // triggers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect trigger — condition that starts/stops effects
-- |
-- | Triggers are pure predicates evaluated against FrameState.
-- | No side effects. No callbacks. Just data.
data EffectTrigger
  = TriggerMouse MouseTrigger
  | TriggerKeyboard KeyboardTrigger
  | TriggerFocus FocusTrigger          -- Focus-based triggers
  | TriggerTime TimeTrigger
  | TriggerScroll ScrollTrigger
  | TriggerViewport ViewportTrigger
  | TriggerAnimation AnimationTrigger
  | TriggerCombined TriggerCombinator
  | TriggerAlways                      -- Always active
  | TriggerNever                       -- Never active

derive instance eqEffectTrigger :: Eq EffectTrigger

instance showEffectTrigger :: Show EffectTrigger where
  show (TriggerMouse m) = "(TriggerMouse " <> show m <> ")"
  show (TriggerKeyboard k) = "(TriggerKeyboard " <> show k <> ")"
  show (TriggerTime t) = "(TriggerTime " <> show t <> ")"
  show (TriggerScroll s) = "(TriggerScroll " <> show s <> ")"
  show (TriggerViewport v) = "(TriggerViewport " <> show v <> ")"
  show (TriggerAnimation a) = "(TriggerAnimation " <> show a <> ")"
  show (TriggerFocus f) = "(TriggerFocus " <> show f <> ")"
  show (TriggerCombined c) = "(TriggerCombined " <> show c <> ")"
  show TriggerAlways = "TriggerAlways"
  show TriggerNever = "TriggerNever"

-- | Trigger condition result
data TriggerCondition
  = ConditionMet        -- Trigger condition is true
  | ConditionNotMet     -- Trigger condition is false
  | ConditionUnknown    -- Cannot evaluate (missing state)

derive instance eqTriggerCondition :: Eq TriggerCondition

-- | Combinator for composing triggers
data TriggerCombinator
  = TriggerAnd EffectTrigger EffectTrigger   -- Both must be true
  | TriggerOr EffectTrigger EffectTrigger    -- Either must be true
  | TriggerNot EffectTrigger                 -- Negation
  | TriggerXor EffectTrigger EffectTrigger   -- Exactly one true

derive instance eqTriggerCombinator :: Eq TriggerCombinator

instance showTriggerCombinator :: Show TriggerCombinator where
  show (TriggerAnd a b) = "(TriggerAnd " <> show a <> " " <> show b <> ")"
  show (TriggerOr a b) = "(TriggerOr " <> show a <> " " <> show b <> ")"
  show (TriggerNot t) = "(TriggerNot " <> show t <> ")"
  show (TriggerXor a b) = "(TriggerXor " <> show a <> " " <> show b <> ")"

-- | Mouse-based triggers
data MouseTrigger
  = MouseHover Int               -- Hovering over element (PickId)
  | MouseNotHover Int            -- Not hovering over element
  | MouseEnter Int               -- Just started hovering
  | MouseLeave Int               -- Just stopped hovering
  | MouseDown Int                -- Button pressed on element
  | MouseUp Int                  -- Button released on element
  | MouseDragging                -- Currently dragging
  | MouseIdle Number             -- No movement for N ms
  | MouseInRegion                -- Mouse in defined region
      { x :: Number, y :: Number, width :: Number, height :: Number }

derive instance eqMouseTrigger :: Eq MouseTrigger

instance showMouseTrigger :: Show MouseTrigger where
  show (MouseHover id) = "(MouseHover " <> show id <> ")"
  show (MouseNotHover id) = "(MouseNotHover " <> show id <> ")"
  show (MouseEnter id) = "(MouseEnter " <> show id <> ")"
  show (MouseLeave id) = "(MouseLeave " <> show id <> ")"
  show (MouseDown id) = "(MouseDown " <> show id <> ")"
  show (MouseUp id) = "(MouseUp " <> show id <> ")"
  show MouseDragging = "MouseDragging"
  show (MouseIdle ms) = "(MouseIdle " <> show ms <> ")"
  show (MouseInRegion _) = "(MouseInRegion ...)"

-- | Keyboard-based triggers
data KeyboardTrigger
  = KeyDown String               -- Key pressed (key code)
  | KeyUp String                 -- Key released
  | KeyHeld String Number        -- Key held for N ms
  | ModifierActive Modifier      -- Modifier key active

derive instance eqKeyboardTrigger :: Eq KeyboardTrigger

instance showKeyboardTrigger :: Show KeyboardTrigger where
  show (KeyDown k) = "(KeyDown " <> k <> ")"
  show (KeyUp k) = "(KeyUp " <> k <> ")"
  show (KeyHeld k ms) = "(KeyHeld " <> k <> " " <> show ms <> ")"
  show (ModifierActive m) = "(ModifierActive " <> show m <> ")"

-- | Focus-based triggers
-- |
-- | Focus triggers handle keyboard navigation and accessibility focus states.
-- | These work with the focus management system to track which element has
-- | keyboard focus, enabling proper keyboard-driven UI interactions.
data FocusTrigger
  = FocusGained Int              -- Element gained focus (PickId)
  | FocusLost Int                -- Element lost focus (PickId)
  | FocusWithin Int              -- Element or descendant has focus (PickId)
  | FocusVisible Int             -- Focus visible (keyboard navigation, not mouse)

derive instance eqFocusTrigger :: Eq FocusTrigger

instance showFocusTrigger :: Show FocusTrigger where
  show (FocusGained id) = "(FocusGained " <> show id <> ")"
  show (FocusLost id) = "(FocusLost " <> show id <> ")"
  show (FocusWithin id) = "(FocusWithin " <> show id <> ")"
  show (FocusVisible id) = "(FocusVisible " <> show id <> ")"

-- | Modifier keys
data Modifier
  = ModShift
  | ModCtrl
  | ModAlt
  | ModMeta

derive instance eqModifier :: Eq Modifier

instance showModifier :: Show Modifier where
  show ModShift = "Shift"
  show ModCtrl = "Ctrl"
  show ModAlt = "Alt"
  show ModMeta = "Meta"

-- | Time-based triggers
data TimeTrigger
  = AfterDelay Number            -- After N ms since trigger registration
  | AtTime Number                -- At specific timestamp
  | Interval Number              -- Every N ms
  | FrameCount Int               -- After N frames
  | Elapsed Number Number        -- Between start and end time

derive instance eqTimeTrigger :: Eq TimeTrigger

instance showTimeTrigger :: Show TimeTrigger where
  show (AfterDelay ms) = "(AfterDelay " <> show ms <> ")"
  show (AtTime t) = "(AtTime " <> show t <> ")"
  show (Interval ms) = "(Interval " <> show ms <> ")"
  show (FrameCount n) = "(FrameCount " <> show n <> ")"
  show (Elapsed start end) = "(Elapsed " <> show start <> " " <> show end <> ")"

-- | Scroll-based triggers
data ScrollTrigger
  = ScrollPosition Number        -- Scroll position threshold (px)
  | ScrollProgress Number        -- Scroll progress (0.0-1.0)
  | ScrollDirection ScrollDir    -- Scrolling in direction
  | ScrollVelocity Number        -- Scroll velocity threshold

derive instance eqScrollTrigger :: Eq ScrollTrigger

instance showScrollTrigger :: Show ScrollTrigger where
  show (ScrollPosition px) = "(ScrollPosition " <> show px <> ")"
  show (ScrollProgress p) = "(ScrollProgress " <> show p <> ")"
  show (ScrollDirection d) = "(ScrollDirection " <> show d <> ")"
  show (ScrollVelocity v) = "(ScrollVelocity " <> show v <> ")"

-- | Scroll direction
data ScrollDir = ScrollUp | ScrollDown | ScrollLeft | ScrollRight

derive instance eqScrollDir :: Eq ScrollDir

instance showScrollDir :: Show ScrollDir where
  show ScrollUp = "ScrollUp"
  show ScrollDown = "ScrollDown"
  show ScrollLeft = "ScrollLeft"
  show ScrollRight = "ScrollRight"

-- | Viewport-based triggers
data ViewportTrigger
  = ViewportWidth Number Number    -- Min, max width
  | ViewportHeight Number Number   -- Min, max height
  | ViewportVisible Int            -- Element visible (PickId)
  | ViewportOrientation Orientation

derive instance eqViewportTrigger :: Eq ViewportTrigger

instance showViewportTrigger :: Show ViewportTrigger where
  show (ViewportWidth min' max') = "(ViewportWidth " <> show min' <> " " <> show max' <> ")"
  show (ViewportHeight min' max') = "(ViewportHeight " <> show min' <> " " <> show max' <> ")"
  show (ViewportVisible id) = "(ViewportVisible " <> show id <> ")"
  show (ViewportOrientation o) = "(ViewportOrientation " <> show o <> ")"

-- | Device orientation
data Orientation = Portrait | Landscape

derive instance eqOrientation :: Eq Orientation

instance showOrientation :: Show Orientation where
  show Portrait = "Portrait"
  show Landscape = "Landscape"

-- | Animation-based triggers
data AnimationTrigger
  = AnimationProgress Number Number  -- Progress between min and max
  | AnimationComplete Int            -- Animation handle completed
  | AnimationPhaseIs AnimPhase       -- Current phase matches
  | SpringAtRest Int                 -- Spring handle at rest

derive instance eqAnimationTrigger :: Eq AnimationTrigger

instance showAnimationTrigger :: Show AnimationTrigger where
  show (AnimationProgress min' max') = "(AnimationProgress " <> show min' <> " " <> show max' <> ")"
  show (AnimationComplete h) = "(AnimationComplete " <> show h <> ")"
  show (AnimationPhaseIs p) = "(AnimationPhaseIs " <> show p <> ")"
  show (SpringAtRest h) = "(SpringAtRest " <> show h <> ")"

-- | Animation phase
data AnimPhase = PhaseIdle | PhaseRunning | PhaseComplete | PhasePaused

derive instance eqAnimPhase :: Eq AnimPhase

instance showAnimPhase :: Show AnimPhase where
  show PhaseIdle = "PhaseIdle"
  show PhaseRunning = "PhaseRunning"
  show PhaseComplete = "PhaseComplete"
  show PhasePaused = "PhasePaused"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect event — discrete happening during effect lifecycle
data EffectEvent
  = EventLifecycle EffectLifecycle
  | EventAnimation AnimationEvent
  | EventInteraction InteractionEvent

derive instance eqEffectEvent :: Eq EffectEvent

instance showEffectEvent :: Show EffectEvent where
  show (EventLifecycle e) = "(EventLifecycle " <> show e <> ")"
  show (EventAnimation e) = "(EventAnimation " <> show e <> ")"
  show (EventInteraction e) = "(EventInteraction " <> show e <> ")"

-- | Effect lifecycle events
data EffectLifecycle
  = EffectStarted                -- Effect began execution
      { effectId :: UUID5.UUID5
      , timestamp :: Number
      }
  | EffectUpdated                -- Effect state changed
      { effectId :: UUID5.UUID5
      , timestamp :: Number
      , progress :: Number
      }
  | EffectCompleted              -- Effect finished normally
      { effectId :: UUID5.UUID5
      , timestamp :: Number
      }
  | EffectCancelled              -- Effect was cancelled
      { effectId :: UUID5.UUID5
      , timestamp :: Number
      , reason :: String
      }
  | EffectPaused                 -- Effect paused
      { effectId :: UUID5.UUID5
      , timestamp :: Number
      }
  | EffectResumed                -- Effect resumed
      { effectId :: UUID5.UUID5
      , timestamp :: Number
      }

derive instance eqEffectLifecycle :: Eq EffectLifecycle

instance showEffectLifecycle :: Show EffectLifecycle where
  show (EffectStarted _) = "(EffectStarted ...)"
  show (EffectUpdated _) = "(EffectUpdated ...)"
  show (EffectCompleted _) = "(EffectCompleted ...)"
  show (EffectCancelled _) = "(EffectCancelled ...)"
  show (EffectPaused _) = "(EffectPaused ...)"
  show (EffectResumed _) = "(EffectResumed ...)"

-- | Animation-specific events
data AnimationEvent
  = AnimationTick                -- Per-frame update
      { handle :: Int
      , progress :: Number
      , deltaMs :: Number
      }
  | AnimationKeyframe            -- Keyframe reached
      { handle :: Int
      , keyframeIndex :: Int
      }
  | AnimationLoop                -- Animation looped
      { handle :: Int
      , iteration :: Int
      }
  | AnimationDirectionChange     -- Direction changed (alternate)
      { handle :: Int
      , newDirection :: AnimDirection
      }

derive instance eqAnimationEvent :: Eq AnimationEvent

instance showAnimationEvent :: Show AnimationEvent where
  show (AnimationTick _) = "(AnimationTick ...)"
  show (AnimationKeyframe _) = "(AnimationKeyframe ...)"
  show (AnimationLoop _) = "(AnimationLoop ...)"
  show (AnimationDirectionChange _) = "(AnimationDirectionChange ...)"

-- | Animation direction
data AnimDirection = Forward | Backward

derive instance eqAnimDirection :: Eq AnimDirection

-- | Interaction events
data InteractionEvent
  = Click Int                    -- Element clicked (PickId)
  | DoubleClick Int              -- Element double-clicked
  | LongPress Int Number         -- Element long-pressed (PickId, duration)
  | DragStart Int                -- Drag started
  | DragMove                     -- Drag moved
      { pickId :: Int, deltaX :: Number, deltaY :: Number }
  | DragEnd Int                  -- Drag ended
  | Swipe SwipeDirection Number  -- Swipe gesture (direction, velocity)
  | Pinch Number                 -- Pinch gesture (scale factor)
  | Rotate Number                -- Rotate gesture (degrees)

derive instance eqInteractionEvent :: Eq InteractionEvent

instance showInteractionEvent :: Show InteractionEvent where
  show (Click id) = "(Click " <> show id <> ")"
  show (DoubleClick id) = "(DoubleClick " <> show id <> ")"
  show (LongPress id dur) = "(LongPress " <> show id <> " " <> show dur <> ")"
  show (DragStart id) = "(DragStart " <> show id <> ")"
  show (DragMove _) = "(DragMove ...)"
  show (DragEnd id) = "(DragEnd " <> show id <> ")"
  show (Swipe dir vel) = "(Swipe " <> show dir <> " " <> show vel <> ")"
  show (Pinch s) = "(Pinch " <> show s <> ")"
  show (Rotate deg) = "(Rotate " <> show deg <> ")"

-- | Swipe direction
data SwipeDirection = SwipeUp | SwipeDown | SwipeLeft | SwipeRight

derive instance eqSwipeDirection :: Eq SwipeDirection

instance showSwipeDirection :: Show SwipeDirection where
  show SwipeUp = "SwipeUp"
  show SwipeDown = "SwipeDown"
  show SwipeLeft = "SwipeLeft"
  show SwipeRight = "SwipeRight"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // snapshots
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect state snapshot — serializable for undo/save/replay
newtype EffectSnapshot = EffectSnapshot
  { id :: UUID5.UUID5            -- Snapshot identity
  , timestamp :: Number          -- When snapshot was taken
  , frame :: FrameSnapshot       -- Frame state at snapshot time
  , animations :: Array AnimationSnapshot
  , springs :: Array SpringSnapshot
  , render :: Maybe RenderSnapshot
  }

derive instance eqEffectSnapshot :: Eq EffectSnapshot

instance showEffectSnapshot :: Show EffectSnapshot where
  show (EffectSnapshot s) = "(EffectSnapshot timestamp:" <> show s.timestamp <> ")"

-- | Frame state snapshot
type FrameSnapshot =
  { frameNumber :: Int
  , elapsedMs :: Number
  , mouseX :: Number
  , mouseY :: Number
  , viewportWidth :: Number
  , viewportHeight :: Number
  }

-- | Animation state snapshot
type AnimationSnapshot =
  { handle :: Int
  , progress :: Number
  , phase :: AnimPhase
  , iteration :: Int
  }

-- | Spring state snapshot
type SpringSnapshot =
  { handle :: Int
  , current :: Number
  , target :: Number
  , velocity :: Number
  }

-- | Render state snapshot
type RenderSnapshot =
  { activeEffects :: Array UUID5.UUID5
  , pendingKernels :: Array UUID5.UUID5
  , gpuBudgetUsed :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // state transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | State transition — describes how effect state changes
data StateTransition
  = TransitionStart              -- Effect starting
      { effectId :: UUID5.UUID5
      , trigger :: EffectTrigger
      }
  | TransitionProgress           -- Effect progressing
      { effectId :: UUID5.UUID5
      , from :: Number
      , to :: Number
      }
  | TransitionComplete           -- Effect completing
      { effectId :: UUID5.UUID5
      }
  | TransitionCancel             -- Effect being cancelled
      { effectId :: UUID5.UUID5
      , reason :: String
      }
  | TransitionReset              -- Effect resetting to initial
      { effectId :: UUID5.UUID5
      }

derive instance eqStateTransition :: Eq StateTransition

instance showStateTransition :: Show StateTransition where
  show (TransitionStart _) = "(TransitionStart ...)"
  show (TransitionProgress _) = "(TransitionProgress ...)"
  show (TransitionComplete _) = "(TransitionComplete ...)"
  show (TransitionCancel _) = "(TransitionCancel ...)"
  show (TransitionReset _) = "(TransitionReset ...)"

-- | Result of applying a transition
data TransitionResult
  = TransitionApplied            -- Transition succeeded
  | TransitionRejected String    -- Transition rejected (reason)
  | TransitionQueued             -- Transition queued for later

derive instance eqTransitionResult :: Eq TransitionResult

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // trigger evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate a trigger without frame state (static evaluation).
-- |
-- | Evaluates boolean logic (And, Or, Not, Xor) and constant triggers
-- | (Always, Never). Returns `ConditionUnknown` for triggers that require
-- | runtime state (viewport, mouse, scroll, time, animation progress).
-- |
-- | For full evaluation with frame state, use `evaluateTriggerWithState`
-- | from the runtime module.
evaluateTrigger :: EffectTrigger -> TriggerCondition
evaluateTrigger trigger = case trigger of
  TriggerAlways -> ConditionMet
  TriggerNever -> ConditionNotMet
  TriggerCombined (TriggerAnd a b) ->
    let ra = evaluateTrigger a
        rb = evaluateTrigger b
    in if ra == ConditionMet && rb == ConditionMet
       then ConditionMet
       else if ra == ConditionUnknown || rb == ConditionUnknown
       then ConditionUnknown
       else ConditionNotMet
  TriggerCombined (TriggerOr a b) ->
    let ra = evaluateTrigger a
        rb = evaluateTrigger b
    in if ra == ConditionMet || rb == ConditionMet
       then ConditionMet
       else if ra == ConditionUnknown || rb == ConditionUnknown
       then ConditionUnknown
       else ConditionNotMet
  TriggerCombined (TriggerNot t) ->
    case evaluateTrigger t of
      ConditionMet -> ConditionNotMet
      ConditionNotMet -> ConditionMet
      ConditionUnknown -> ConditionUnknown
  TriggerCombined (TriggerXor a b) ->
    let ra = evaluateTrigger a
        rb = evaluateTrigger b
    in case ra, rb of
      ConditionMet, ConditionNotMet -> ConditionMet
      ConditionNotMet, ConditionMet -> ConditionMet
      ConditionUnknown, _ -> ConditionUnknown
      _, ConditionUnknown -> ConditionUnknown
      _, _ -> ConditionNotMet
  -- All other triggers need frame state to evaluate
  _ -> ConditionUnknown

-- | Combine triggers with AND
triggerAnd :: EffectTrigger -> EffectTrigger -> EffectTrigger
triggerAnd a b = TriggerCombined (TriggerAnd a b)

-- | Combine triggers with OR
triggerOr :: EffectTrigger -> EffectTrigger -> EffectTrigger
triggerOr a b = TriggerCombined (TriggerOr a b)

-- | Negate a trigger
triggerNot :: EffectTrigger -> EffectTrigger
triggerNot t = TriggerCombined (TriggerNot t)

-- | All triggers must be true
triggerAll :: Array EffectTrigger -> EffectTrigger
triggerAll triggers = foldlTriggers triggerAnd TriggerAlways triggers

-- | Any trigger must be true
triggerAny :: Array EffectTrigger -> EffectTrigger
triggerAny triggers = foldlTriggers triggerOr TriggerNever triggers

-- | Helper for folding triggers
foldlTriggers :: (EffectTrigger -> EffectTrigger -> EffectTrigger) -> EffectTrigger -> Array EffectTrigger -> EffectTrigger
foldlTriggers f init arr = case Array.uncons arr of
  Nothing -> init
  Just { head: h, tail: t } -> foldlTriggers f (f init h) t

-- | Evaluate a trigger with time context
-- |
-- | Takes current time in ms and elapsed time since trigger registration.
-- | For time-based triggers, this allows proper evaluation instead of Unknown.
-- |
-- | ## Parameters
-- | - currentTimeMs: Current timestamp in milliseconds
-- | - elapsedMs: Time since trigger was registered
-- | - frameNumber: Current frame number
-- | - trigger: The trigger to evaluate
evaluateTriggerWithTime :: Number -> Number -> Int -> EffectTrigger -> TriggerCondition
evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame trigger = case trigger of
  TriggerAlways -> ConditionMet
  TriggerNever -> ConditionNotMet
  TriggerTime timeTrigger -> 
    evaluateTimeTrigger currentTimeMs elapsedMs currentFrame timeTrigger
  TriggerCombined (TriggerAnd a b) ->
    let ra = evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame a
        rb = evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame b
    in if ra == ConditionMet && rb == ConditionMet
       then ConditionMet
       else if ra == ConditionUnknown || rb == ConditionUnknown
       then ConditionUnknown
       else ConditionNotMet
  TriggerCombined (TriggerOr a b) ->
    let ra = evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame a
        rb = evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame b
    in if ra == ConditionMet || rb == ConditionMet
       then ConditionMet
       else if ra == ConditionUnknown || rb == ConditionUnknown
       then ConditionUnknown
       else ConditionNotMet
  TriggerCombined (TriggerNot t) ->
    case evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame t of
      ConditionMet -> ConditionNotMet
      ConditionNotMet -> ConditionMet
      ConditionUnknown -> ConditionUnknown
  TriggerCombined (TriggerXor a b) ->
    let ra = evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame a
        rb = evaluateTriggerWithTime currentTimeMs elapsedMs currentFrame b
    in case ra, rb of
      ConditionMet, ConditionNotMet -> ConditionMet
      ConditionNotMet, ConditionMet -> ConditionMet
      ConditionUnknown, _ -> ConditionUnknown
      _, ConditionUnknown -> ConditionUnknown
      _, _ -> ConditionNotMet
  -- Mouse, keyboard, scroll, viewport, animation triggers still need full state
  _ -> ConditionUnknown

-- | Evaluate a time-based trigger
-- |
-- | Uses >=, <= for range comparisons. This is where the comparison operators
-- | from Prelude are actually exercised.
evaluateTimeTrigger :: Number -> Number -> Int -> TimeTrigger -> TriggerCondition
evaluateTimeTrigger currentTimeMs elapsedMs currentFrame timeTrigger = case timeTrigger of
  AfterDelay delayMs ->
    if elapsedMs >= delayMs
    then ConditionMet
    else ConditionNotMet
  AtTime targetTimeMs ->
    -- Check if we've reached or passed the target time
    if currentTimeMs >= targetTimeMs
    then ConditionMet
    else ConditionNotMet
  Interval intervalMs ->
    -- Interval triggers are always potentially met (handled by scheduler)
    -- Here we just check if enough time has passed for at least one tick
    if elapsedMs >= intervalMs
    then ConditionMet
    else ConditionNotMet
  FrameCount targetFrames ->
    if currentFrame >= targetFrames
    then ConditionMet
    else ConditionNotMet
  Elapsed startMs endMs ->
    -- Check if current time is within the range [start, end]
    if currentTimeMs >= startMs && currentTimeMs <= endMs
    then ConditionMet
    else if currentTimeMs >= endMs
    then ConditionNotMet  -- Past the window, definitively not met
    else ConditionNotMet  -- Before the window

-- | Check if a condition is met (convenience predicate)
-- |
-- | Useful for filtering or branching on trigger results.
isConditionMet :: TriggerCondition -> Boolean
isConditionMet ConditionMet = true
isConditionMet _ = false

-- | Check if a condition is definitively not met
-- |
-- | Uses `not` for boolean negation. Returns true only when condition
-- | is definitively not met (not Unknown, not Met).
isConditionNotMet :: TriggerCondition -> Boolean
isConditionNotMet cond = not (cond == ConditionMet || cond == ConditionUnknown)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // snapshot operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a snapshot with generated UUID5
createSnapshot :: Number -> FrameSnapshot -> Array AnimationSnapshot -> Array SpringSnapshot -> EffectSnapshot
createSnapshot timestamp frame animations springs =
  let
    -- Generate deterministic UUID from snapshot content
    contentStr = show timestamp <> show frame.frameNumber
    uuid = UUID5.uuid5 UUID5.nsFrameState contentStr
  in
    EffectSnapshot
      { id: uuid
      , timestamp
      , frame
      , animations
      , springs
      , render: Nothing
      }

-- | Restore state from snapshot (returns the snapshot for chaining)
restoreSnapshot :: EffectSnapshot -> EffectSnapshot
restoreSnapshot = identity
  where identity x = x

-- | Diff two snapshots
diffSnapshots :: EffectSnapshot -> EffectSnapshot -> SnapshotDiff
diffSnapshots (EffectSnapshot a) (EffectSnapshot b) =
  { timestampDelta: b.timestamp - a.timestamp
  , framesDelta: b.frame.frameNumber - a.frame.frameNumber
  , animationsChanged: Array.length a.animations /= Array.length b.animations
  , springsChanged: Array.length a.springs /= Array.length b.springs
  }

-- | Snapshot difference
type SnapshotDiff =
  { timestampDelta :: Number
  , framesDelta :: Int
  , animationsChanged :: Boolean
  , springsChanged :: Boolean
  }

-- | Get snapshot UUID5
snapshotId :: EffectSnapshot -> UUID5.UUID5
snapshotId (EffectSnapshot s) = s.id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // event construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create effect started event
effectStarted :: UUID5.UUID5 -> Number -> EffectEvent
effectStarted effectId timestamp = EventLifecycle $ EffectStarted { effectId, timestamp }

-- | Create effect updated event
effectUpdated :: UUID5.UUID5 -> Number -> Number -> EffectEvent
effectUpdated effectId timestamp progress = EventLifecycle $ EffectUpdated { effectId, timestamp, progress }

-- | Create effect completed event
effectCompleted :: UUID5.UUID5 -> Number -> EffectEvent
effectCompleted effectId timestamp = EventLifecycle $ EffectCompleted { effectId, timestamp }

-- | Create effect cancelled event
effectCancelled :: UUID5.UUID5 -> Number -> String -> EffectEvent
effectCancelled effectId timestamp reason = EventLifecycle $ EffectCancelled { effectId, timestamp, reason }

-- | Create animation tick event
animationTick :: Int -> Number -> Number -> EffectEvent
animationTick handle progress deltaMs = EventAnimation $ AnimationTick { handle, progress, deltaMs }

-- | Create interaction event
interactionOccurred :: InteractionEvent -> EffectEvent
interactionOccurred = EventInteraction

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Trigger on hover over element
onHover :: Int -> EffectTrigger
onHover pickId = TriggerMouse (MouseHover pickId)

-- | Trigger on focus.
-- |
-- | Fires when an element gains keyboard focus. Works with both mouse clicks
-- | that set focus and keyboard navigation (Tab, Shift+Tab). The runtime's
-- | focus management system tracks the currently focused element and evaluates
-- | this trigger accordingly.
onFocus :: Int -> EffectTrigger
onFocus pickId = TriggerFocus (FocusGained pickId)

-- | Trigger on active/pressed state
onActive :: Int -> EffectTrigger
onActive pickId = TriggerMouse (MouseDown pickId)

-- | Trigger when element visible in viewport
onVisible :: Int -> EffectTrigger
onVisible pickId = TriggerViewport (ViewportVisible pickId)

-- | Trigger on scroll position
onScroll :: Number -> EffectTrigger
onScroll position = TriggerScroll (ScrollPosition position)

-- | Trigger after delay
afterDelay :: Number -> EffectTrigger
afterDelay ms = TriggerTime (AfterDelay ms)

-- | Trigger at animation progress
atProgress :: Number -> Number -> EffectTrigger
atProgress minP maxP = TriggerAnimation (AnimationProgress minP maxP)
