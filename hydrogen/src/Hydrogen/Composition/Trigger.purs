-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // composition // trigger
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Trigger System — Event-driven state transitions.
-- |
-- | Triggers define how layers respond to events:
-- | - User input (hover, click, focus, scroll)
-- | - Data changes (query result updated)
-- | - Time (animation start/end, duration elapsed)
-- | - System (viewport resize, theme change)
-- |
-- | ## Event Model
-- |
-- | Triggers are NOT frame-driven. The UI is stable until an event occurs:
-- | 1. Event fires (hover, click, data change)
-- | 2. Trigger conditions evaluated
-- | 3. Actions executed (property changes, animations)
-- | 4. New stable state cached
-- |
-- | This is efficient for billion-agent scale: stable states don't recalculate.

module Hydrogen.Composition.Trigger
  ( -- * Core Types
    Trigger(..)
  , TriggerEvent(..)
  , TriggerAction(..)
  , TriggerCondition(..)
  
  -- * Events
  , EventType(..)
  , eventType
  
  -- * Actions
  , PropertyChange(..)
  , AnimationTarget(..)
  
  -- * Conditions
  , Comparator(..)
  , evaluate
  , conditionAnd
  , conditionOr
  , isAlwaysTrue
  , isAlwaysFalse
  
  -- * Property Change Helpers
  , animateTo
  , animateFromTo
  
  -- * Constructors
  , onHover
  , onClick
  , onFocus
  , onScroll
  , onDataChange
  , onTimer
  , onViewportResize
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (&&)
  , (||)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , not
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // event types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Categories of events that can trigger actions.
data EventType
  = EventUser       -- User input (hover, click, focus)
  | EventData       -- Data/query changes
  | EventTime       -- Timer/animation events
  | EventSystem     -- System events (resize, theme)

derive instance eqEventType :: Eq EventType

instance showEventType :: Show EventType where
  show EventUser = "user"
  show EventData = "data"
  show EventTime = "time"
  show EventSystem = "system"

-- | Specific trigger events.
data TriggerEvent
  -- User Input
  = OnHoverStart
  | OnHoverEnd
  | OnClick
  | OnDoubleClick
  | OnRightClick
  | OnFocusIn
  | OnFocusOut
  | OnKeyDown String        -- Key code
  | OnKeyUp String
  | OnScroll
  | OnScrollStart
  | OnScrollEnd
  | OnDragStart
  | OnDragEnd
  | OnDrop
  | OnPinch
  | OnRotate
  -- Data
  | OnDataChange String     -- Query/data ref
  | OnDataLoad String
  | OnDataError String
  -- Time
  | OnAnimationStart
  | OnAnimationEnd
  | OnAnimationIteration
  | OnTimer Number          -- Delay in ms
  | OnInterval Number       -- Repeat interval
  -- System
  | OnViewportResize
  | OnOrientationChange
  | OnThemeChange
  | OnVisibilityChange
  | OnOnline
  | OnOffline

derive instance eqTriggerEvent :: Eq TriggerEvent

instance showTriggerEvent :: Show TriggerEvent where
  show OnHoverStart = "hover:start"
  show OnHoverEnd = "hover:end"
  show OnClick = "click"
  show OnDoubleClick = "dblclick"
  show OnRightClick = "rightclick"
  show OnFocusIn = "focus:in"
  show OnFocusOut = "focus:out"
  show (OnKeyDown k) = "keydown:" <> k
  show (OnKeyUp k) = "keyup:" <> k
  show OnScroll = "scroll"
  show OnScrollStart = "scroll:start"
  show OnScrollEnd = "scroll:end"
  show OnDragStart = "drag:start"
  show OnDragEnd = "drag:end"
  show OnDrop = "drop"
  show OnPinch = "pinch"
  show OnRotate = "rotate"
  show (OnDataChange r) = "data:change:" <> r
  show (OnDataLoad r) = "data:load:" <> r
  show (OnDataError r) = "data:error:" <> r
  show OnAnimationStart = "animation:start"
  show OnAnimationEnd = "animation:end"
  show OnAnimationIteration = "animation:iteration"
  show (OnTimer t) = "timer:" <> show t
  show (OnInterval t) = "interval:" <> show t
  show OnViewportResize = "viewport:resize"
  show OnOrientationChange = "orientation:change"
  show OnThemeChange = "theme:change"
  show OnVisibilityChange = "visibility:change"
  show OnOnline = "online"
  show OnOffline = "offline"

-- | Get event type category.
eventType :: TriggerEvent -> EventType
eventType OnHoverStart = EventUser
eventType OnHoverEnd = EventUser
eventType OnClick = EventUser
eventType OnDoubleClick = EventUser
eventType OnRightClick = EventUser
eventType OnFocusIn = EventUser
eventType OnFocusOut = EventUser
eventType (OnKeyDown _) = EventUser
eventType (OnKeyUp _) = EventUser
eventType OnScroll = EventUser
eventType OnScrollStart = EventUser
eventType OnScrollEnd = EventUser
eventType OnDragStart = EventUser
eventType OnDragEnd = EventUser
eventType OnDrop = EventUser
eventType OnPinch = EventUser
eventType OnRotate = EventUser
eventType (OnDataChange _) = EventData
eventType (OnDataLoad _) = EventData
eventType (OnDataError _) = EventData
eventType OnAnimationStart = EventTime
eventType OnAnimationEnd = EventTime
eventType OnAnimationIteration = EventTime
eventType (OnTimer _) = EventTime
eventType (OnInterval _) = EventTime
eventType OnViewportResize = EventSystem
eventType OnOrientationChange = EventSystem
eventType OnThemeChange = EventSystem
eventType OnVisibilityChange = EventSystem
eventType OnOnline = EventSystem
eventType OnOffline = EventSystem

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // conditions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Comparison operators for conditions.
data Comparator
  = CompEq
  | CompNeq
  | CompLt
  | CompLte
  | CompGt
  | CompGte
  | CompContains
  | CompStartsWith
  | CompEndsWith

derive instance eqComparator :: Eq Comparator

instance showComparator :: Show Comparator where
  show CompEq = "=="
  show CompNeq = "!="
  show CompLt = "<"
  show CompLte = "<="
  show CompGt = ">"
  show CompGte = ">="
  show CompContains = "contains"
  show CompStartsWith = "starts-with"
  show CompEndsWith = "ends-with"

-- | Conditions that must be met for trigger to fire.
data TriggerCondition
  = ConditionAlways                               -- No condition
  | ConditionProperty String Comparator String    -- Property comparison
  | ConditionData String Comparator String        -- Data value comparison
  | ConditionViewport String Comparator Number    -- Viewport condition
  | ConditionAnd TriggerCondition TriggerCondition
  | ConditionOr TriggerCondition TriggerCondition
  | ConditionNot TriggerCondition

derive instance eqTriggerCondition :: Eq TriggerCondition

instance showTriggerCondition :: Show TriggerCondition where
  show ConditionAlways = "always"
  show (ConditionProperty p c v) = "prop:" <> p <> show c <> v
  show (ConditionData d c v) = "data:" <> d <> show c <> v
  show (ConditionViewport p c v) = "viewport:" <> p <> show c <> show v
  show (ConditionAnd a b) = "(" <> show a <> " && " <> show b <> ")"
  show (ConditionOr a b) = "(" <> show a <> " || " <> show b <> ")"
  show (ConditionNot c) = "!" <> show c

-- | Evaluate a simple number condition (for demo).
evaluate :: Comparator -> Number -> Number -> Boolean
evaluate CompEq a b = a == b
evaluate CompNeq a b = not (a == b)
evaluate CompLt a b = a < b
evaluate CompLte a b = a <= b
evaluate CompGt a b = a > b
evaluate CompGte a b = a >= b
evaluate _ _ _ = false  -- String ops don't apply to numbers

-- | Combine two conditions with AND.
conditionAnd :: TriggerCondition -> TriggerCondition -> TriggerCondition
conditionAnd ConditionAlways b = b
conditionAnd a ConditionAlways = a
conditionAnd a b = ConditionAnd a b

-- | Combine two conditions with OR.
conditionOr :: TriggerCondition -> TriggerCondition -> TriggerCondition
conditionOr ConditionAlways _ = ConditionAlways
conditionOr _ ConditionAlways = ConditionAlways
conditionOr a b = ConditionOr a b

-- | Check if a condition is trivially true (always passes).
isAlwaysTrue :: TriggerCondition -> Boolean
isAlwaysTrue ConditionAlways = true
isAlwaysTrue (ConditionAnd a b) = isAlwaysTrue a && isAlwaysTrue b
isAlwaysTrue (ConditionOr a b) = isAlwaysTrue a || isAlwaysTrue b
isAlwaysTrue _ = false

-- | Check if a condition is trivially false (never passes).
isAlwaysFalse :: TriggerCondition -> Boolean
isAlwaysFalse (ConditionNot ConditionAlways) = true
isAlwaysFalse (ConditionAnd a b) = isAlwaysFalse a || isAlwaysFalse b
isAlwaysFalse (ConditionOr a b) = isAlwaysFalse a && isAlwaysFalse b
isAlwaysFalse _ = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // actions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Property to animate/change.
data AnimationTarget
  = TargetOpacity
  | TargetPositionX
  | TargetPositionY
  | TargetScale
  | TargetScaleX
  | TargetScaleY
  | TargetRotation
  | TargetBlur
  | TargetShadowOffset
  | TargetShadowBlur
  | TargetShadowOpacity
  | TargetCustom String

derive instance eqAnimationTarget :: Eq AnimationTarget

instance showAnimationTarget :: Show AnimationTarget where
  show TargetOpacity = "opacity"
  show TargetPositionX = "x"
  show TargetPositionY = "y"
  show TargetScale = "scale"
  show TargetScaleX = "scaleX"
  show TargetScaleY = "scaleY"
  show TargetRotation = "rotation"
  show TargetBlur = "blur"
  show TargetShadowOffset = "shadowOffset"
  show TargetShadowBlur = "shadowBlur"
  show TargetShadowOpacity = "shadowOpacity"
  show (TargetCustom name) = "custom:" <> name

-- | Property change specification.
type PropertyChange =
  { target :: AnimationTarget
  , from :: Maybe Number      -- Nothing = current value
  , to :: Number
  , duration :: Number        -- ms, 0 = instant
  , easing :: String          -- Easing function name
  , delay :: Number           -- ms
  }

-- | Create a property change that animates from current value to target.
animateTo :: AnimationTarget -> Number -> Number -> PropertyChange
animateTo target to duration =
  { target
  , from: Nothing
  , to
  , duration
  , easing: "ease-out"
  , delay: 0.0
  }

-- | Create a property change with explicit from and to values.
animateFromTo :: AnimationTarget -> Number -> Number -> Number -> PropertyChange
animateFromTo target from to duration =
  { target
  , from: Just from
  , to
  , duration
  , easing: "ease-out"
  , delay: 0.0
  }

-- | Actions that triggers can execute.
data TriggerAction
  = ActionAnimate PropertyChange
  | ActionSetProperty String String       -- Property name, value
  | ActionToggleClass String              -- CSS class name
  | ActionEmit String                     -- Emit event upward
  | ActionNavigate String                 -- URL/route
  | ActionExecute String                  -- Action ID (safe, sanitized)
  | ActionSequence (Array TriggerAction)  -- Run in sequence
  | ActionParallel (Array TriggerAction)  -- Run in parallel

derive instance eqTriggerAction :: Eq TriggerAction

instance showTriggerAction :: Show TriggerAction where
  show (ActionAnimate _) = "animate"
  show (ActionSetProperty p _) = "set:" <> p
  show (ActionToggleClass c) = "toggle:" <> c
  show (ActionEmit e) = "emit:" <> e
  show (ActionNavigate u) = "navigate:" <> u
  show (ActionExecute a) = "execute:" <> a
  show (ActionSequence _) = "sequence"
  show (ActionParallel _) = "parallel"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // trigger struct
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete trigger definition.
-- |
-- | A trigger listens for an event, checks conditions, and runs actions.
type Trigger =
  { event :: TriggerEvent
  , condition :: TriggerCondition
  , actions :: Array TriggerAction
  , enabled :: Boolean
  , once :: Boolean           -- Fire only once
  , debounce :: Number        -- Debounce in ms
  , throttle :: Number        -- Throttle in ms
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create hover trigger (fires on hover start, reverses on hover end).
onHover :: Array TriggerAction -> Trigger
onHover actions =
  { event: OnHoverStart
  , condition: ConditionAlways
  , actions
  , enabled: true
  , once: false
  , debounce: 0.0
  , throttle: 0.0
  }

-- | Create click trigger.
onClick :: Array TriggerAction -> Trigger
onClick actions =
  { event: OnClick
  , condition: ConditionAlways
  , actions
  , enabled: true
  , once: false
  , debounce: 0.0
  , throttle: 0.0
  }

-- | Create focus trigger.
onFocus :: Array TriggerAction -> Trigger
onFocus actions =
  { event: OnFocusIn
  , condition: ConditionAlways
  , actions
  , enabled: true
  , once: false
  , debounce: 0.0
  , throttle: 0.0
  }

-- | Create scroll trigger.
onScroll :: Array TriggerAction -> Trigger
onScroll actions =
  { event: OnScroll
  , condition: ConditionAlways
  , actions
  , enabled: true
  , once: false
  , debounce: 0.0
  , throttle: 16.0  -- ~60fps max
  }

-- | Create data change trigger.
onDataChange :: String -> Array TriggerAction -> Trigger
onDataChange dataRef actions =
  { event: OnDataChange dataRef
  , condition: ConditionAlways
  , actions
  , enabled: true
  , once: false
  , debounce: 0.0
  , throttle: 0.0
  }

-- | Create timer trigger.
onTimer :: Number -> Array TriggerAction -> Trigger
onTimer delay actions =
  { event: OnTimer delay
  , condition: ConditionAlways
  , actions
  , enabled: true
  , once: true
  , debounce: 0.0
  , throttle: 0.0
  }

-- | Create viewport resize trigger.
onViewportResize :: Array TriggerAction -> Trigger
onViewportResize actions =
  { event: OnViewportResize
  , condition: ConditionAlways
  , actions
  , enabled: true
  , once: false
  , debounce: 100.0  -- Debounce resize events
  , throttle: 0.0
  }
