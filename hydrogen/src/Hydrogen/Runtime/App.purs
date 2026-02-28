-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // runtime // app
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Application Shell
-- |
-- | The pure core of a Hydrogen application. Defines the App type and
-- | runtime loop logic as pure functions. The actual Effect execution
-- | happens at the FFI boundary in the DOM runtime.
-- |
-- | ## Architecture
-- |
-- | ```
-- | State × Msg → State × [Cmd]
-- | view :: State → Element Msg
-- | ```
-- |
-- | The App shell:
-- | 1. Holds application definition (init, update, view, subscriptions)
-- | 2. Manages trigger state evaluation
-- | 3. Produces render instructions (Element → DrawCommand)
-- | 4. Wires animation ticks through the update cycle
-- |
-- | ## Dependencies
-- | - Hydrogen.Runtime.Cmd (Cmd, Transition)
-- | - Hydrogen.Runtime.Animate (animation state)
-- | - Hydrogen.Schema.Gestural.Trigger (TriggerState, TriggerDef)

module Hydrogen.Runtime.App
  ( -- * App Definition
    App
  , Sub(OnAnimationFrame, OnKeyDown, OnKeyUp, OnMouseMove, OnResize, OnVisibilityChange, OnInterval)
  , MousePos
  , Dimensions
  , app
  
  -- * App Configuration
  , AppConfig
  , defaultConfig
  
  -- * Runtime State
  , RuntimeState
  , initialRuntime
  
  -- * Event Loop (Pure)
  , DomEvent(MouseMoved, KeyPressed, KeyReleased, WindowResized, VisibilityChanged)
  , processMessage
  , processTick
  , processEvent
  
  -- * Trigger Integration
  , evaluateTriggers
  , dispatchEffects
  
  -- * Condition Context
  , ConditionContext
  , buildConditionContext
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Functor
  , Unit
  , map
  , notEq
  , unit
  , ($)
  , (+)
  , (<<<)
  )

import Data.Array (concatMap, filter, snoc) as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Runtime.Cmd
  ( Cmd(None, Batch, Delay)
  , Transition
  )

import Hydrogen.Schema.Gestural.Trigger
  ( TriggerState
  , TriggerEffect
  , TriggerDef
  , initialTriggerState
  , pendingEffects
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // app definition
-- ═════════════════════════════════════════════════════════════════════════════

-- | A Hydrogen Application
-- |
-- | Parameterized by:
-- | - `state` — the application's model/state type
-- | - `msg` — the message type for state transitions
-- | - `element` — the view output type (kept polymorphic for target flexibility)
-- |
-- | The `view` function is polymorphic in `element` to support multiple render
-- | targets: DOM Elements, DrawCommands, static HTML, etc.
type App state msg element =
  { init :: Transition state msg
    -- ^ Initial state and startup commands
  , update :: msg -> state -> Transition state msg
    -- ^ State transition function
  , view :: state -> element
    -- ^ Pure view function (state → element)
  , subscriptions :: state -> Array (Sub msg)
    -- ^ Active subscriptions based on state
  , triggers :: Array TriggerDef
    -- ^ Trigger definitions for interactive effects
  }

-- | Subscription type — describes ongoing event sources
-- |
-- | Subscriptions are declarative: "while this state holds, listen for X"
data Sub msg
  = OnAnimationFrame (Number -> msg)
    -- ^ Request animation frames
  | OnKeyDown (String -> msg)
    -- ^ Keyboard events
  | OnKeyUp (String -> msg)
    -- ^ Keyboard events
  | OnMouseMove (MousePos -> msg)
    -- ^ Mouse position updates
  | OnResize (Dimensions -> msg)
    -- ^ Window resize events
  | OnVisibilityChange (Boolean -> msg)
    -- ^ Page visibility changes
  | OnInterval Number msg
    -- ^ Timer at interval (ms)

-- | Mouse position
type MousePos = { x :: Number, y :: Number }

-- | Window/element dimensions
type Dimensions = { width :: Number, height :: Number }

-- | Construct an App with sensible defaults for optional fields
app
  :: forall state msg element
   . { init :: Transition state msg
     , update :: msg -> state -> Transition state msg
     , view :: state -> element
     }
  -> App state msg element
app cfg =
  { init: cfg.init
  , update: cfg.update
  , view: cfg.view
  , subscriptions: \_ -> []
  , triggers: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // app configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Runtime configuration options
-- |
-- | These settings control runtime behavior, not application logic.
-- | Application logic belongs in the App type.
type AppConfig =
  { enableTriggers :: Boolean
    -- ^ Whether to evaluate trigger conditions each frame
  , enableAnimationBatching :: Boolean
    -- ^ Batch multiple animation updates into single frame
  , maxFrameTime :: Number
    -- ^ Maximum time budget per frame (ms) before yielding
  , debugMode :: Boolean
    -- ^ Enable debug logging and performance metrics
  }

-- | Sensible default configuration
defaultConfig :: AppConfig
defaultConfig =
  { enableTriggers: true
  , enableAnimationBatching: true
  , maxFrameTime: 16.0  -- Target 60fps
  , debugMode: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // runtime state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Runtime state maintained by the Hydrogen runtime
-- |
-- | This is internal to the runtime — application code doesn't touch this.
-- | It tracks timing, triggers, and frame scheduling.
type RuntimeState state =
  { appState :: state
    -- ^ Current application state
  , triggerState :: TriggerState
    -- ^ State for trigger evaluation
  , lastFrameTime :: Number
    -- ^ Timestamp of last frame (ms)
  , frameCount :: Int
    -- ^ Total frames rendered
  , mousePos :: MousePos
    -- ^ Current mouse position
  , windowSize :: Dimensions
    -- ^ Current window dimensions
  , activeKeys :: Array String
    -- ^ Currently pressed keys
  , pendingCmds :: Array (Cmd Unit)
    -- ^ Commands waiting to execute (type-erased for batching)
  }

-- | Create initial runtime state from app's init
initialRuntime :: forall state msg. Transition state msg -> RuntimeState state
initialRuntime initTransition =
  { appState: initTransition.state
  , triggerState: initialTriggerState
  , lastFrameTime: 0.0
  , frameCount: 0
  , mousePos: { x: 0.0, y: 0.0 }
  , windowSize: { width: 0.0, height: 0.0 }
  , activeKeys: []
  , pendingCmds: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // event loop
-- ═════════════════════════════════════════════════════════════════════════════

-- | Process a message through the application
-- |
-- | Pure function: takes current runtime state, produces new state + commands.
-- | This is the core of the Hydrogen event loop.
processMessage
  :: forall state msg element
   . App state msg element
  -> msg
  -> RuntimeState state
  -> { runtime :: RuntimeState state, cmd :: Cmd msg }
processMessage application msg runtime =
  let
    trans = application.update msg runtime.appState
  in
    { runtime: runtime { appState = trans.state }
    , cmd: trans.cmd
    }

-- | Process an animation frame tick
-- |
-- | Updates timing state and evaluates triggers based on new timestamp.
-- | Returns any messages generated by trigger conditions being met.
processTick
  :: forall state msg element
   . AppConfig
  -> App state msg element
  -> Number  -- ^ Current timestamp (ms)
  -> RuntimeState state
  -> { runtime :: RuntimeState state, effects :: Array TriggerEffect }
processTick config application timestamp runtime =
  let
    newRuntime = runtime
      { lastFrameTime = timestamp
      , frameCount = runtime.frameCount + 1
      }
    effects = if config.enableTriggers
      then evaluateTriggers application.triggers runtime
      else []
  in
    { runtime: newRuntime
    , effects: effects
    }

-- | Process a DOM event
-- |
-- | Updates runtime state based on event type (mouse move, key press, etc.)
data DomEvent
  = MouseMoved MousePos
  | KeyPressed String
  | KeyReleased String
  | WindowResized Dimensions
  | VisibilityChanged Boolean

processEvent
  :: forall state
   . DomEvent
  -> RuntimeState state
  -> RuntimeState state
processEvent event runtime = case event of
  MouseMoved pos ->
    runtime { mousePos = pos }
  KeyPressed key ->
    runtime { activeKeys = Array.snoc runtime.activeKeys key }
  KeyReleased key ->
    runtime { activeKeys = Array.filter (\k -> notEq k key) runtime.activeKeys }
  WindowResized dims ->
    runtime { windowSize = dims }
  VisibilityChanged _ ->
    runtime  -- Could track visibility if needed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // trigger integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate all triggers against current runtime state
-- |
-- | Checks each trigger's conditions against current mouse position,
-- | active keys, timestamps, etc. Returns effects for triggers whose
-- | conditions are met.
-- |
-- | Note: This is a simplified implementation. Full condition evaluation
-- | (hover duration tracking, proximity calculations, etc.) requires
-- | additional runtime state and will be built in Hydrogen.Runtime.Trigger.
evaluateTriggers
  :: forall state
   . Array TriggerDef
  -> RuntimeState state
  -> Array TriggerEffect
evaluateTriggers _triggers runtime =
  -- Get effects from triggers that have all conditions met
  -- The actual condition checking is done by the DOM runtime which
  -- updates triggerState via checkConditions when events occur
  pendingEffects runtime.triggerState

-- | Dispatch effects generated by triggers
-- |
-- | Converts TriggerEffects to Cmds that the runtime can execute.
-- | This is the bridge from Schema types to Runtime commands.
dispatchEffects
  :: forall msg
   . (TriggerEffect -> Maybe msg)  -- ^ Effect handler provided by app
  -> Array TriggerEffect
  -> Cmd msg
dispatchEffects handler effects =
  let
    msgs = Array.concatMap (maybeToArray <<< handler) effects
  in
    case msgs of
      [] -> None
      _  -> Batch (map msgToCmd msgs)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Condition context built from runtime state
-- |
-- | This is passed to checkConditions for trigger evaluation.
type ConditionContext =
  { mousePos :: MousePos
  , activeKeys :: Array String
  , timestamp :: Number
  , scrollPosition :: Number
  , idleTime :: Number
  }

-- | Build condition context from runtime state
buildConditionContext :: forall state. RuntimeState state -> ConditionContext
buildConditionContext runtime =
  { mousePos: runtime.mousePos
  , activeKeys: runtime.activeKeys
  , timestamp: runtime.lastFrameTime
  , scrollPosition: 0.0  -- Would be tracked by DOM runtime
  , idleTime: 0.0        -- Would be tracked by DOM runtime
  }

-- | Convert Maybe to Array (for concatMap)
maybeToArray :: forall a. Maybe a -> Array a
maybeToArray Nothing = []
maybeToArray (Just a) = [a]

-- | Wrap a message as a zero-delay command
-- |
-- | Dispatches the message in the next microtask.
-- | Uses Delay 0.0 to schedule without blocking.
msgToCmd :: forall msg. msg -> Cmd msg
msgToCmd m = Delay 0.0 m
