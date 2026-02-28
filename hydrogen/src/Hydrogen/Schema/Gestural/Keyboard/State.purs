-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // gestural // keyboard // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | State - keyboard state tracking.
-- |
-- | Tracks the current state of keyboard input including
-- | modifier keys, recent events, and typing status.
-- |
-- | ## Dependencies
-- | - Prelude (Maybe, Boolean)
-- | - Data.Maybe (Maybe(Just, Nothing))
-- | - Gestural.Keyboard.Modifiers (ModifierState, noModifiers)
-- | - Gestural.Keyboard.Event (KeyEvent, isPrintableKey)
-- |
-- | ## Dependents
-- | - Component.* (keyboard-enabled components)
-- | - Interaction.Focus (keyboard navigation state)

module Hydrogen.Schema.Gestural.Keyboard.State
  ( -- * Keyboard State
    KeyboardState
  , initialKeyboardState
  , stateModifiers
  , stateLastEvent
  , stateIsTyping
  , stateTimestamp
    -- * State Updates
  , updateKeyboardState
  , clearKeyboardState
  , resetModifiers
    -- * State Queries
  , hasActiveModifiers
  , timeSinceLastEvent
  , isIdle
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing), isJust)
import Hydrogen.Schema.Gestural.Keyboard.Modifiers
  ( ModifierState
  , noModifiers
  , hasAnyModifier
  )
import Hydrogen.Schema.Gestural.Keyboard.Event (KeyEvent, isPrintableKey)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // keyboard // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete keyboard state
-- |
-- | Tracks modifier state and recent key events for components.
type KeyboardState =
  { modifiers :: ModifierState    -- ^ Current modifier key states
  , lastEvent :: Maybe KeyEvent   -- ^ Most recent key event
  , isTyping :: Boolean           -- ^ User is actively typing (for debounce)
  , timestamp :: Number           -- ^ Last update timestamp (ms)
  }

-- | Initial keyboard state
initialKeyboardState :: KeyboardState
initialKeyboardState =
  { modifiers: noModifiers
  , lastEvent: Nothing
  , isTyping: false
  , timestamp: 0.0
  }

-- | Get current modifier state
stateModifiers :: KeyboardState -> ModifierState
stateModifiers ks = ks.modifiers

-- | Get last key event
stateLastEvent :: KeyboardState -> Maybe KeyEvent
stateLastEvent ks = ks.lastEvent

-- | Is user currently typing?
stateIsTyping :: KeyboardState -> Boolean
stateIsTyping ks = ks.isTyping

-- | Get last update timestamp
stateTimestamp :: KeyboardState -> Number
stateTimestamp ks = ks.timestamp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // state // updates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update keyboard state with new event
updateKeyboardState :: KeyEvent -> KeyboardState -> KeyboardState
updateKeyboardState ke ks =
  ks { modifiers = ke.modifiers
     , lastEvent = Just ke
     , isTyping = isPrintableKey ke
     , timestamp = ke.timestamp
     }

-- | Clear keyboard state (e.g., on blur)
clearKeyboardState :: KeyboardState -> KeyboardState
clearKeyboardState ks =
  ks { modifiers = noModifiers
     , lastEvent = Nothing
     , isTyping = false
     }

-- | Reset only modifiers (keep other state)
resetModifiers :: KeyboardState -> KeyboardState
resetModifiers ks =
  ks { modifiers = noModifiers }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // state // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if any modifiers are currently active
hasActiveModifiers :: KeyboardState -> Boolean
hasActiveModifiers ks = hasAnyModifier ks.modifiers

-- | Calculate time since last event
-- |
-- | Returns difference between current time and last event timestamp.
-- | Returns 0 if no events have occurred.
timeSinceLastEvent :: Number -> KeyboardState -> Number
timeSinceLastEvent currentTime ks =
  if isJust ks.lastEvent
    then currentTime - ks.timestamp
    else 0.0

-- | Check if keyboard is idle (no recent activity)
-- |
-- | Idle if no events or last event was more than threshold ms ago.
isIdle :: Number -> Number -> KeyboardState -> Boolean
isIdle currentTime threshold ks =
  case ks.lastEvent of
    Nothing -> true
    Just _ -> timeSinceLastEvent currentTime ks > threshold
