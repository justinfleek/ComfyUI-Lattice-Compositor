-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // gestural // keyboard // event
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Event - keyboard event types and constructors.
-- |
-- | Models keyboard events per W3C KeyboardEvent interface.
-- | Captures key codes, logical values, modifiers, and timing.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Data.String.CodeUnits (length)
-- | - Gestural.Keyboard.Keys (KeyCode)
-- | - Gestural.Keyboard.Modifiers (ModifierState, hasCtrlOrCmd)
-- |
-- | ## Dependents
-- | - Gestural.Keyboard.Shortcut (matching events to shortcuts)
-- | - Gestural.Keyboard.State (tracking keyboard state)
-- | - Component.* (handling keyboard input)

module Hydrogen.Schema.Gestural.Keyboard.Event
  ( -- * Key Event Type
    KeyEventType(KeyDown, KeyUp, KeyPress)
  , isKeyDown
  , isKeyUp
  , isKeyPress
    -- * Key Event
  , KeyEvent
  , keyEvent
  , keyEventFull
  , eventCode
  , eventKey
  , eventModifiers
  , isRepeat
  , eventTimestamp
    -- * Event Classification
  , isPrintableKey
  , isModifierKey
  , isFunctionKey
  , isNavigationKey
  ) where

import Prelude

import Data.String.CodeUnits as CU
import Hydrogen.Schema.Gestural.Keyboard.Keys (KeyCode(KeyCode))
import Hydrogen.Schema.Gestural.Keyboard.Modifiers (ModifierState, hasCtrlOrCmd, noModifiers)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // key // event type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of keyboard event
data KeyEventType
  = KeyDown     -- ^ Key was pressed down
  | KeyUp       -- ^ Key was released
  | KeyPress    -- ^ Character was typed (deprecated but still used)

derive instance eqKeyEventType :: Eq KeyEventType
derive instance ordKeyEventType :: Ord KeyEventType

instance showKeyEventType :: Show KeyEventType where
  show KeyDown = "keydown"
  show KeyUp = "keyup"
  show KeyPress = "keypress"

-- | Is this a keydown event?
isKeyDown :: KeyEventType -> Boolean
isKeyDown KeyDown = true
isKeyDown _ = false

-- | Is this a keyup event?
isKeyUp :: KeyEventType -> Boolean
isKeyUp KeyUp = true
isKeyUp _ = false

-- | Is this a keypress event?
isKeyPress :: KeyEventType -> Boolean
isKeyPress KeyPress = true
isKeyPress _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // key // event
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete keyboard event data
-- |
-- | Based on W3C KeyboardEvent interface.
type KeyEvent =
  { eventType :: KeyEventType   -- ^ Type of key event
  , code :: KeyCode             -- ^ Physical key code (e.g., "KeyA")
  , key :: String               -- ^ Logical key value (e.g., "a", "A", "Enter")
  , modifiers :: ModifierState  -- ^ State of modifier keys
  , repeat :: Boolean           -- ^ Is this a repeat event from holding key
  , timestamp :: Number         -- ^ Event timestamp (ms)
  }

-- | Create key event with defaults
-- |
-- | Creates event with no modifiers, no repeat, timestamp 0.
keyEvent :: KeyEventType -> KeyCode -> String -> KeyEvent
keyEvent eventType code key =
  { eventType
  , code
  , key
  , modifiers: noModifiers
  , repeat: false
  , timestamp: 0.0
  }

-- | Create key event with all fields
keyEventFull
  :: KeyEventType
  -> KeyCode
  -> String
  -> ModifierState
  -> Boolean
  -> Number
  -> KeyEvent
keyEventFull eventType code key modifiers repeat timestamp =
  { eventType
  , code
  , key
  , modifiers
  , repeat
  , timestamp
  }

-- | Get event key code
eventCode :: KeyEvent -> KeyCode
eventCode ke = ke.code

-- | Get event key value
eventKey :: KeyEvent -> String
eventKey ke = ke.key

-- | Get event modifiers
eventModifiers :: KeyEvent -> ModifierState
eventModifiers ke = ke.modifiers

-- | Is this a repeat event?
isRepeat :: KeyEvent -> Boolean
isRepeat ke = ke.repeat

-- | Get event timestamp
eventTimestamp :: KeyEvent -> Number
eventTimestamp ke = ke.timestamp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // event // classification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if event is for a printable character
-- |
-- | Printable if key is single character and no Ctrl/Cmd modifier.
isPrintableKey :: KeyEvent -> Boolean
isPrintableKey ke = CU.length ke.key == 1 && not (hasCtrlOrCmd ke.modifiers)

-- | Check if event is for a modifier key
-- |
-- | Modifier keys: Control, Shift, Alt, Meta, CapsLock, NumLock
isModifierKey :: KeyEvent -> Boolean
isModifierKey ke = case ke.code of
  KeyCode "ControlLeft" -> true
  KeyCode "ControlRight" -> true
  KeyCode "ShiftLeft" -> true
  KeyCode "ShiftRight" -> true
  KeyCode "AltLeft" -> true
  KeyCode "AltRight" -> true
  KeyCode "MetaLeft" -> true
  KeyCode "MetaRight" -> true
  KeyCode "CapsLock" -> true
  KeyCode "NumLock" -> true
  _ -> false

-- | Check if event is for a function key (F1-F12)
isFunctionKey :: KeyEvent -> Boolean
isFunctionKey ke = case ke.code of
  KeyCode "F1" -> true
  KeyCode "F2" -> true
  KeyCode "F3" -> true
  KeyCode "F4" -> true
  KeyCode "F5" -> true
  KeyCode "F6" -> true
  KeyCode "F7" -> true
  KeyCode "F8" -> true
  KeyCode "F9" -> true
  KeyCode "F10" -> true
  KeyCode "F11" -> true
  KeyCode "F12" -> true
  _ -> false

-- | Check if event is for a navigation key
-- |
-- | Navigation keys: arrows, Home, End, PageUp, PageDown
isNavigationKey :: KeyEvent -> Boolean
isNavigationKey ke = case ke.code of
  KeyCode "ArrowUp" -> true
  KeyCode "ArrowDown" -> true
  KeyCode "ArrowLeft" -> true
  KeyCode "ArrowRight" -> true
  KeyCode "Home" -> true
  KeyCode "End" -> true
  KeyCode "PageUp" -> true
  KeyCode "PageDown" -> true
  _ -> false
