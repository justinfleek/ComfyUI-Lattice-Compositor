-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // gestural // keyboard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keyboard - keyboard input, modifiers, shortcuts, and navigation.
-- |
-- | Re-exports all keyboard-related types and functions from sub-modules.
-- | Provides the foundation for accessible keyboard navigation and
-- | terminal-style interactions (vim/emacs keybindings).
-- |
-- | ## Sub-modules
-- | - Keys: Key code type and named constants
-- | - Modifiers: Modifier key state tracking
-- | - Event: Keyboard event types
-- | - Shortcut: Keyboard shortcut definitions
-- | - Navigation: Directional navigation types
-- | - State: Keyboard state tracking
-- |
-- | ## Dependents
-- | - Component.* (keyboard-enabled components)
-- | - Interaction.Focus (keyboard navigation)
-- | - A11y.* (accessibility shortcuts)

module Hydrogen.Schema.Gestural.Keyboard
  ( -- * Re-exports from Keys
    module Hydrogen.Schema.Gestural.Keyboard.Keys
    -- * Re-exports from Modifiers
  , module Hydrogen.Schema.Gestural.Keyboard.Modifiers
    -- * Re-exports from Event
  , module Hydrogen.Schema.Gestural.Keyboard.Event
    -- * Re-exports from Shortcut
  , module Hydrogen.Schema.Gestural.Keyboard.Shortcut
    -- * Re-exports from Navigation
  , module Hydrogen.Schema.Gestural.Keyboard.Navigation
    -- * Re-exports from State
  , module Hydrogen.Schema.Gestural.Keyboard.State
  ) where

import Hydrogen.Schema.Gestural.Keyboard.Keys
  ( KeyCode(KeyCode)
  , keyCode
  , unwrapKeyCode
  , keyEnter
  , keyEscape
  , keyBackspace
  , keyTab
  , keySpace
  , keyDelete
  , keyHome
  , keyEnd
  , keyPageUp
  , keyPageDown
  , keyInsert
  , keyArrowUp
  , keyArrowDown
  , keyArrowLeft
  , keyArrowRight
  , keyF1, keyF2, keyF3, keyF4, keyF5, keyF6
  , keyF7, keyF8, keyF9, keyF10, keyF11, keyF12
  , keyA, keyB, keyC, keyD, keyE, keyF, keyG, keyH, keyI
  , keyJ, keyK, keyL, keyM, keyN, keyO, keyP, keyQ, keyR
  , keyS, keyT, keyU, keyV, keyW, keyX, keyY, keyZ
  , key0, key1, key2, key3, key4, key5, key6, key7, key8, key9
  , keyBracketLeft
  , keyBracketRight
  , keySemicolon
  , keyQuote
  , keyBackquote
  , keySlash
  , keyBackslash
  , keyComma
  , keyPeriod
  , keyMinus
  , keyEqual
  )

import Hydrogen.Schema.Gestural.Keyboard.Modifiers
  ( ModifierState
  , noModifiers
  , ctrlOnly
  , altOnly
  , shiftOnly
  , metaOnly
  , hasCtrlOrCmd
  , hasAnyModifier
  , onlyShift
  , onlyCtrl
  , onlyAlt
  , onlyMeta
  , ctrlShift
  , altShift
  , ctrlAlt
  , ctrlAltShift
  , hasPlatformModifier
  )

import Hydrogen.Schema.Gestural.Keyboard.Event
  ( KeyEventType(KeyDown, KeyUp, KeyPress)
  , isKeyDown
  , isKeyUp
  , isKeyPress
  , KeyEvent
  , keyEvent
  , keyEventFull
  , eventCode
  , eventKey
  , eventModifiers
  , isRepeat
  , eventTimestamp
  , isPrintableKey
  , isModifierKey
  , isFunctionKey
  , isNavigationKey
  )

import Hydrogen.Schema.Gestural.Keyboard.Shortcut
  ( Shortcut
  , shortcut
  , simpleShortcut
  , ctrlShortcut
  , ctrlShiftShortcut
  , altShortcut
  , altShiftShortcut
  , metaShortcut
  , metaShiftShortcut
  , matchesShortcut
  , matchesShortcutLoose
  , shortcutCopy
  , shortcutCut
  , shortcutPaste
  , shortcutUndo
  , shortcutRedo
  , shortcutSelectAll
  , shortcutSave
  , shortcutFind
  , shortcutClose
  , shortcutNew
  , shortcutOpen
  , shortcutRedoY
  )

import Hydrogen.Schema.Gestural.Keyboard.Navigation
  ( ArrowDirection(ArrowUp, ArrowDown, ArrowLeft, ArrowRight)
  , isHorizontalArrow
  , isVerticalArrow
  , arrowFromCode
  , arrowFromEvent
  , oppositeArrow
  , TabDirection(TabForward, TabBackward)
  , tabDirectionFromEvent
  , oppositeTab
  , VimMovement(VimUp, VimDown, VimLeft, VimRight)
  , vimFromCode
  , vimFromEvent
  , vimToArrow
  , FocusAction(FocusNext, FocusPrev, FocusFirst, FocusLast, FocusParent)
  , focusActionFromEvent
  )

import Hydrogen.Schema.Gestural.Keyboard.State
  ( KeyboardState
  , initialKeyboardState
  , stateModifiers
  , stateLastEvent
  , stateIsTyping
  , stateTimestamp
  , updateKeyboardState
  , clearKeyboardState
  , resetModifiers
  , hasActiveModifiers
  , timeSinceLastEvent
  , isIdle
  )
