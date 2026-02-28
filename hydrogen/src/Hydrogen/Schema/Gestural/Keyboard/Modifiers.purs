-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // gestural // keyboard // modifiers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Modifiers - modifier key state tracking.
-- |
-- | Models the state of modifier keys (Ctrl, Alt, Shift, Meta).
-- | Provides helpers for common modifier combinations.
-- |
-- | ## Dependencies
-- | - Prelude (Boolean, not, &&, ||)
-- |
-- | ## Dependents
-- | - Gestural.Keyboard.Event (events include modifier state)
-- | - Gestural.Keyboard.Shortcut (shortcuts match on modifiers)
-- | - Gestural.Keyboard.State (tracks current modifiers)

module Hydrogen.Schema.Gestural.Keyboard.Modifiers
  ( -- * Modifier State
    ModifierState
  , noModifiers
  , ctrlOnly
  , altOnly
  , shiftOnly
  , metaOnly
    -- * Modifier Queries
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
    -- * Platform Helpers
  , hasPlatformModifier
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // modifier // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of modifier keys
-- |
-- | Tracks which modifier keys are currently pressed.
-- | Based on KeyboardEvent modifier properties.
type ModifierState =
  { ctrl :: Boolean      -- ^ Control key (Ctrl on Win/Linux, Control on Mac)
  , alt :: Boolean       -- ^ Alt key (Alt on Win/Linux, Option on Mac)
  , shift :: Boolean     -- ^ Shift key
  , meta :: Boolean      -- ^ Meta key (Win key on Win, Command on Mac)
  , capsLock :: Boolean  -- ^ Caps Lock (toggled state)
  , numLock :: Boolean   -- ^ Num Lock (toggled state)
  }

-- | No modifiers pressed
noModifiers :: ModifierState
noModifiers =
  { ctrl: false
  , alt: false
  , shift: false
  , meta: false
  , capsLock: false
  , numLock: false
  }

-- | Only Ctrl pressed
ctrlOnly :: ModifierState
ctrlOnly = noModifiers { ctrl = true }

-- | Only Alt pressed
altOnly :: ModifierState
altOnly = noModifiers { alt = true }

-- | Only Shift pressed
shiftOnly :: ModifierState
shiftOnly = noModifiers { shift = true }

-- | Only Meta pressed
metaOnly :: ModifierState
metaOnly = noModifiers { meta = true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // modifier // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if Ctrl (or Cmd on Mac) is pressed
-- |
-- | Platform-agnostic check for the primary modifier key.
-- | On Mac, Command (meta) is the primary; on Win/Linux, Ctrl.
hasCtrlOrCmd :: ModifierState -> Boolean
hasCtrlOrCmd mods = mods.ctrl || mods.meta

-- | Check if any modifier is pressed (excluding lock keys)
hasAnyModifier :: ModifierState -> Boolean
hasAnyModifier mods = mods.ctrl || mods.alt || mods.shift || mods.meta

-- | Check if only Shift is pressed
onlyShift :: ModifierState -> Boolean
onlyShift mods = mods.shift && not mods.ctrl && not mods.alt && not mods.meta

-- | Check if only Ctrl is pressed
onlyCtrl :: ModifierState -> Boolean
onlyCtrl mods = mods.ctrl && not mods.shift && not mods.alt && not mods.meta

-- | Check if only Alt is pressed
onlyAlt :: ModifierState -> Boolean
onlyAlt mods = mods.alt && not mods.ctrl && not mods.shift && not mods.meta

-- | Check if only Meta is pressed
onlyMeta :: ModifierState -> Boolean
onlyMeta mods = mods.meta && not mods.ctrl && not mods.shift && not mods.alt

-- | Check if Ctrl+Shift is pressed (no other modifiers)
ctrlShift :: ModifierState -> Boolean
ctrlShift mods = mods.ctrl && mods.shift && not mods.alt && not mods.meta

-- | Check if Alt+Shift is pressed (no other modifiers)
altShift :: ModifierState -> Boolean
altShift mods = mods.alt && mods.shift && not mods.ctrl && not mods.meta

-- | Check if Ctrl+Alt is pressed (no other modifiers)
ctrlAlt :: ModifierState -> Boolean
ctrlAlt mods = mods.ctrl && mods.alt && not mods.shift && not mods.meta

-- | Check if Ctrl+Alt+Shift is pressed (no Meta)
ctrlAltShift :: ModifierState -> Boolean
ctrlAltShift mods = mods.ctrl && mods.alt && mods.shift && not mods.meta

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // platform // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check for platform modifier (Ctrl on Win/Linux, Meta on Mac)
-- |
-- | This is the primary action modifier on each platform.
-- | For cross-platform shortcuts, check both ctrl and meta.
hasPlatformModifier :: ModifierState -> Boolean
hasPlatformModifier = hasCtrlOrCmd
