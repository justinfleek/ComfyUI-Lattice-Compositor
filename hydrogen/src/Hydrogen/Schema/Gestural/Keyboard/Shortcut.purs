-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // gestural // keyboard // shortcut
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shortcut - keyboard shortcut definitions and matching.
-- |
-- | Models keyboard shortcuts (key combinations) and matches
-- | events against shortcut definitions. Supports both web-style
-- | shortcuts (Ctrl+Key) and terminal-style sequences.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, &&, ==)
-- | - Gestural.Keyboard.Keys (KeyCode)
-- | - Gestural.Keyboard.Event (KeyEvent)
-- |
-- | ## Dependents
-- | - Component.* (shortcut handling)
-- | - A11y.KeyboardShortcuts (accessibility)

module Hydrogen.Schema.Gestural.Keyboard.Shortcut
  ( -- * Shortcut Type
    Shortcut
  , shortcut
    -- * Common Shortcut Constructors
  , simpleShortcut
  , ctrlShortcut
  , ctrlShiftShortcut
  , altShortcut
  , altShiftShortcut
  , metaShortcut
  , metaShiftShortcut
    -- * Shortcut Matching
  , matchesShortcut
  , matchesShortcutLoose
    -- * Common Shortcuts
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
  ) where

import Prelude

import Hydrogen.Schema.Gestural.Keyboard.Keys
  ( KeyCode
  , keyA
  , keyC
  , keyF
  , keyN
  , keyO
  , keyS
  , keyV
  , keyW
  , keyX
  , keyY
  , keyZ
  )
import Hydrogen.Schema.Gestural.Keyboard.Event (KeyEvent)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // shortcut // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyboard shortcut definition
-- |
-- | Represents a key combination that triggers an action.
-- | Modifiers are matched exactly by default.
type Shortcut =
  { code :: KeyCode      -- ^ Required key code
  , ctrl :: Boolean      -- ^ Requires Ctrl/Cmd
  , alt :: Boolean       -- ^ Requires Alt/Option
  , shift :: Boolean     -- ^ Requires Shift
  , meta :: Boolean      -- ^ Requires Meta (explicit, separate from ctrl)
  }

-- | Create shortcut with explicit modifiers
shortcut :: KeyCode -> Boolean -> Boolean -> Boolean -> Boolean -> Shortcut
shortcut code ctrl alt shift meta = { code, ctrl, alt, shift, meta }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // shortcut // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create shortcut with just a key (no modifiers)
simpleShortcut :: KeyCode -> Shortcut
simpleShortcut code =
  { code
  , ctrl: false
  , alt: false
  , shift: false
  , meta: false
  }

-- | Create Ctrl+Key shortcut (Cmd+Key on Mac)
ctrlShortcut :: KeyCode -> Shortcut
ctrlShortcut code =
  { code
  , ctrl: true
  , alt: false
  , shift: false
  , meta: false
  }

-- | Create Ctrl+Shift+Key shortcut
ctrlShiftShortcut :: KeyCode -> Shortcut
ctrlShiftShortcut code =
  { code
  , ctrl: true
  , alt: false
  , shift: true
  , meta: false
  }

-- | Create Alt+Key shortcut
altShortcut :: KeyCode -> Shortcut
altShortcut code =
  { code
  , ctrl: false
  , alt: true
  , shift: false
  , meta: false
  }

-- | Create Alt+Shift+Key shortcut
altShiftShortcut :: KeyCode -> Shortcut
altShiftShortcut code =
  { code
  , ctrl: false
  , alt: true
  , shift: true
  , meta: false
  }

-- | Create Meta+Key shortcut (Cmd on Mac, Win on Windows)
metaShortcut :: KeyCode -> Shortcut
metaShortcut code =
  { code
  , ctrl: false
  , alt: false
  , shift: false
  , meta: true
  }

-- | Create Meta+Shift+Key shortcut
metaShiftShortcut :: KeyCode -> Shortcut
metaShiftShortcut code =
  { code
  , ctrl: false
  , alt: false
  , shift: true
  , meta: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // shortcut // matching
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if key event matches shortcut exactly
-- |
-- | All modifiers must match exactly.
matchesShortcut :: Shortcut -> KeyEvent -> Boolean
matchesShortcut sc ke =
  ke.code == sc.code
  && ke.modifiers.ctrl == sc.ctrl
  && ke.modifiers.alt == sc.alt
  && ke.modifiers.shift == sc.shift
  && ke.modifiers.meta == sc.meta

-- | Check if key event matches shortcut loosely
-- |
-- | Ctrl and Meta are treated as interchangeable (cross-platform).
-- | Shift must match exactly if required.
matchesShortcutLoose :: Shortcut -> KeyEvent -> Boolean
matchesShortcutLoose sc ke =
  ke.code == sc.code
  && ke.modifiers.alt == sc.alt
  && ke.modifiers.shift == sc.shift
  && (if sc.ctrl || sc.meta
      then ke.modifiers.ctrl || ke.modifiers.meta
      else not ke.modifiers.ctrl && not ke.modifiers.meta)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // common // shortcuts
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ctrl+C / Cmd+C (Copy)
shortcutCopy :: Shortcut
shortcutCopy = ctrlShortcut keyC

-- | Ctrl+X / Cmd+X (Cut)
shortcutCut :: Shortcut
shortcutCut = ctrlShortcut keyX

-- | Ctrl+V / Cmd+V (Paste)
shortcutPaste :: Shortcut
shortcutPaste = ctrlShortcut keyV

-- | Ctrl+Z / Cmd+Z (Undo)
shortcutUndo :: Shortcut
shortcutUndo = ctrlShortcut keyZ

-- | Ctrl+Shift+Z or Ctrl+Y / Cmd+Shift+Z (Redo)
shortcutRedo :: Shortcut
shortcutRedo = ctrlShiftShortcut keyZ

-- | Ctrl+A / Cmd+A (Select All)
shortcutSelectAll :: Shortcut
shortcutSelectAll = ctrlShortcut keyA

-- | Ctrl+S / Cmd+S (Save)
shortcutSave :: Shortcut
shortcutSave = ctrlShortcut keyS

-- | Ctrl+F / Cmd+F (Find)
shortcutFind :: Shortcut
shortcutFind = ctrlShortcut keyF

-- | Ctrl+W / Cmd+W (Close)
shortcutClose :: Shortcut
shortcutClose = ctrlShortcut keyW

-- | Ctrl+N / Cmd+N (New)
shortcutNew :: Shortcut
shortcutNew = ctrlShortcut keyN

-- | Ctrl+O / Cmd+O (Open)
shortcutOpen :: Shortcut
shortcutOpen = ctrlShortcut keyO

-- | Redo variant with Y key (Windows style)
shortcutRedoY :: Shortcut
shortcutRedoY = ctrlShortcut keyY
