-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // keyboard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Global keyboard shortcut management
-- |
-- | Register keyboard shortcuts with modifier keys, scopes, and sequences.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Util.Keyboard as Keyboard
-- |
-- | -- Simple shortcut
-- | unregister <- Keyboard.registerShortcut
-- |   (Keyboard.parseShortcut "Ctrl+K")
-- |   (Console.log "Ctrl+K pressed!")
-- |
-- | -- With scope (only active in certain contexts)
-- | unregister <- Keyboard.registerScopedShortcut "editor"
-- |   (Keyboard.parseShortcut "Ctrl+S")
-- |   saveDocument
-- |
-- | -- Key sequence (vim-style)
-- | unregister <- Keyboard.registerSequence ["g", "i"]
-- |   (Console.log "Go to inbox!")
-- |
-- | -- Prevent default
-- | unregister <- Keyboard.registerShortcut
-- |   (Keyboard.parseShortcut "Ctrl+S" # Keyboard.preventDefault)
-- |   saveDocument
-- | ```
module Hydrogen.Util.Keyboard
  ( -- * Types
    Shortcut
  , ShortcutConfig
  , Modifier(..)
  , Scope
    -- * Shortcut Creation
  , shortcut
  , parseShortcut
  , withModifiers
    -- * Shortcut Modifiers
  , ctrl
  , alt
  , shift
  , meta
  , preventDefault
  , stopPropagation
    -- * Registration
  , registerShortcut
  , registerScopedShortcut
  , unregisterAll
    -- * Scope Management
  , createScope
  , activateScope
  , deactivateScope
  , isActiveScope
  , globalScope
    -- * Key Sequences
  , registerSequence
  , registerScopedSequence
  , sequenceTimeout
    -- * Help Integration
  , ShortcutInfo
  , getRegisteredShortcuts
  , formatShortcut
  , formatForPlatform
    -- * Utilities
  , isInputFocused
  , shouldIgnore
  ) where

import Prelude hiding (when)

import Data.Array (filter, elem)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String
import Data.String.Pattern (Pattern(Pattern))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A keyboard shortcut
type Shortcut =
  { key :: String
  , modifiers :: Array Modifier
  , config :: ShortcutConfig
  }

-- | Shortcut configuration
type ShortcutConfig =
  { preventDefault :: Boolean
  , stopPropagation :: Boolean
  , ignoreInputs :: Boolean
  , description :: String
  }

-- | Keyboard modifiers
data Modifier
  = Ctrl
  | Alt
  | Shift
  | Meta  -- Cmd on Mac, Win on Windows

derive instance eqModifier :: Eq Modifier
derive instance ordModifier :: Ord Modifier

instance showModifier :: Show Modifier where
  show Ctrl = "Ctrl"
  show Alt = "Alt"
  show Shift = "Shift"
  show Meta = "Meta"

-- | Scope for scoped shortcuts
newtype Scope = Scope String

derive instance eqScope :: Eq Scope
derive instance ordScope :: Ord Scope

instance showScope :: Show Scope where
  show (Scope s) = "Scope(" <> s <> ")"

-- | Shortcut info for help display
type ShortcutInfo =
  { shortcut :: Shortcut
  , scope :: Scope
  , description :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═════════════════════════════════════════════════════════════════════════════

foreign import registerShortcutImpl
  :: { key :: String
     , ctrl :: Boolean
     , alt :: Boolean
     , shift :: Boolean
     , meta :: Boolean
     , preventDefault :: Boolean
     , stopPropagation :: Boolean
     , ignoreInputs :: Boolean
     }
  -> Effect Unit
  -> Effect (Effect Unit)

foreign import registerSequenceImpl
  :: Array String
  -> Int  -- timeout
  -> Effect Unit
  -> Effect (Effect Unit)

foreign import isInputFocusedImpl :: Effect Boolean

foreign import isMacPlatformImpl :: Effect Boolean

-- Global scope storage
foreign import addToShortcutRegistry
  :: { key :: String, scope :: String, description :: String }
  -> Effect Unit

foreign import getShortcutRegistry
  :: Effect (Array { key :: String, scope :: String, description :: String })

foreign import clearShortcutRegistry :: Effect Unit

-- Scope management
foreign import activeScopesRef :: Effect (Ref (Array String))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // shortcut creation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default shortcut config
defaultConfig :: ShortcutConfig
defaultConfig =
  { preventDefault: true
  , stopPropagation: false
  , ignoreInputs: true
  , description: ""
  }

-- | Create a shortcut from a key
shortcut :: String -> Shortcut
shortcut key =
  { key
  , modifiers: []
  , config: defaultConfig
  }

-- | Parse a shortcut string
-- |
-- | Supports formats like:
-- | - "Ctrl+K", "Cmd+Shift+P", "Alt+1"
-- | - Uses "Cmd" as alias for Meta (platform-aware)
-- |
-- | ```purescript
-- | parseShortcut "Ctrl+K"       -- Ctrl + K
-- | parseShortcut "Ctrl+Shift+P" -- Ctrl + Shift + P
-- | parseShortcut "Escape"       -- Escape (no modifiers)
-- | ```
parseShortcut :: String -> Shortcut
parseShortcut str =
  let
    parts = String.split (Pattern "+") str
    mods = filter isModifier parts
    keys = filter (not <<< isModifier) parts
    key = case keys of
      [k] -> k
      _ -> ""
  in
    { key
    , modifiers: parseModifiers mods
    , config: defaultConfig
    }
  where
  isModifier :: String -> Boolean
  isModifier s = elem (String.toLower s) ["ctrl", "alt", "shift", "meta", "cmd"]
  
  parseModifiers :: Array String -> Array Modifier
  parseModifiers = map parseModifier >>> filter isJust >>> map unsafeFromJust
  
  parseModifier :: String -> Maybe Modifier
  parseModifier s = case String.toLower s of
    "ctrl" -> Just Ctrl
    "alt" -> Just Alt
    "shift" -> Just Shift
    "meta" -> Just Meta
    "cmd" -> Just Meta
    _ -> Nothing
  
  isJust :: forall a. Maybe a -> Boolean
  isJust (Just _) = true
  isJust Nothing = false
  
  unsafeFromJust :: forall a. Maybe a -> a
  unsafeFromJust (Just a) = a
  unsafeFromJust Nothing = unsafeFromJust Nothing -- Will never hit

-- | Add modifiers to a shortcut
withModifiers :: Array Modifier -> Shortcut -> Shortcut
withModifiers mods s = s { modifiers = s.modifiers <> mods }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // shortcut modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add Ctrl modifier
ctrl :: Shortcut -> Shortcut
ctrl s = s { modifiers = s.modifiers <> [Ctrl] }

-- | Add Alt modifier
alt :: Shortcut -> Shortcut
alt s = s { modifiers = s.modifiers <> [Alt] }

-- | Add Shift modifier
shift :: Shortcut -> Shortcut
shift s = s { modifiers = s.modifiers <> [Shift] }

-- | Add Meta modifier (Cmd on Mac)
meta :: Shortcut -> Shortcut
meta s = s { modifiers = s.modifiers <> [Meta] }

-- | Set preventDefault
preventDefault :: Shortcut -> Shortcut
preventDefault s = s { config = s.config { preventDefault = true } }

-- | Set stopPropagation
stopPropagation :: Shortcut -> Shortcut
stopPropagation s = s { config = s.config { stopPropagation = true } }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // registration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Register a global keyboard shortcut
-- |
-- | Returns an unregister function.
registerShortcut :: Shortcut -> Effect Unit -> Effect (Effect Unit)
registerShortcut s callback = do
  addToShortcutRegistry
    { key: formatShortcut s
    , scope: "global"
    , description: s.config.description
    }
  registerShortcutImpl
    { key: s.key
    , ctrl: elem Ctrl s.modifiers
    , alt: elem Alt s.modifiers
    , shift: elem Shift s.modifiers
    , meta: elem Meta s.modifiers
    , preventDefault: s.config.preventDefault
    , stopPropagation: s.config.stopPropagation
    , ignoreInputs: s.config.ignoreInputs
    }
    callback

-- | Register a scoped shortcut
-- |
-- | Only active when the scope is active.
registerScopedShortcut :: Scope -> Shortcut -> Effect Unit -> Effect (Effect Unit)
registerScopedShortcut (Scope scopeName) s callback = do
  addToShortcutRegistry
    { key: formatShortcut s
    , scope: scopeName
    , description: s.config.description
    }
  registerShortcutImpl
    { key: s.key
    , ctrl: elem Ctrl s.modifiers
    , alt: elem Alt s.modifiers
    , shift: elem Shift s.modifiers
    , meta: elem Meta s.modifiers
    , preventDefault: s.config.preventDefault
    , stopPropagation: s.config.stopPropagation
    , ignoreInputs: s.config.ignoreInputs
    }
    do
      active <- isActiveScope (Scope scopeName)
      when active callback

-- | Unregister all shortcuts
unregisterAll :: Effect Unit
unregisterAll = clearShortcutRegistry

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // scope management
-- ═════════════════════════════════════════════════════════════════════════════

-- | Global scope (always active)
globalScope :: Scope
globalScope = Scope "global"

-- | Create a new scope
createScope :: String -> Scope
createScope = Scope

-- | Activate a scope
activateScope :: Scope -> Effect Unit
activateScope (Scope scopeName) = do
  ref <- activeScopesRef
  Ref.modify_ (\scopes -> if elem scopeName scopes then scopes else scopes <> [scopeName]) ref

-- | Deactivate a scope
deactivateScope :: Scope -> Effect Unit
deactivateScope (Scope scopeName) = do
  ref <- activeScopesRef
  Ref.modify_ (filter (_ /= scopeName)) ref

-- | Check if a scope is active
isActiveScope :: Scope -> Effect Boolean
isActiveScope (Scope scopeName) = do
  if scopeName == "global"
    then pure true
    else do
      ref <- activeScopesRef
      scopes <- Ref.read ref
      pure $ elem scopeName scopes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // key sequences
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default sequence timeout (1000ms)
defaultSequenceTimeout :: Int
defaultSequenceTimeout = 1000

-- | Register a key sequence (vim-style)
-- |
-- | ```purescript
-- | registerSequence ["g", "i"] (Console.log "Go to inbox")
-- | ```
registerSequence :: Array String -> Effect Unit -> Effect (Effect Unit)
registerSequence keys callback =
  registerSequenceImpl keys defaultSequenceTimeout callback

-- | Register a scoped key sequence
registerScopedSequence :: Scope -> Array String -> Effect Unit -> Effect (Effect Unit)
registerScopedSequence scope keys callback = do
  registerSequenceImpl keys defaultSequenceTimeout do
    active <- isActiveScope scope
    when active callback

-- | Set custom sequence timeout
sequenceTimeout :: Int -> Int
sequenceTimeout = identity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // help integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all registered shortcuts
getRegisteredShortcuts :: Effect (Array ShortcutInfo)
getRegisteredShortcuts = do
  registry <- getShortcutRegistry
  pure $ map toShortcutInfo registry
  where
  toShortcutInfo r =
    { shortcut: parseShortcut r.key
    , scope: Scope r.scope
    , description: r.description
    }

-- | Format shortcut for display
formatShortcut :: Shortcut -> String
formatShortcut s =
  let
    modStrs = map show s.modifiers
    parts = modStrs <> [s.key]
  in
    String.joinWith "+" parts

-- | Format shortcut for current platform
-- |
-- | Uses Cmd symbol on Mac, Ctrl on others.
formatForPlatform :: Shortcut -> Effect String
formatForPlatform s = do
  isMac <- isMacPlatformImpl
  let
    formatMod :: Modifier -> String
    formatMod = case _ of
      Meta -> if isMac then "\x2318" else "Ctrl"  -- Cmd symbol
      Ctrl -> if isMac then "\x2303" else "Ctrl"  -- Control symbol
      Alt -> if isMac then "\x2325" else "Alt"    -- Option symbol
      Shift -> if isMac then "\x21E7" else "Shift" -- Shift symbol
    modStrs = map formatMod s.modifiers
    parts = modStrs <> [s.key]
  pure $ String.joinWith (if isMac then "" else "+") parts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if an input element is focused
isInputFocused :: Effect Boolean
isInputFocused = isInputFocusedImpl

-- | Check if shortcut should be ignored
-- |
-- | Returns true if an input is focused and shortcut should respect that.
shouldIgnore :: Shortcut -> Effect Boolean
shouldIgnore s = 
  if s.config.ignoreInputs
    then isInputFocused
    else pure false

-- Local when helper
when :: Boolean -> Effect Unit -> Effect Unit
when true action = action
when false _ = pure unit
