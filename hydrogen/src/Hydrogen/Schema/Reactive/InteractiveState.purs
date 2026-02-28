-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // reactive // interactive-state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | InteractiveState - compound states for interactive elements.
-- |
-- | Combines boolean flags into semantic interaction states that map
-- | directly to CSS pseudo-classes and ARIA states.

module Hydrogen.Schema.Reactive.InteractiveState
  ( -- * Pointer State
    PointerState(..)
  , pointerIdle
  , pointerHover
  , pointerPressed
  , isPointerOver
  , isPointerDown
  -- * Focus State
  , FocusState(..)
  , focusNone
  , focusKeyboard
  , focusPointer
  , focusProgrammatic
  , hasFocus
  , showFocusRing
  -- * Activation State
  , ActivationState(..)
  , inactive
  , activating
  , active
  , deactivating
  -- * Combined Interactive State
  , InteractiveState
  , interactiveState
  , defaultInteractive
  , isInteractable
  , isEngaged
  , toAriaAttributes
  , toLegacyCssClasses
  -- * Pointer Device
  , PointerDevice(..)
  , pointerDevice
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // pointer state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of pointer (mouse/touch/pen) relative to element
data PointerState
  = PointerIdle      -- ^ Not interacting
  | PointerHover     -- ^ Pointer over element
  | PointerPressed   -- ^ Pointer down on element
  | PointerDragging  -- ^ Being dragged

derive instance eqPointerState :: Eq PointerState
derive instance ordPointerState :: Ord PointerState

instance showPointerState :: Show PointerState where
  show PointerIdle = "idle"
  show PointerHover = "hover"
  show PointerPressed = "pressed"
  show PointerDragging = "dragging"

pointerIdle :: PointerState
pointerIdle = PointerIdle

pointerHover :: PointerState
pointerHover = PointerHover

pointerPressed :: PointerState
pointerPressed = PointerPressed

isPointerOver :: PointerState -> Boolean
isPointerOver PointerIdle = false
isPointerOver _ = true

isPointerDown :: PointerState -> Boolean
isPointerDown PointerPressed = true
isPointerDown PointerDragging = true
isPointerDown _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // focus state
-- ═════════════════════════════════════════════════════════════════════════════

-- | How the element received focus
-- |
-- | Distinguishing focus source enables :focus-visible behavior
data FocusState
  = FocusNone        -- ^ Not focused
  | FocusKeyboard    -- ^ Focused via keyboard (Tab, arrows)
  | FocusPointer     -- ^ Focused via mouse/touch click
  | FocusProgrammatic -- ^ Focused via JavaScript

derive instance eqFocusState :: Eq FocusState
derive instance ordFocusState :: Ord FocusState

instance showFocusState :: Show FocusState where
  show FocusNone = "none"
  show FocusKeyboard = "keyboard"
  show FocusPointer = "pointer"
  show FocusProgrammatic = "programmatic"

focusNone :: FocusState
focusNone = FocusNone

focusKeyboard :: FocusState
focusKeyboard = FocusKeyboard

focusPointer :: FocusState
focusPointer = FocusPointer

focusProgrammatic :: FocusState
focusProgrammatic = FocusProgrammatic

-- | Element has any kind of focus
hasFocus :: FocusState -> Boolean
hasFocus FocusNone = false
hasFocus _ = true

-- | Should show focus ring (keyboard only per :focus-visible)
showFocusRing :: FocusState -> Boolean
showFocusRing FocusKeyboard = true
showFocusRing _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // activation state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Activation lifecycle for animated state changes
data ActivationState
  = Inactive      -- ^ Default state
  | Activating    -- ^ Transitioning to active (enter animation)
  | Active        -- ^ Fully active
  | Deactivating  -- ^ Transitioning to inactive (exit animation)

derive instance eqActivationState :: Eq ActivationState
derive instance ordActivationState :: Ord ActivationState

instance showActivationState :: Show ActivationState where
  show Inactive = "inactive"
  show Activating = "activating"
  show Active = "active"
  show Deactivating = "deactivating"

inactive :: ActivationState
inactive = Inactive

activating :: ActivationState
activating = Activating

active :: ActivationState
active = Active

deactivating :: ActivationState
deactivating = Deactivating

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // pointer device
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of pointing device
data PointerDevice
  = Mouse
  | Touch
  | Pen
  | Unknown

derive instance eqPointerDevice :: Eq PointerDevice
derive instance ordPointerDevice :: Ord PointerDevice

instance showPointerDevice :: Show PointerDevice where
  show Mouse = "mouse"
  show Touch = "touch"
  show Pen = "pen"
  show Unknown = "unknown"

pointerDevice :: String -> PointerDevice
pointerDevice "mouse" = Mouse
pointerDevice "touch" = Touch
pointerDevice "pen" = Pen
pointerDevice _ = Unknown

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // combined interactive state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete interactive state for an element
-- |
-- | Combines all interaction dimensions into a single record
type InteractiveState =
  { pointer :: PointerState
  , focus :: FocusState
  , activation :: ActivationState
  , disabled :: Boolean
  , loading :: Boolean
  , device :: PointerDevice
  }

-- | Create an interactive state
interactiveState 
  :: PointerState 
  -> FocusState 
  -> ActivationState 
  -> Boolean 
  -> Boolean 
  -> PointerDevice 
  -> InteractiveState
interactiveState p f a d l dev =
  { pointer: p
  , focus: f
  , activation: a
  , disabled: d
  , loading: l
  , device: dev
  }

-- | Default non-interactive state
defaultInteractive :: InteractiveState
defaultInteractive =
  { pointer: PointerIdle
  , focus: FocusNone
  , activation: Inactive
  , disabled: false
  , loading: false
  , device: Unknown
  }

-- | Can receive interaction
isInteractable :: InteractiveState -> Boolean
isInteractable s = not s.disabled && not s.loading

-- | User is actively engaging
isEngaged :: InteractiveState -> Boolean
isEngaged s = isPointerOver s.pointer || hasFocus s.focus

-- | Generate ARIA attributes from state
toAriaAttributes :: InteractiveState -> Array { key :: String, value :: String }
toAriaAttributes s =
  [ { key: "aria-disabled", value: if s.disabled then "true" else "false" }
  , { key: "aria-busy", value: if s.loading then "true" else "false" }
  ]

-- | Generate CSS class names from state
toLegacyCssClasses :: InteractiveState -> Array String
toLegacyCssClasses s = 
  (if isPointerOver s.pointer then ["hover"] else []) <>
  (if hasFocus s.focus then ["focus"] else []) <>
  (if showFocusRing s.focus then ["focus-visible"] else []) <>
  (if isPointerDown s.pointer then ["active", "pressed"] else []) <>
  (if s.disabled then ["disabled"] else []) <>
  (if s.loading then ["loading"] else []) <>
  (case s.activation of
    Inactive -> []
    Activating -> ["activating", "entering"]
    Active -> ["active"]
    Deactivating -> ["deactivating", "exiting"])
