-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // element // button // semantics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ButtonSemantics — purpose, identity, and accessibility atoms.
-- |
-- | ## Atoms Included
-- |
-- | - ButtonPurpose (action, submit, toggle, media, etc.)
-- | - ButtonIdentity (UUID5 deterministic identity)
-- | - Toggle state (for toggle buttons)
-- | - Popup type (for menu/dialog triggers)
-- | - ARIA attributes

module Hydrogen.Schema.Element.Button.Semantics
  ( -- * Button Semantics Record
    ButtonSemantics
  , defaultSemantics
  , actionSemantics
  , submitSemantics
  , toggleSemantics
    -- * Accessors
  , semPurpose
  , semLabel
  , semToggleState
  , semDisabled
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.ButtonSemantics
  ( ButtonPurpose(ActionButton, FormSubmit, ToggleControl)
  , ToggleState(Pressed, Unpressed)
  , PopupType
  ) as Sem

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // button semantics
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Semantics atoms for button purpose and accessibility.
-- |
-- | What the button DOES, not how it looks.
type ButtonSemantics =
  { -- Purpose
    purpose :: Sem.ButtonPurpose         -- ^ Semantic purpose
  , label :: String                      -- ^ Visible or ARIA label
    -- State
  , toggleState :: Maybe Sem.ToggleState -- ^ For toggle buttons
  , popupType :: Maybe Sem.PopupType     -- ^ For menu/dialog triggers
    -- Flags
  , disabled :: Boolean                  -- ^ Is button disabled?
  , loading :: Boolean                   -- ^ Is button in loading state?
    -- Accessibility
  , ariaDescribedBy :: Maybe String      -- ^ ID of describing element
  , ariaControls :: Maybe String         -- ^ ID of controlled element
  }

-- | Default semantics: action button with label.
defaultSemantics :: String -> ButtonSemantics
defaultSemantics lbl =
  { purpose: Sem.ActionButton
  , label: lbl
  , toggleState: Nothing
  , popupType: Nothing
  , disabled: false
  , loading: false
  , ariaDescribedBy: Nothing
  , ariaControls: Nothing
  }

-- | Action button semantics (general purpose).
actionSemantics :: String -> ButtonSemantics
actionSemantics = defaultSemantics

-- | Submit button semantics (form submission).
submitSemantics :: String -> ButtonSemantics
submitSemantics lbl = (defaultSemantics lbl) { purpose = Sem.FormSubmit }

-- | Toggle button semantics (on/off state).
toggleSemantics :: String -> Boolean -> ButtonSemantics
toggleSemantics lbl isPressed = (defaultSemantics lbl)
  { purpose = Sem.ToggleControl
  , toggleState = Just (if isPressed then Sem.Pressed else Sem.Unpressed)
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get purpose.
semPurpose :: ButtonSemantics -> Sem.ButtonPurpose
semPurpose s = s.purpose

-- | Get label.
semLabel :: ButtonSemantics -> String
semLabel s = s.label

-- | Get toggle state.
semToggleState :: ButtonSemantics -> Maybe Sem.ToggleState
semToggleState s = s.toggleState

-- | Get disabled flag.
semDisabled :: ButtonSemantics -> Boolean
semDisabled s = s.disabled
