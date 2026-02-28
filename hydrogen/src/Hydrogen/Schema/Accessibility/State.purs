-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ARIA States — Dynamic state attributes
-- |
-- | States reflect the current condition of an element that may change
-- | during user interaction. Unlike properties, states are expected to
-- | change frequently.
-- |
-- | ## Reference
-- | https://www.w3.org/TR/wai-aria-1.2/#state_prop_def
module Hydrogen.Schema.Accessibility.State
  ( -- * Tristate Values
    Tristate(..)
  , tristateToString
    -- * ARIA States
  , AriaExpanded(..)
  , AriaSelected(..)
  , AriaPressed(..)
  , AriaChecked(..)
  , AriaDisabled(..)
  , AriaHidden(..)
  , AriaInvalid(..)
  , AriaBusy(..)
  , AriaCurrent(..)
  , AriaGrabbed(..)
    -- * State Rendering
  , expandedToAttr
  , selectedToAttr
  , pressedToAttr
  , checkedToAttr
  , disabledToAttr
  , hiddenToAttr
  , invalidToAttr
  , busyToAttr
  , currentToAttr
  , grabbedToAttr
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // tristate values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tristate for aria-pressed, aria-checked where "mixed" is valid.
data Tristate
  = TriFalse
  | TriTrue
  | TriMixed

derive instance eqTristate :: Eq Tristate

instance showTristate :: Show Tristate where
  show = tristateToString

-- | Convert tristate to ARIA attribute value.
tristateToString :: Tristate -> String
tristateToString TriFalse = "false"
tristateToString TriTrue = "true"
tristateToString TriMixed = "mixed"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // aria states
-- ═════════════════════════════════════════════════════════════════════════════

-- | aria-expanded: Indicates if a collapsible element is expanded.
newtype AriaExpanded = AriaExpanded Boolean

derive instance eqAriaExpanded :: Eq AriaExpanded
derive newtype instance showAriaExpanded :: Show AriaExpanded

-- | aria-selected: Indicates the current selection state.
newtype AriaSelected = AriaSelected Boolean

derive instance eqAriaSelected :: Eq AriaSelected
derive newtype instance showAriaSelected :: Show AriaSelected

-- | aria-pressed: Indicates the pressed state of a toggle button.
-- | Can be true, false, or mixed (partially pressed).
newtype AriaPressed = AriaPressed Tristate

derive instance eqAriaPressed :: Eq AriaPressed

instance showAriaPressed :: Show AriaPressed where
  show (AriaPressed t) = "AriaPressed " <> show t

-- | aria-checked: Indicates the checked state of checkboxes/radios.
-- | Can be true, false, or mixed (indeterminate).
newtype AriaChecked = AriaChecked Tristate

derive instance eqAriaChecked :: Eq AriaChecked

instance showAriaChecked :: Show AriaChecked where
  show (AriaChecked t) = "AriaChecked " <> show t

-- | aria-disabled: Indicates the element is perceivable but not operable.
newtype AriaDisabled = AriaDisabled Boolean

derive instance eqAriaDisabled :: Eq AriaDisabled
derive newtype instance showAriaDisabled :: Show AriaDisabled

-- | aria-hidden: Indicates the element is not exposed to the accessibility API.
newtype AriaHidden = AriaHidden Boolean

derive instance eqAriaHidden :: Eq AriaHidden
derive newtype instance showAriaHidden :: Show AriaHidden

-- | aria-invalid: Indicates the entered value does not conform to expected format.
data AriaInvalid
  = InvalidFalse
  | InvalidTrue
  | InvalidGrammar
  | InvalidSpelling

derive instance eqAriaInvalid :: Eq AriaInvalid

instance showAriaInvalid :: Show AriaInvalid where
  show InvalidFalse = "false"
  show InvalidTrue = "true"
  show InvalidGrammar = "grammar"
  show InvalidSpelling = "spelling"

-- | aria-busy: Indicates an element is being modified.
newtype AriaBusy = AriaBusy Boolean

derive instance eqAriaBusy :: Eq AriaBusy
derive newtype instance showAriaBusy :: Show AriaBusy

-- | aria-current: Indicates the current item within a set.
data AriaCurrent
  = CurrentFalse
  | CurrentTrue
  | CurrentPage
  | CurrentStep
  | CurrentLocation
  | CurrentDate
  | CurrentTime

derive instance eqAriaCurrent :: Eq AriaCurrent

instance showAriaCurrent :: Show AriaCurrent where
  show CurrentFalse = "false"
  show CurrentTrue = "true"
  show CurrentPage = "page"
  show CurrentStep = "step"
  show CurrentLocation = "location"
  show CurrentDate = "date"
  show CurrentTime = "time"

-- | aria-grabbed: Indicates the grabbed state in drag-and-drop.
-- | Nothing = undefined (not grabbable), Just false = grabbable, Just true = grabbed
newtype AriaGrabbed = AriaGrabbed (Maybe Boolean)

derive instance eqAriaGrabbed :: Eq AriaGrabbed

instance showAriaGrabbed :: Show AriaGrabbed where
  show (AriaGrabbed Nothing) = "undefined"
  show (AriaGrabbed (Just b)) = show b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // state rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert AriaExpanded to attribute value.
expandedToAttr :: AriaExpanded -> String
expandedToAttr (AriaExpanded true) = "true"
expandedToAttr (AriaExpanded false) = "false"

-- | Convert AriaSelected to attribute value.
selectedToAttr :: AriaSelected -> String
selectedToAttr (AriaSelected true) = "true"
selectedToAttr (AriaSelected false) = "false"

-- | Convert AriaPressed to attribute value.
pressedToAttr :: AriaPressed -> String
pressedToAttr (AriaPressed t) = tristateToString t

-- | Convert AriaChecked to attribute value.
checkedToAttr :: AriaChecked -> String
checkedToAttr (AriaChecked t) = tristateToString t

-- | Convert AriaDisabled to attribute value.
disabledToAttr :: AriaDisabled -> String
disabledToAttr (AriaDisabled true) = "true"
disabledToAttr (AriaDisabled false) = "false"

-- | Convert AriaHidden to attribute value.
hiddenToAttr :: AriaHidden -> String
hiddenToAttr (AriaHidden true) = "true"
hiddenToAttr (AriaHidden false) = "false"

-- | Convert AriaInvalid to attribute value.
invalidToAttr :: AriaInvalid -> String
invalidToAttr InvalidFalse = "false"
invalidToAttr InvalidTrue = "true"
invalidToAttr InvalidGrammar = "grammar"
invalidToAttr InvalidSpelling = "spelling"

-- | Convert AriaBusy to attribute value.
busyToAttr :: AriaBusy -> String
busyToAttr (AriaBusy true) = "true"
busyToAttr (AriaBusy false) = "false"

-- | Convert AriaCurrent to attribute value.
currentToAttr :: AriaCurrent -> String
currentToAttr CurrentFalse = "false"
currentToAttr CurrentTrue = "true"
currentToAttr CurrentPage = "page"
currentToAttr CurrentStep = "step"
currentToAttr CurrentLocation = "location"
currentToAttr CurrentDate = "date"
currentToAttr CurrentTime = "time"

-- | Convert AriaGrabbed to attribute value.
grabbedToAttr :: AriaGrabbed -> String
grabbedToAttr (AriaGrabbed Nothing) = "undefined"
grabbedToAttr (AriaGrabbed (Just true)) = "true"
grabbedToAttr (AriaGrabbed (Just false)) = "false"
