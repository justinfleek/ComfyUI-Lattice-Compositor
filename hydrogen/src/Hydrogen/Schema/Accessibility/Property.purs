-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ARIA Properties — Static relationship and characteristic attributes
-- |
-- | Properties define relationships between elements and provide additional
-- | information about element characteristics. Unlike states, properties
-- | change infrequently.
-- |
-- | ## Reference
-- | https://www.w3.org/TR/wai-aria-1.2/#state_prop_def
module Hydrogen.Schema.Accessibility.Property
  ( -- * Relationship Properties
    AriaLabelledBy(..)
  , AriaDescribedBy(..)
  , AriaControls(..)
  , AriaOwns(..)
  , AriaFlowTo(..)
  , AriaDetails(..)
  , AriaErrorMessage(..)
    -- * Widget Properties  
  , AriaAutocomplete(..)
  , AriaHaspopup(..)
  , AriaOrientation(..)
  , AriaPosInSet(..)
  , AriaSetSize(..)
  , AriaLevel(..)
  , AriaValueNow(..)
  , AriaValueMin(..)
  , AriaValueMax(..)
  , AriaValueText(..)
    -- * Label Properties
  , AriaLabel(..)
  , AriaPlaceholder(..)
  , AriaRoleDescription(..)
  ) where

import Prelude

import Data.Maybe (Maybe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // relationship properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | aria-labelledby: ID references to elements that label this element.
newtype AriaLabelledBy = AriaLabelledBy (Array String)

derive instance eqAriaLabelledBy :: Eq AriaLabelledBy

instance showAriaLabelledBy :: Show AriaLabelledBy where
  show (AriaLabelledBy ids) = "AriaLabelledBy " <> show ids

-- | aria-describedby: ID references to elements that describe this element.
newtype AriaDescribedBy = AriaDescribedBy (Array String)

derive instance eqAriaDescribedBy :: Eq AriaDescribedBy

instance showAriaDescribedBy :: Show AriaDescribedBy where
  show (AriaDescribedBy ids) = "AriaDescribedBy " <> show ids

-- | aria-controls: ID references to elements controlled by this element.
newtype AriaControls = AriaControls (Array String)

derive instance eqAriaControls :: Eq AriaControls

instance showAriaControls :: Show AriaControls where
  show (AriaControls ids) = "AriaControls " <> show ids

-- | aria-owns: ID references to elements owned by this element.
-- | Creates parent/child relationship when DOM doesn't reflect it.
newtype AriaOwns = AriaOwns (Array String)

derive instance eqAriaOwns :: Eq AriaOwns

instance showAriaOwns :: Show AriaOwns where
  show (AriaOwns ids) = "AriaOwns " <> show ids

-- | aria-flowto: ID references to next elements in reading order.
newtype AriaFlowTo = AriaFlowTo (Array String)

derive instance eqAriaFlowTo :: Eq AriaFlowTo

instance showAriaFlowTo :: Show AriaFlowTo where
  show (AriaFlowTo ids) = "AriaFlowTo " <> show ids

-- | aria-details: ID reference to element with detailed description.
newtype AriaDetails = AriaDetails String

derive instance eqAriaDetails :: Eq AriaDetails
derive newtype instance showAriaDetails :: Show AriaDetails

-- | aria-errormessage: ID reference to element containing error message.
newtype AriaErrorMessage = AriaErrorMessage String

derive instance eqAriaErrorMessage :: Eq AriaErrorMessage
derive newtype instance showAriaErrorMessage :: Show AriaErrorMessage

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // widget properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | aria-autocomplete: Type of autocomplete interaction for combobox/textbox.
data AriaAutocomplete
  = AutocompleteNone
  | AutocompleteInline
  | AutocompleteList
  | AutocompleteBoth

derive instance eqAriaAutocomplete :: Eq AriaAutocomplete

instance showAriaAutocomplete :: Show AriaAutocomplete where
  show AutocompleteNone = "none"
  show AutocompleteInline = "inline"
  show AutocompleteList = "list"
  show AutocompleteBoth = "both"

-- | aria-haspopup: Type of popup triggered by this element.
data AriaHaspopup
  = HasPopupFalse
  | HasPopupTrue
  | HasPopupMenu
  | HasPopupListbox
  | HasPopupTree
  | HasPopupGrid
  | HasPopupDialog

derive instance eqAriaHaspopup :: Eq AriaHaspopup

instance showAriaHaspopup :: Show AriaHaspopup where
  show HasPopupFalse = "false"
  show HasPopupTrue = "true"
  show HasPopupMenu = "menu"
  show HasPopupListbox = "listbox"
  show HasPopupTree = "tree"
  show HasPopupGrid = "grid"
  show HasPopupDialog = "dialog"

-- | aria-orientation: Indicates horizontal or vertical orientation.
data AriaOrientation
  = OrientationHorizontal
  | OrientationVertical
  | OrientationUndefined

derive instance eqAriaOrientation :: Eq AriaOrientation

instance showAriaOrientation :: Show AriaOrientation where
  show OrientationHorizontal = "horizontal"
  show OrientationVertical = "vertical"
  show OrientationUndefined = "undefined"

-- | aria-posinset: Position in the current set of items (1-indexed).
newtype AriaPosInSet = AriaPosInSet Int

derive instance eqAriaPosInSet :: Eq AriaPosInSet
derive newtype instance showAriaPosInSet :: Show AriaPosInSet

-- | aria-setsize: Total count of items in the current set.
-- | Nothing indicates unknown size.
newtype AriaSetSize = AriaSetSize (Maybe Int)

derive instance eqAriaSetSize :: Eq AriaSetSize

instance showAriaSetSize :: Show AriaSetSize where
  show (AriaSetSize s) = "AriaSetSize " <> show s

-- | aria-level: Hierarchical level (1-indexed).
newtype AriaLevel = AriaLevel Int

derive instance eqAriaLevel :: Eq AriaLevel
derive newtype instance showAriaLevel :: Show AriaLevel

-- | aria-valuenow: Current value for range widgets.
newtype AriaValueNow = AriaValueNow Number

derive instance eqAriaValueNow :: Eq AriaValueNow
derive newtype instance showAriaValueNow :: Show AriaValueNow

-- | aria-valuemin: Minimum value for range widgets.
newtype AriaValueMin = AriaValueMin Number

derive instance eqAriaValueMin :: Eq AriaValueMin
derive newtype instance showAriaValueMin :: Show AriaValueMin

-- | aria-valuemax: Maximum value for range widgets.
newtype AriaValueMax = AriaValueMax Number

derive instance eqAriaValueMax :: Eq AriaValueMax
derive newtype instance showAriaValueMax :: Show AriaValueMax

-- | aria-valuetext: Human-readable representation of value.
newtype AriaValueText = AriaValueText String

derive instance eqAriaValueText :: Eq AriaValueText
derive newtype instance showAriaValueText :: Show AriaValueText

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // label properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | aria-label: Human-readable label text.
newtype AriaLabel = AriaLabel String

derive instance eqAriaLabel :: Eq AriaLabel
derive newtype instance showAriaLabel :: Show AriaLabel

-- | aria-placeholder: Short hint for expected input.
newtype AriaPlaceholder = AriaPlaceholder String

derive instance eqAriaPlaceholder :: Eq AriaPlaceholder
derive newtype instance showAriaPlaceholder :: Show AriaPlaceholder

-- | aria-roledescription: Human-readable description of the role.
-- | Use sparingly — most roles don't need custom descriptions.
newtype AriaRoleDescription = AriaRoleDescription String

derive instance eqAriaRoleDescription :: Eq AriaRoleDescription
derive newtype instance showAriaRoleDescription :: Show AriaRoleDescription
