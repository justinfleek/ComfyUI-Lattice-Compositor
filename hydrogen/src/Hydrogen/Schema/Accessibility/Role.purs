-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ARIA Roles — WAI-ARIA 1.2 role taxonomy
-- |
-- | Roles define what an element IS to assistive technology.
-- | Per WAI-ARIA 1.2 specification.
-- |
-- | ## Categories
-- | - Widget roles (interactive elements)
-- | - Document structure roles (content organization)
-- | - Landmark roles (page regions) — see Landmark.purs
-- | - Live region roles (dynamic content)
-- | - Window roles (dialogs, alerts)
-- |
-- | ## Reference
-- | https://www.w3.org/TR/wai-aria-1.2/#role_definitions
module Hydrogen.Schema.Accessibility.Role
  ( -- * Widget Roles
    WidgetRole(..)
  , widgetRoleToString
    -- * Composite Widget Roles
  , CompositeRole(..)
  , compositeRoleToString
    -- * Document Structure Roles
  , StructureRole(..)
  , structureRoleToString
    -- * Window Roles
  , WindowRole(..)
  , windowRoleToString
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // widget roles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Widget roles for interactive UI elements.
-- |
-- | These roles indicate elements that users interact with directly.
data WidgetRole
  = RoleButton
  | RoleCheckbox
  | RoleGridcell
  | RoleLink
  | RoleMenuitem
  | RoleMenuitemcheckbox
  | RoleMenuitemradio
  | RoleOption
  | RoleProgressbar
  | RoleRadio
  | RoleScrollbar
  | RoleSearchbox
  | RoleSeparator
  | RoleSlider
  | RoleSpinbutton
  | RoleSwitch
  | RoleTab
  | RoleTabpanel
  | RoleTextbox
  | RoleTreeitem

derive instance eqWidgetRole :: Eq WidgetRole

instance showWidgetRole :: Show WidgetRole where
  show = widgetRoleToString

-- | Convert widget role to ARIA role string.
widgetRoleToString :: WidgetRole -> String
widgetRoleToString RoleButton = "button"
widgetRoleToString RoleCheckbox = "checkbox"
widgetRoleToString RoleGridcell = "gridcell"
widgetRoleToString RoleLink = "link"
widgetRoleToString RoleMenuitem = "menuitem"
widgetRoleToString RoleMenuitemcheckbox = "menuitemcheckbox"
widgetRoleToString RoleMenuitemradio = "menuitemradio"
widgetRoleToString RoleOption = "option"
widgetRoleToString RoleProgressbar = "progressbar"
widgetRoleToString RoleRadio = "radio"
widgetRoleToString RoleScrollbar = "scrollbar"
widgetRoleToString RoleSearchbox = "searchbox"
widgetRoleToString RoleSeparator = "separator"
widgetRoleToString RoleSlider = "slider"
widgetRoleToString RoleSpinbutton = "spinbutton"
widgetRoleToString RoleSwitch = "switch"
widgetRoleToString RoleTab = "tab"
widgetRoleToString RoleTabpanel = "tabpanel"
widgetRoleToString RoleTextbox = "textbox"
widgetRoleToString RoleTreeitem = "treeitem"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // composite widget roles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Composite widget roles — containers that manage child widgets.
-- |
-- | These roles require specific child roles and manage focus.
data CompositeRole
  = RoleCombobox
  | RoleGrid
  | RoleListbox
  | RoleMenu
  | RoleMenubar
  | RoleRadiogroup
  | RoleTablist
  | RoleTree
  | RoleTreegrid

derive instance eqCompositeRole :: Eq CompositeRole

instance showCompositeRole :: Show CompositeRole where
  show = compositeRoleToString

-- | Convert composite role to ARIA role string.
compositeRoleToString :: CompositeRole -> String
compositeRoleToString RoleCombobox = "combobox"
compositeRoleToString RoleGrid = "grid"
compositeRoleToString RoleListbox = "listbox"
compositeRoleToString RoleMenu = "menu"
compositeRoleToString RoleMenubar = "menubar"
compositeRoleToString RoleRadiogroup = "radiogroup"
compositeRoleToString RoleTablist = "tablist"
compositeRoleToString RoleTree = "tree"
compositeRoleToString RoleTreegrid = "treegrid"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // document structure roles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Document structure roles — content organization.
-- |
-- | These roles describe the structure and meaning of content.
data StructureRole
  = RoleApplication
  | RoleArticle
  | RoleBlockquote
  | RoleCaption
  | RoleCell
  | RoleColumnheader
  | RoleDefinition
  | RoleDirectory
  | RoleDocument
  | RoleFeed
  | RoleFigure
  | RoleGroup
  | RoleHeading
  | RoleImg
  | RoleList
  | RoleListitem
  | RoleMath
  | RoleMeter
  | RoleNote
  | RoleParagraph
  | RoleRow
  | RoleRowgroup
  | RoleRowheader
  | RoleTable
  | RoleTerm
  | RoleToolbar
  | RoleTooltip

derive instance eqStructureRole :: Eq StructureRole

instance showStructureRole :: Show StructureRole where
  show = structureRoleToString

-- | Convert structure role to ARIA role string.
structureRoleToString :: StructureRole -> String
structureRoleToString RoleApplication = "application"
structureRoleToString RoleArticle = "article"
structureRoleToString RoleBlockquote = "blockquote"
structureRoleToString RoleCaption = "caption"
structureRoleToString RoleCell = "cell"
structureRoleToString RoleColumnheader = "columnheader"
structureRoleToString RoleDefinition = "definition"
structureRoleToString RoleDirectory = "directory"
structureRoleToString RoleDocument = "document"
structureRoleToString RoleFeed = "feed"
structureRoleToString RoleFigure = "figure"
structureRoleToString RoleGroup = "group"
structureRoleToString RoleHeading = "heading"
structureRoleToString RoleImg = "img"
structureRoleToString RoleList = "list"
structureRoleToString RoleListitem = "listitem"
structureRoleToString RoleMath = "math"
structureRoleToString RoleMeter = "meter"
structureRoleToString RoleNote = "note"
structureRoleToString RoleParagraph = "paragraph"
structureRoleToString RoleRow = "row"
structureRoleToString RoleRowgroup = "rowgroup"
structureRoleToString RoleRowheader = "rowheader"
structureRoleToString RoleTable = "table"
structureRoleToString RoleTerm = "term"
structureRoleToString RoleToolbar = "toolbar"
structureRoleToString RoleTooltip = "tooltip"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // window roles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Window roles — dialogs and alerts.
-- |
-- | These roles create modal or non-modal overlays.
data WindowRole
  = RoleAlert
  | RoleAlertdialog
  | RoleDialog

derive instance eqWindowRole :: Eq WindowRole

instance showWindowRole :: Show WindowRole where
  show = windowRoleToString

-- | Convert window role to ARIA role string.
windowRoleToString :: WindowRole -> String
windowRoleToString RoleAlert = "alert"
windowRoleToString RoleAlertdialog = "alertdialog"
windowRoleToString RoleDialog = "dialog"
