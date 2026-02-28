-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Accessibility Molecules — Composed accessibility patterns
-- |
-- | Molecules combine atoms into cohesive accessibility patterns.
-- | These represent common widget accessibility requirements.
-- |
-- | ## Pattern Categories
-- | - Disclosure patterns (expandable content)
-- | - Selection patterns (single/multi select)
-- | - Range patterns (sliders, progress)
-- | - Navigation patterns (menus, tabs)
-- | - Modal patterns (dialogs, alerts)
module Hydrogen.Schema.Accessibility.Molecules
  ( -- * Disclosure Pattern
    DisclosureState(..)
  , disclosureExpanded
  , disclosureCollapsed
    -- * Selection Pattern
  , SelectionState(..)
  , singleSelect
  , multiSelect
    -- * Range Pattern
  , RangeState(..)
  , mkRange
  , normalizeRange
    -- * Tab Pattern
  , TabState(..)
  , mkTabState
    -- * Dialog Pattern
  , DialogState(..)
  , modalDialog
  , nonModalDialog
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // disclosure pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Disclosure state for expandable content (accordions, details, dropdowns).
-- |
-- | Combines aria-expanded with optional aria-controls.
type DisclosureState =
  { expanded :: Boolean
  , controlsId :: Maybe String
  }

-- | Create expanded disclosure state.
disclosureExpanded :: Maybe String -> DisclosureState
disclosureExpanded controlsId = { expanded: true, controlsId }

-- | Create collapsed disclosure state.
disclosureCollapsed :: Maybe String -> DisclosureState
disclosureCollapsed controlsId = { expanded: false, controlsId }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // selection pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection state for selectable items (listbox, tree, grid).
-- |
-- | Tracks selected state and multiselectable container flag.
type SelectionState =
  { selected :: Boolean
  , multiselectable :: Boolean
  , posInSet :: Maybe Int
  , setSize :: Maybe Int
  }

-- | Create single-select selection state.
singleSelect :: Boolean -> SelectionState
singleSelect selected =
  { selected
  , multiselectable: false
  , posInSet: Nothing
  , setSize: Nothing
  }

-- | Create multi-select selection state with position info.
multiSelect :: Boolean -> Int -> Int -> SelectionState
multiSelect selected pos size =
  { selected
  , multiselectable: true
  , posInSet: Just pos
  , setSize: Just size
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // range pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Range state for sliders, progress bars, spinbuttons.
-- |
-- | Combines aria-valuenow, aria-valuemin, aria-valuemax, aria-valuetext.
type RangeState =
  { valueNow :: Number
  , valueMin :: Number
  , valueMax :: Number
  , valueText :: Maybe String
  }

-- | Create a range state.
mkRange :: Number -> Number -> Number -> RangeState
mkRange minVal maxVal nowVal =
  { valueNow: nowVal
  , valueMin: minVal
  , valueMax: maxVal
  , valueText: Nothing
  }

-- | Normalize range value to 0-1.
normalizeRange :: RangeState -> Number
normalizeRange r =
  let range = r.valueMax - r.valueMin
  in if range == 0.0
     then 0.0
     else (r.valueNow - r.valueMin) / range

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // tab pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tab state for tablist/tab/tabpanel patterns.
-- |
-- | Tracks selection, position, and panel relationship.
type TabState =
  { selected :: Boolean
  , posInSet :: Int
  , setSize :: Int
  , controlsPanelId :: String
  }

-- | Create tab state.
mkTabState :: Boolean -> Int -> Int -> String -> TabState
mkTabState selected pos size panelId =
  { selected
  , posInSet: pos
  , setSize: size
  , controlsPanelId: panelId
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // dialog pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dialog state for modal and non-modal dialogs.
-- |
-- | Tracks modal state, labelledby, and describedby relationships.
type DialogState =
  { modal :: Boolean
  , labelledById :: Maybe String
  , describedById :: Maybe String
  }

-- | Create modal dialog state.
modalDialog :: Maybe String -> Maybe String -> DialogState
modalDialog labelId descId =
  { modal: true
  , labelledById: labelId
  , describedById: descId
  }

-- | Create non-modal dialog state.
nonModalDialog :: Maybe String -> Maybe String -> DialogState
nonModalDialog labelId descId =
  { modal: false
  , labelledById: labelId
  , describedById: descId
  }
