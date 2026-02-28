-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Accessibility Schema — WAI-ARIA 1.2 Primitives
-- |
-- | This module provides the complete atomic vocabulary for accessibility.
-- | All types are bounded and compose deterministically.
-- |
-- | ## Pillar: Accessibility
-- |
-- | Following the Schema architecture:
-- | - **Atoms**: Individual ARIA roles, states, properties
-- | - **Molecules**: LiveRegionConfig, composed patterns
-- | - **Compounds**: Full accessibility trees (future)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Accessibility as A11y
-- |
-- | -- Set role
-- | E.attr "role" (A11y.widgetRoleToString A11y.RoleButton)
-- |
-- | -- Set state
-- | E.attr "aria-expanded" (A11y.expandedToAttr (A11y.AriaExpanded true))
-- |
-- | -- Configure live region
-- | let config = A11y.statusRegion
-- | E.attr "aria-live" (A11y.politenessToString config.live)
-- | ```
-- |
-- | ## Reference
-- | https://www.w3.org/TR/wai-aria-1.2/
module Hydrogen.Schema.Accessibility
  ( -- * Role Module
    module Role
    -- * State Module
  , module State
    -- * Property Module
  , module Property
    -- * Live Region Module
  , module LiveRegion
    -- * Landmark Module
  , module Landmark
    -- * Molecules Module
  , module Molecules
  ) where

import Hydrogen.Schema.Accessibility.Role
  ( WidgetRole(..)
  , widgetRoleToString
  , CompositeRole(..)
  , compositeRoleToString
  , StructureRole(..)
  , structureRoleToString
  , WindowRole(..)
  , windowRoleToString
  ) as Role

import Hydrogen.Schema.Accessibility.State
  ( Tristate(..)
  , tristateToString
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
  ) as State

import Hydrogen.Schema.Accessibility.Property
  ( AriaLabelledBy(..)
  , AriaDescribedBy(..)
  , AriaControls(..)
  , AriaOwns(..)
  , AriaFlowTo(..)
  , AriaDetails(..)
  , AriaErrorMessage(..)
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
  , AriaLabel(..)
  , AriaPlaceholder(..)
  , AriaRoleDescription(..)
  ) as Property

import Hydrogen.Schema.Accessibility.LiveRegion
  ( Politeness(..)
  , politenessToString
  , AriaLive(..)
  , AriaAtomic(..)
  , AriaRelevant(..)
  , Relevance(..)
  , LiveRegionConfig
  , defaultLiveRegion
  , assertive
  , polite
  , statusRegion
  , alertRegion
  , logRegion
  ) as LiveRegion

import Hydrogen.Schema.Accessibility.Landmark
  ( LandmarkRole(..)
  , landmarkToString
  , landmarkFromString
  , isUniqueLandmark
  , requiresLabel
  ) as Landmark

import Hydrogen.Schema.Accessibility.Molecules
  ( DisclosureState
  , disclosureExpanded
  , disclosureCollapsed
  , SelectionState
  , singleSelect
  , multiSelect
  , RangeState
  , mkRange
  , normalizeRange
  , TabState
  , mkTabState
  , DialogState
  , modalDialog
  , nonModalDialog
  ) as Molecules
