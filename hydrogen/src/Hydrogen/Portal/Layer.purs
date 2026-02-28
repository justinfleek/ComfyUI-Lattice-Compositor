-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // portal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Portal system for layered rendering — Pure Data
-- |
-- | Portals model **content that renders at a different layer** from its
-- | logical position in the component tree. This is pure data describing
-- | layering intent; the runtime interprets it for actual rendering.
-- |
-- | ## Pure Data Model
-- |
-- | Instead of imperative DOM manipulation, portals are described as:
-- |
-- | 1. **LayerLevel** — Which layer to render to (z-index tier)
-- | 2. **PortalContent** — What to render in the portal
-- | 3. **StackingContext** — The current state of all layers
-- |
-- | ```purescript
-- | import Hydrogen.Portal.Layer as Portal
-- |
-- | -- Define a modal that renders in the Modal layer
-- | myModal :: forall msg. Model -> Portal.PortalContent msg
-- | myModal model =
-- |   Portal.portalContent
-- |     { level: Portal.Modal
-- |     , key: "my-modal"
-- |     , trapFocus: true
-- |     , ariaLabel: Just "Confirmation dialog"
-- |     }
-- |     [ modalContent model ]
-- |
-- | -- In your view, portals are collected at the top level
-- | view :: Model -> Element msg
-- | view model = 
-- |   Portal.withPortals
-- |     [ when model.showModal (myModal model) ]
-- |     (mainContent model)
-- | ```
module Hydrogen.Portal.Layer
  ( -- * Layer Levels (Pure Data)
    LayerLevel(..)
  , layerZIndex
  , compareLayerLevel
    -- * Portal Content (Pure Data)
  , PortalContent
  , PortalKey
  , portalContent
  , emptyPortal
    -- * Portal Configuration (Pure Data)
  , PortalConfig
  , defaultPortalConfig
  , withAriaLabel
  , withClassName
  , withTrapFocus
    -- * Stacking Context (Pure Data)
  , StackingContext
  , StackedLayer
  , emptyStackingContext
  , addLayer
  , removeLayer
  , getTopLayer
  , getAllLayers
  , isTopLayer
    -- * Focus State (Pure Data)
  , FocusState
  , FocusTrap
  , defaultFocusState
  , createFocusTrap
  , releaseFocusTrap
  , focusedLayerKey
    -- * Portal Operations (Pure Functions)
  , collectPortals
  , mergePortals
  , sortByLevel
  , filterByLevel
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // layer levels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Predefined layer levels — pure enum
-- |
-- | Each level maps to a z-index tier. Content at higher levels
-- | renders above content at lower levels.
data LayerLevel
  = Base        -- ^ z-index: 0 - Normal document flow
  | Dropdown    -- ^ z-index: 1000 - Dropdowns, select menus
  | Sticky      -- ^ z-index: 1100 - Sticky headers, fixed elements
  | Popover     -- ^ z-index: 1200 - Popovers, context menus
  | Modal       -- ^ z-index: 1300 - Modal dialogs
  | Toast       -- ^ z-index: 1400 - Toast notifications
  | Tooltip     -- ^ z-index: 1500 - Tooltips (highest standard)
  | Overlay     -- ^ z-index: 1600 - Full-screen overlays
  | Custom Int  -- ^ Custom z-index value

derive instance eqLayerLevel :: Eq LayerLevel

instance ordLayerLevel :: Ord LayerLevel where
  compare a b = compare (layerZIndex a) (layerZIndex b)

instance showLayerLevel :: Show LayerLevel where
  show Base = "Base"
  show Dropdown = "Dropdown"
  show Sticky = "Sticky"
  show Popover = "Popover"
  show Modal = "Modal"
  show Toast = "Toast"
  show Tooltip = "Tooltip"
  show Overlay = "Overlay"
  show (Custom n) = "Custom " <> show n

-- | Get the z-index for a layer level — pure function
layerZIndex :: LayerLevel -> Int
layerZIndex = case _ of
  Base -> 0
  Dropdown -> 1000
  Sticky -> 1100
  Popover -> 1200
  Modal -> 1300
  Toast -> 1400
  Tooltip -> 1500
  Overlay -> 1600
  Custom n -> n

-- | Compare two layer levels — pure function
compareLayerLevel :: LayerLevel -> LayerLevel -> Ordering
compareLayerLevel = compare

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // portal content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Portal key for identity tracking
type PortalKey = String

-- | Portal configuration — pure data
type PortalConfig =
  { level :: LayerLevel
  , key :: PortalKey
  , className :: Maybe String
  , ariaLabel :: Maybe String
  , ariaModal :: Boolean
  , trapFocus :: Boolean
  , closeOnEscape :: Boolean
  , closeOnBackdropClick :: Boolean
  }

-- | Default portal configuration
defaultPortalConfig :: PortalConfig
defaultPortalConfig =
  { level: Modal
  , key: ""
  , className: Nothing
  , ariaLabel: Nothing
  , ariaModal: false
  , trapFocus: false
  , closeOnEscape: false
  , closeOnBackdropClick: false
  }

-- | Add aria-label to config — pure function
withAriaLabel :: String -> PortalConfig -> PortalConfig
withAriaLabel label config = config { ariaLabel = Just label }

-- | Add className to config — pure function
withClassName :: String -> PortalConfig -> PortalConfig
withClassName cls config = config { className = Just cls }

-- | Enable focus trap — pure function
withTrapFocus :: PortalConfig -> PortalConfig
withTrapFocus config = config { trapFocus = true }

-- | Portal content — pure data describing what to render in a portal
-- |
-- | The `msg` type parameter allows specifying callback messages.
type PortalContent msg =
  { config :: PortalConfig
  , children :: Array msg    -- Placeholder for Element msg in real impl
  , visible :: Boolean
  }

-- | Create portal content — pure function
portalContent 
  :: forall msg
   . PortalConfig 
  -> Array msg 
  -> PortalContent msg
portalContent config children =
  { config
  , children
  , visible: true
  }

-- | Empty portal (not rendered)
emptyPortal :: forall msg. PortalContent msg
emptyPortal =
  { config: defaultPortalConfig
  , children: []
  , visible: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // stacking context
-- ═════════════════════════════════════════════════════════════════════════════

-- | A layer in the stacking context — pure data
type StackedLayer =
  { key :: PortalKey
  , level :: LayerLevel
  , zIndex :: Int
  , hasFocusTrap :: Boolean
  , order :: Int          -- Order within same level
  }

-- | Stacking context — pure data representing all active layers
-- |
-- | This is computed from all active portals and passed through
-- | the application state.
type StackingContext =
  { layers :: Array StackedLayer
  , topLayerKey :: Maybe PortalKey
  , nextOrder :: Int
  }

-- | Empty stacking context
emptyStackingContext :: StackingContext
emptyStackingContext =
  { layers: []
  , topLayerKey: Nothing
  , nextOrder: 0
  }

-- | Add a layer to the stacking context — pure function
addLayer :: PortalConfig -> StackingContext -> StackingContext
addLayer config ctx =
  let
    newLayer =
      { key: config.key
      , level: config.level
      , zIndex: layerZIndex config.level
      , hasFocusTrap: config.trapFocus
      , order: ctx.nextOrder
      }
    newLayers = Array.snoc ctx.layers newLayer
    sortedLayers = sortByZIndexAndOrder newLayers
    topKey = case Array.last sortedLayers of
      Just l -> Just l.key
      Nothing -> Nothing
  in
    ctx
      { layers = sortedLayers
      , topLayerKey = topKey
      , nextOrder = ctx.nextOrder + 1
      }

-- | Remove a layer from the stacking context — pure function
removeLayer :: PortalKey -> StackingContext -> StackingContext
removeLayer key ctx =
  let
    newLayers = Array.filter (\l -> l.key /= key) ctx.layers
    topKey = case Array.last newLayers of
      Just l -> Just l.key
      Nothing -> Nothing
  in
    ctx { layers = newLayers, topLayerKey = topKey }

-- | Get the top layer — pure function
getTopLayer :: StackingContext -> Maybe StackedLayer
getTopLayer ctx = Array.last ctx.layers

-- | Get all layers — pure function
getAllLayers :: StackingContext -> Array StackedLayer
getAllLayers = _.layers

-- | Check if a layer is the top layer — pure function
isTopLayer :: PortalKey -> StackingContext -> Boolean
isTopLayer key ctx = ctx.topLayerKey == Just key

-- | Sort layers by z-index and order — pure function
sortByZIndexAndOrder :: Array StackedLayer -> Array StackedLayer
sortByZIndexAndOrder = Array.sortBy compareLayers
  where
  compareLayers a b =
    case compare a.zIndex b.zIndex of
      EQ -> compare a.order b.order
      other -> other

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // focus state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focus trap — pure data describing a focus trap
type FocusTrap =
  { layerKey :: PortalKey
  , previousFocusKey :: Maybe String   -- Element to restore focus to
  }

-- | Focus state — pure data tracking focus traps
type FocusState =
  { activeTraps :: Array FocusTrap
  , focusedLayerKey :: Maybe PortalKey
  }

-- | Default focus state
defaultFocusState :: FocusState
defaultFocusState =
  { activeTraps: []
  , focusedLayerKey: Nothing
  }

-- | Create a focus trap — pure function
createFocusTrap :: PortalKey -> Maybe String -> FocusState -> FocusState
createFocusTrap layerKey previousFocus state =
  let
    trap = { layerKey, previousFocusKey: previousFocus }
  in
    state
      { activeTraps = Array.snoc state.activeTraps trap
      , focusedLayerKey = Just layerKey
      }

-- | Release a focus trap — pure function
releaseFocusTrap :: PortalKey -> FocusState -> FocusState
releaseFocusTrap key state =
  let
    newTraps = Array.filter (\t -> t.layerKey /= key) state.activeTraps
    newFocusedKey = case Array.last newTraps of
      Just t -> Just t.layerKey
      Nothing -> Nothing
  in
    state { activeTraps = newTraps, focusedLayerKey = newFocusedKey }

-- | Get the currently focused layer key — pure function
focusedLayerKey :: FocusState -> Maybe PortalKey
focusedLayerKey = _.focusedLayerKey

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // portal operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collect all visible portals — pure function
collectPortals :: forall msg. Array (PortalContent msg) -> Array (PortalContent msg)
collectPortals = Array.filter _.visible

-- | Merge multiple portal arrays — pure function
mergePortals :: forall msg. Array (Array (PortalContent msg)) -> Array (PortalContent msg)
mergePortals = foldl (<>) []

-- | Sort portals by layer level — pure function
sortByLevel :: forall msg. Array (PortalContent msg) -> Array (PortalContent msg)
sortByLevel = Array.sortBy comparePortals
  where
  comparePortals a b = compare a.config.level b.config.level

-- | Filter portals by level — pure function
filterByLevel :: forall msg. LayerLevel -> Array (PortalContent msg) -> Array (PortalContent msg)
filterByLevel level = Array.filter (\p -> p.config.level == level)
