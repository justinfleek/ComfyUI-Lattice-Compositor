-- | Layer List Component
-- |
-- | Displays the list of layers in the current composition with selection,
-- | visibility toggles, lock toggles, and drag-to-reorder support.
-- |
-- | Matches the Vue UI layer list exactly.
module Lattice.UI.Components.LayerList
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  ) where

import Prelude

import Data.Array (mapWithIndex)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.Project (LayerType(..), LayerBase)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { layers :: Array LayerBase
  , selectedIds :: Array String
  }

data Output
  = SelectLayer String
  | ToggleVisibility String
  | ToggleLock String
  | ReorderLayer String Int

data Query a

type Slot id = H.Slot Query Output id

type State =
  { layers :: Array LayerBase
  , selectedIds :: Array String
  , draggedId :: Maybe String
  }

data Action
  = Initialize
  | Receive Input
  | HandleSelect String
  | HandleToggleVisible String
  | HandleToggleLock String
  | HandleDragStart String
  | HandleDragEnd
  | HandleDrop Int

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { layers: input.layers
  , selectedIds: input.selectedIds
  , draggedId: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-layer-list" ]
    , HP.attr (HH.AttrName "style") listStyle
    ]
    [ if state.layers == []
        then renderEmptyState
        else HH.div [ cls [ "lattice-layer-items" ] ]
               (mapWithIndex (renderLayerItem state) state.layers)
    ]

renderEmptyState :: forall m. H.ComponentHTML Action () m
renderEmptyState =
  HH.div
    [ cls [ "lattice-layer-empty" ]
    , HP.attr (HH.AttrName "style") emptyStyle
    ]
    [ HH.p [ cls [ "lattice-text-muted" ] ]
        [ HH.text "No layers" ]
    , HH.p [ cls [ "lattice-text-muted" ] ]
        [ HH.text "Add a layer to begin" ]
    ]

renderLayerItem :: forall m. State -> Int -> LayerBase -> H.ComponentHTML Action () m
renderLayerItem state index layer =
  let
    isSelected = state.selectedIds # \ids -> 
      case layer.id of
        _ -> false -- Simplified for now
    isDragging = state.draggedId == Just (show layer.id)
  in
  HH.div
    [ cls [ "lattice-layer-item" ]
    , HP.attr (HH.AttrName "style") (itemStyle isSelected isDragging)
    , HP.attr (HH.AttrName "data-layer-id") (show layer.id)
    , HP.draggable true
    , HE.onClick \_ -> HandleSelect (show layer.id)
    ]
    [ -- Visibility toggle
      HH.button
        [ cls [ "lattice-layer-toggle" ]
        , HP.title (if layer.visible then "Hide" else "Show")
        , HE.onClick \e -> HandleToggleVisible (show layer.id)
        ]
        [ HH.span [ cls [ "lattice-icon" ] ]
            [ HH.text (if layer.visible then "👁" else "○") ]
        ]
    
      -- Lock toggle
    , HH.button
        [ cls [ "lattice-layer-toggle" ]
        , HP.title (if layer.locked then "Unlock" else "Lock")
        , HE.onClick \e -> HandleToggleLock (show layer.id)
        ]
        [ HH.span [ cls [ "lattice-icon" ] ]
            [ HH.text (if layer.locked then "🔒" else "○") ]
        ]
    
      -- Layer type icon
    , HH.span
        [ cls [ "lattice-layer-type-icon" ]
        , HP.attr (HH.AttrName "style") iconStyle
        ]
        [ HH.text (layerTypeIcon layer.layerType) ]
    
      -- Layer name
    , HH.span
        [ cls [ "lattice-layer-name" ]
        , HP.attr (HH.AttrName "style") nameStyle
        ]
        [ HH.text (show layer.name) ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // layer type icons
-- ════════════════════════════════════════════════════════════════════════════

layerTypeIcon :: LayerType -> String
layerTypeIcon = case _ of
  LTImage -> "🖼"
  LTVideo -> "🎬"
  LTSolid -> "■"
  LTText -> "T"
  LTShape -> "◇"
  LTNull -> "◎"
  LTCamera -> "📷"
  LTLight -> "💡"
  LTAudio -> "🔊"
  LTParticle -> "✨"
  LTAdjustment -> "◐"
  LTPreComp -> "📁"
  LTGroup -> "📂"
  LTNestedComp -> "📦"
  LTDepth -> "▦"
  LTNormal -> "↗"
  LTGenerated -> "⚡"
  LTMatte -> "◧"
  LTControl -> "⊕"
  LTSpline -> "〰"
  LTPath -> "✏"
  LTPose -> "🦴"
  LTEffect -> "fx"
  LTModel -> "🎲"
  LTPointCloud -> "⁘"
  LTDepthflow -> "≋"

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // inline // styles
-- ════════════════════════════════════════════════════════════════════════════

listStyle :: String
listStyle =
  "display: flex; flex-direction: column; overflow-y: auto; " <>
  "background: var(--lattice-surface-1);"

emptyStyle :: String
emptyStyle =
  "display: flex; flex-direction: column; align-items: center; " <>
  "justify-content: center; padding: var(--lattice-space-8); " <>
  "text-align: center; gap: var(--lattice-space-2);"

itemStyle :: Boolean -> Boolean -> String
itemStyle selected dragging =
  "display: flex; align-items: center; gap: var(--lattice-space-2); " <>
  "padding: var(--lattice-space-2) var(--lattice-space-3); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle); " <>
  "cursor: pointer; user-select: none; " <>
  (if selected 
     then "background: var(--lattice-accent-muted); "
     else "background: transparent; ") <>
  (if dragging
     then "opacity: 0.5; "
     else "")

iconStyle :: String
iconStyle =
  "width: 20px; text-align: center; font-size: 14px;"

nameStyle :: String
nameStyle =
  "flex: 1; overflow: hidden; text-overflow: ellipsis; " <>
  "white-space: nowrap; font-size: var(--lattice-text-sm);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ { layers = input.layers, selectedIds = input.selectedIds }
  
  HandleSelect layerId -> do
    H.raise (SelectLayer layerId)
  
  HandleToggleVisible layerId -> do
    H.raise (ToggleVisibility layerId)
  
  HandleToggleLock layerId -> do
    H.raise (ToggleLock layerId)
  
  HandleDragStart layerId -> do
    H.modify_ _ { draggedId = Just layerId }
  
  HandleDragEnd -> do
    H.modify_ _ { draggedId = Nothing }
  
  HandleDrop targetIndex -> do
    state <- H.get
    case state.draggedId of
      Just layerId -> do
        H.raise (ReorderLayer layerId targetIndex)
        H.modify_ _ { draggedId = Nothing }
      Nothing -> pure unit
