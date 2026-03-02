-- | Properties Panel Component
-- |
-- | The main properties panel that shows properties for the selected layer.
-- | Displays different property sections based on layer type.
module Lattice.UI.Components.PropertiesPanel
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Type.Proxy (Proxy(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls, textMuted)
import Lattice.UI.Components.TransformProperties as TransformProperties
import Lattice.Project (LayerBase, LayerType(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { selectedLayer :: Maybe LayerBase
  }

data Output
  = LayerUpdated LayerBase

data Query a

type Slot id = H.Slot Query Output id

type State =
  { selectedLayer :: Maybe LayerBase
  , activeTab :: PropertyTab
  }

data PropertyTab
  = TabTransform
  | TabEffects
  | TabMasks
  | TabLayerStyles

derive instance eqPropertyTab :: Eq PropertyTab

data Action
  = Initialize
  | Receive Input
  | SetTab PropertyTab
  | HandleTransformChange TransformProperties.Output

type Slots =
  ( transform :: TransformProperties.Slot Unit
  )

_transform :: Proxy "transform"
_transform = Proxy

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
  { selectedLayer: input.selectedLayer
  , activeTab: TabTransform
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-properties-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    ]
    [ renderHeader state
    , renderContent state
    ]

renderHeader :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "lattice-properties-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.span [ cls [ "lattice-properties-title" ] ]
        [ HH.text $ case state.selectedLayer of
            Just layer -> show layer.name <> " - " <> layerTypeName layer.layerType
            Nothing -> "Properties"
        ]
    ]

renderContent :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderContent state =
  case state.selectedLayer of
    Nothing -> renderEmptyState
    Just layer -> renderLayerProperties state layer

renderEmptyState :: forall m. MonadAff m => H.ComponentHTML Action Slots m
renderEmptyState =
  HH.div
    [ cls [ "lattice-properties-empty" ]
    , HP.attr (HH.AttrName "style") emptyStyle
    ]
    [ textMuted "Select a layer to view properties" ]

renderLayerProperties :: forall m. MonadAff m => State -> LayerBase -> H.ComponentHTML Action Slots m
renderLayerProperties state layer =
  HH.div
    [ cls [ "lattice-properties-content" ]
    , HP.attr (HH.AttrName "style") contentStyle
    ]
    [ -- Tab bar
      renderTabBar state
    
      -- Tab content
    , renderTabContent state layer
    ]

renderTabBar :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderTabBar state =
  HH.div
    [ cls [ "lattice-properties-tabs" ]
    , HP.attr (HH.AttrName "style") tabBarStyle
    ]
    [ tabButton "Transform" TabTransform state.activeTab
    , tabButton "Effects" TabEffects state.activeTab
    , tabButton "Masks" TabMasks state.activeTab
    , tabButton "Styles" TabLayerStyles state.activeTab
    ]

tabButton :: forall m. String -> PropertyTab -> PropertyTab -> H.ComponentHTML Action Slots m
tabButton label tab activeTab =
  HH.button
    [ cls [ "lattice-properties-tab" ]
    , HP.attr (HH.AttrName "style") (tabStyle (tab == activeTab))
    , HP.attr (HH.AttrName "data-state") (if tab == activeTab then "active" else "inactive")
    ]
    [ HH.text label ]

renderTabContent :: forall m. MonadAff m => State -> LayerBase -> H.ComponentHTML Action Slots m
renderTabContent state layer =
  HH.div
    [ cls [ "lattice-properties-tab-content" ]
    , HP.attr (HH.AttrName "style") tabContentStyle
    ]
    [ case state.activeTab of
        TabTransform -> renderTransformTab layer
        TabEffects -> renderEffectsTab layer
        TabMasks -> renderMasksTab layer
        TabLayerStyles -> renderStylesTab layer
    ]

renderTransformTab :: forall m. MonadAff m => LayerBase -> H.ComponentHTML Action Slots m
renderTransformTab layer =
  HH.slot _transform unit TransformProperties.component
    { transform: defaultTransform
    , is3D: layer.is3D
    , layerId: show layer.id
    }
    HandleTransformChange

renderEffectsTab :: forall m. MonadAff m => LayerBase -> H.ComponentHTML Action Slots m
renderEffectsTab _layer =
  HH.div [ cls [ "lattice-effects-list" ] ]
    [ HH.p [ cls [ "lattice-text-muted" ] ]
        [ HH.text "No effects applied" ]
    , HH.button [ cls [ "lattice-btn lattice-btn-ghost" ] ]
        [ HH.text "+ Add Effect" ]
    ]

renderMasksTab :: forall m. MonadAff m => LayerBase -> H.ComponentHTML Action Slots m
renderMasksTab _layer =
  HH.div [ cls [ "lattice-masks-list" ] ]
    [ HH.p [ cls [ "lattice-text-muted" ] ]
        [ HH.text "No masks" ]
    , HH.button [ cls [ "lattice-btn lattice-btn-ghost" ] ]
        [ HH.text "+ Add Mask" ]
    ]

renderStylesTab :: forall m. MonadAff m => LayerBase -> H.ComponentHTML Action Slots m
renderStylesTab _layer =
  HH.div [ cls [ "lattice-styles-list" ] ]
    [ HH.p [ cls [ "lattice-text-muted" ] ]
        [ HH.text "No layer styles" ]
    , HH.button [ cls [ "lattice-btn lattice-btn-ghost" ] ]
        [ HH.text "+ Add Style" ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

layerTypeName :: LayerType -> String
layerTypeName = case _ of
  LTImage -> "Image"
  LTVideo -> "Video"
  LTSolid -> "Solid"
  LTText -> "Text"
  LTShape -> "Shape"
  LTNull -> "Null"
  LTCamera -> "Camera"
  LTLight -> "Light"
  LTAudio -> "Audio"
  LTParticle -> "Particle"
  LTAdjustment -> "Adjustment"
  LTPreComp -> "Pre-comp"
  LTGroup -> "Group"
  LTNestedComp -> "Nested Comp"
  LTDepth -> "Depth"
  LTNormal -> "Normal"
  LTGenerated -> "Generated"
  LTMatte -> "Matte"
  LTControl -> "Control"
  LTSpline -> "Spline"
  LTPath -> "Path"
  LTPose -> "Pose"
  LTEffect -> "Effect"
  LTModel -> "3D Model"
  LTPointCloud -> "Point Cloud"
  LTDepthflow -> "Depthflow"

defaultTransform :: TransformProperties.Transform
defaultTransform =
  { positionX: 960.0
  , positionY: 540.0
  , positionZ: 0.0
  , scaleX: 1.0
  , scaleY: 1.0
  , scaleZ: 1.0
  , rotation: 0.0
  , rotationX: 0.0
  , rotationY: 0.0
  , rotationZ: 0.0
  , anchorX: 960.0
  , anchorY: 540.0
  , anchorZ: 0.0
  , opacity: 100.0
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // inline // styles
-- ════════════════════════════════════════════════════════════════════════════

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1);"

headerStyle :: String
headerStyle =
  "padding: var(--lattice-space-3); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle); " <>
  "font-weight: var(--lattice-font-semibold);"

emptyStyle :: String
emptyStyle =
  "display: flex; align-items: center; justify-content: center; " <>
  "height: 100%; text-align: center; padding: var(--lattice-space-8);"

contentStyle :: String
contentStyle =
  "display: flex; flex-direction: column; flex: 1; overflow: hidden;"

tabBarStyle :: String
tabBarStyle =
  "display: flex; gap: var(--lattice-space-1); " <>
  "padding: var(--lattice-space-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

tabStyle :: Boolean -> String
tabStyle active =
  "padding: var(--lattice-space-1) var(--lattice-space-2); " <>
  "font-size: var(--lattice-text-xs); " <>
  "border-radius: var(--lattice-radius-sm); " <>
  "background: " <> (if active then "var(--lattice-accent-muted)" else "transparent") <> "; " <>
  "color: " <> (if active then "var(--lattice-text-primary)" else "var(--lattice-text-secondary)") <> "; " <>
  "border: none; cursor: pointer;"

tabContentStyle :: String
tabContentStyle =
  "flex: 1; overflow-y: auto; padding: var(--lattice-space-3);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ { selectedLayer = input.selectedLayer }
  
  SetTab tab -> do
    H.modify_ _ { activeTab = tab }
  
  HandleTransformChange (TransformProperties.TransformChanged _layerId _transform) -> do
    -- In a real implementation, we'd update the layer and raise an event
    pure unit
