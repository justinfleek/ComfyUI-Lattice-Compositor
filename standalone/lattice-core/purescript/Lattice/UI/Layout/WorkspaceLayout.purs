-- | Workspace Layout Component
-- |
-- | The main workspace layout for the Lattice Compositor.
-- | This matches the Vue UI layout exactly:
-- |
-- | ┌─────────────────────────────────────────────────────────┐
-- | │ MenuBar (28px)                                          │
-- | ├─────────────────────────────────────────────────────────┤
-- | │ Toolbar (54px)                                          │
-- | ├────────┬───────────────────────────────────────┬───────────────┤
-- | │        │                               │               │
-- | │  Left  │       Center Viewport         │    Right      │
-- | │ Sidebar│       (Canvas + Timeline)     │   Sidebar     │
-- | │ (14%)  │           (66%)               │    (20%)      │
-- | │        │                               │               │
-- | └────────┴───────────────────────────────┴───────────────┘
module Lattice.UI.Layout.WorkspaceLayout
  ( component
  , Input
  , Output
  , Query
  , Slot
  ) where

import Prelude

import Data.Const (Const)
import Data.Maybe (Maybe(..))
import Type.Proxy (Proxy(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.UI.Components.LayerList as LayerList
import Lattice.UI.Components.Timeline as Timeline
import Lattice.UI.Components.PropertiesPanel as PropertiesPanel
import Lattice.Project (LayerBase)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input = Unit

type Output = Void

data Query a

type Slot id = H.Slot Query Output id

type State =
  { leftSidebarWidth :: Number  -- Percentage (default 14%)
  , rightSidebarWidth :: Number -- Percentage (default 20%)
  , timelineHeight :: Number    -- Percentage (default 35%)
  , layers :: Array LayerBase
  , selectedLayerIds :: Array String
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Number
  , isPlaying :: Boolean
  , activeLeftTab :: LeftTab
  }

data LeftTab = TabProject | TabEffects | TabAssets
derive instance eqLeftTab :: Eq LeftTab

data Action
  = Initialize
  | SetLeftTab LeftTab
  | HandleLayerList LayerList.Output
  | HandleTimeline Timeline.Output
  | HandleProperties PropertiesPanel.Output

type Slots =
  ( menuBar :: H.Slot (Const Void) Void Unit
  , toolbar :: H.Slot (Const Void) Void Unit
  , leftSidebar :: H.Slot (Const Void) Void Unit
  , viewport :: H.Slot (Const Void) Void Unit
  , timeline :: Timeline.Slot Unit
  , rightSidebar :: H.Slot (Const Void) Void Unit
  , layerList :: LayerList.Slot Unit
  , properties :: PropertiesPanel.Slot Unit
  )

_menuBar :: Proxy "menuBar"
_menuBar = Proxy

_toolbar :: Proxy "toolbar"
_toolbar = Proxy

_leftSidebar :: Proxy "leftSidebar"
_leftSidebar = Proxy

_viewport :: Proxy "viewport"
_viewport = Proxy

_timeline :: Proxy "timeline"
_timeline = Proxy

_rightSidebar :: Proxy "rightSidebar"
_rightSidebar = Proxy

_layerList :: Proxy "layerList"
_layerList = Proxy

_properties :: Proxy "properties"
_properties = Proxy

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q i o m. MonadAff m => H.Component q i o m
component = H.mkComponent
  { initialState: const initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

initialState :: State
initialState =
  { leftSidebarWidth: 14.0
  , rightSidebarWidth: 20.0
  , timelineHeight: 35.0
  , layers: []
  , selectedLayerIds: []
  , currentFrame: 0
  , totalFrames: 81
  , fps: 16.0
  , isPlaying: false
  , activeLeftTab: TabProject
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-workspace" ]
    , HP.attr (HH.AttrName "style") workspaceStyle
    ]
    [ -- Menu Bar
      renderMenuBar
    
      -- Toolbar
    , renderToolbar
    
      -- Main content area (3-column split)
    , HH.div
        [ cls [ "lattice-workspace-content" ]
        , HP.attr (HH.AttrName "style") contentStyle
        ]
        [ -- Left Sidebar
          HH.div
            [ cls [ "lattice-sidebar lattice-sidebar-left" ]
            , HP.attr (HH.AttrName "style") (sidebarStyle state.leftSidebarWidth)
            ]
            [ renderLeftSidebar state ]
        
          -- Center (Viewport + Timeline)
        , HH.div
            [ cls [ "lattice-center" ]
            , HP.attr (HH.AttrName "style") centerStyle
            ]
            [ -- Viewport
              HH.div
                [ cls [ "lattice-viewport" ]
                , HP.attr (HH.AttrName "style") (viewportStyle state.timelineHeight)
                ]
                [ renderViewport ]
            
              -- Timeline
            , HH.div
                [ cls [ "lattice-timeline-container" ]
                , HP.attr (HH.AttrName "style") (timelineStyle state.timelineHeight)
                ]
                [ renderTimeline state ]
            ]
        
          -- Right Sidebar
        , HH.div
            [ cls [ "lattice-sidebar lattice-sidebar-right" ]
            , HP.attr (HH.AttrName "style") (sidebarStyle state.rightSidebarWidth)
            ]
            [ renderRightSidebar state ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                       // sub
-- ════════════════════════════════════════════════════════════════════════════

renderMenuBar :: forall m. H.ComponentHTML Action Slots m
renderMenuBar =
  HH.div
    [ cls [ "lattice-menubar" ]
    , HP.attr (HH.AttrName "style") menuBarStyle
    ]
    [ HH.div [ cls [ "lattice-menubar-left" ] ]
        [ menuItem "File"
        , menuItem "Edit"
        , menuItem "View"
        , menuItem "Insert"
        , menuItem "Layer"
        , menuItem "Animation"
        , menuItem "Effects"
        , menuItem "Window"
        , menuItem "Help"
        ]
    , HH.div [ cls [ "lattice-menubar-right" ] ]
        [ HH.span [ cls [ "lattice-project-name" ] ] 
            [ HH.text "Untitled Project" ]
        ]
    ]

menuItem :: forall m. String -> H.ComponentHTML Action Slots m
menuItem label =
  HH.button
    [ cls [ "lattice-menu-trigger" ] ]
    [ HH.text label ]

renderToolbar :: forall m. H.ComponentHTML Action Slots m
renderToolbar =
  HH.div
    [ cls [ "lattice-toolbar" ]
    , HP.attr (HH.AttrName "style") toolbarStyle
    ]
    [ -- Tool group: Selection
      HH.div [ cls [ "lattice-tool-group" ] ]
        [ toolButton "select" "Selection Tool" true
        , toolButton "hand" "Pan Tool" false
        , toolButton "zoom" "Zoom Tool" false
        ]
    
      -- Tool group: Transform
    , HH.div [ cls [ "lattice-tool-group" ] ]
        [ toolButton "move" "Move" false
        , toolButton "rotate" "Rotate" false
        , toolButton "scale" "Scale" false
        ]
    
      -- Tool group: Create
    , HH.div [ cls [ "lattice-tool-group" ] ]
        [ toolButton "pen" "Pen Tool" false
        , toolButton "rectangle" "Rectangle" false
        , toolButton "ellipse" "Ellipse" false
        , toolButton "text" "Text Tool" false
        ]
    
      -- Spacer
    , HH.div [ cls [ "lattice-toolbar-spacer" ] ] []
    
      -- Playback controls
    , HH.div [ cls [ "lattice-tool-group lattice-playback" ] ]
        [ toolButton "skip-back" "Go to Start" false
        , toolButton "step-back" "Previous Frame" false
        , toolButton "play" "Play/Pause" false
        , toolButton "step-forward" "Next Frame" false
        , toolButton "skip-forward" "Go to End" false
        ]
    
      -- Time display
    , HH.div [ cls [ "lattice-time-display" ] ]
        [ HH.span_ [ HH.text "00:00:00:00" ] ]
    ]

toolButton :: forall m. String -> String -> Boolean -> H.ComponentHTML Action Slots m
toolButton iconName tooltip active =
  HH.button
    [ cls [ "lattice-tool-btn" ]
    , HP.title tooltip
    , HP.attr (HH.AttrName "data-state") (if active then "active" else "inactive")
    ]
    [ HH.span 
        [ cls [ "lattice-icon" ]
        , HP.attr (HH.AttrName "data-icon") iconName
        ] 
        [] -- Icon rendered via CSS data-icon attribute
    ]

renderLeftSidebar :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderLeftSidebar state =
  HH.div [ cls [ "lattice-sidebar-content" ] ]
    [ -- Tabs: Project / Effects / Assets
      HH.div [ cls [ "lattice-sidebar-tabs" ] ]
        [ HH.button 
            [ cls [ "lattice-tabs-trigger" ]
            , HP.attr (HH.AttrName "data-state") (if state.activeLeftTab == TabProject then "active" else "inactive")
            , HE.onClick \_ -> SetLeftTab TabProject
            ]
            [ HH.text "Project" ]
        , HH.button 
            [ cls [ "lattice-tabs-trigger" ]
            , HP.attr (HH.AttrName "data-state") (if state.activeLeftTab == TabEffects then "active" else "inactive")
            , HE.onClick \_ -> SetLeftTab TabEffects
            ]
            [ HH.text "Effects" ]
        , HH.button 
            [ cls [ "lattice-tabs-trigger" ]
            , HP.attr (HH.AttrName "data-state") (if state.activeLeftTab == TabAssets then "active" else "inactive")
            , HE.onClick \_ -> SetLeftTab TabAssets
            ]
            [ HH.text "Assets" ]
        ]
    
      -- Tab content
    , case state.activeLeftTab of
        TabProject -> renderProjectTab state
        TabEffects -> renderEffectsTab
        TabAssets -> renderAssetsTab
    ]

renderProjectTab :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderProjectTab state =
  HH.div [ cls [ "lattice-sidebar-panel" ] ]
    [ HH.div [ cls [ "lattice-panel-header" ] ]
        [ HH.text "Layers" ]
    , HH.slot _layerList unit LayerList.component
        { layers: state.layers
        , selectedIds: state.selectedLayerIds
        }
        HandleLayerList
    ]

renderEffectsTab :: forall m. H.ComponentHTML Action Slots m
renderEffectsTab =
  HH.div [ cls [ "lattice-sidebar-panel" ] ]
    [ HH.div [ cls [ "lattice-panel-header" ] ]
        [ HH.text "Effects" ]
    , HH.div [ cls [ "lattice-panel-content" ] ]
        [ HH.p [ cls [ "lattice-text-muted" ] ] 
            [ HH.text "Select a layer to view effects" ]
        ]
    ]

renderAssetsTab :: forall m. H.ComponentHTML Action Slots m
renderAssetsTab =
  HH.div [ cls [ "lattice-sidebar-panel" ] ]
    [ HH.div [ cls [ "lattice-panel-header" ] ]
        [ HH.text "Assets" ]
    , HH.div [ cls [ "lattice-panel-content" ] ]
        [ HH.p [ cls [ "lattice-text-muted" ] ] 
            [ HH.text "No assets imported" ]
        , HH.button [ cls [ "lattice-btn lattice-btn-primary" ] ]
            [ HH.text "+ Import" ]
        ]
    ]

renderViewport :: forall m. H.ComponentHTML Action Slots m
renderViewport =
  HH.div [ cls [ "lattice-viewport-content" ] ]
    [ -- Viewport tabs
      HH.div [ cls [ "lattice-viewport-tabs" ] ]
        [ tabButton "Composition" true
        , tabButton "Layer" false
        , tabButton "Footage" false
        ]
    
      -- Canvas area
    , HH.div 
        [ cls [ "lattice-canvas-container" ]
        , HP.id "lattice-canvas"
        ]
        [ -- WebGL canvas mount point - canvas is created programmatically
          HH.div [ cls [ "lattice-canvas-placeholder" ] ]
            [ HH.text "Canvas" ]
        ]
    ]

renderTimeline :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderTimeline state =
  HH.slot _timeline unit Timeline.component
    { layers: state.layers
    , currentFrame: state.currentFrame
    , totalFrames: state.totalFrames
    , fps: state.fps
    , selectedLayerIds: state.selectedLayerIds
    , isPlaying: state.isPlaying
    }
    HandleTimeline

renderRightSidebar :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderRightSidebar state =
  HH.div [ cls [ "lattice-sidebar-content" ] ]
    [ -- Properties panel
      HH.slot _properties unit PropertiesPanel.component
        { selectedLayer: getSelectedLayer state }
        HandleProperties
    
      -- AI section
    , HH.div [ cls [ "lattice-ai-section" ] ]
        [ HH.div [ cls [ "lattice-sidebar-tabs" ] ]
            [ tabButton "Chat" true
            , tabButton "Generate" false
            , tabButton "Flow" false
            ]
        , HH.div [ cls [ "lattice-ai-content" ] ]
            [ HH.p [ cls [ "lattice-text-muted" ] ]
                [ HH.text "AI assistant ready" ]
            ]
        ]
    ]

getSelectedLayer :: State -> Maybe LayerBase
getSelectedLayer state =
  case state.selectedLayerIds of
    [layerId] -> findLayer layerId state.layers
    _ -> Nothing

findLayer :: String -> Array LayerBase -> Maybe LayerBase
findLayer _layerId _layers = Nothing  -- Simplified for now

tabButton :: forall m. String -> Boolean -> H.ComponentHTML Action Slots m
tabButton label active =
  HH.button
    [ cls [ "lattice-tabs-trigger" ]
    , HP.attr (HH.AttrName "data-state") (if active then "active" else "inactive")
    ]
    [ HH.text label ]

collapsiblePanel :: forall m. String -> Boolean -> Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
collapsiblePanel title expanded content =
  HH.div [ cls [ "lattice-collapsible" ] ]
    [ HH.div 
        [ cls [ "lattice-collapsible-header" ]
        , HP.attr (HH.AttrName "data-state") (if expanded then "open" else "closed")
        ]
        [ HH.span [ cls [ "lattice-collapsible-icon" ] ]
            [ HH.text (if expanded then "▼" else "►") ]
        , HH.span [ cls [ "lattice-collapsible-title" ] ]
            [ HH.text title ]
        ]
    , if expanded
        then HH.div [ cls [ "lattice-collapsible-content" ] ] content
        else HH.text ""
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // inline // styles
-- ════════════════════════════════════════════════════════════════════════════

workspaceStyle :: String
workspaceStyle = 
  "display: flex; flex-direction: column; height: 100vh; " <>
  "background: var(--lattice-void); overflow: hidden;"

menuBarStyle :: String
menuBarStyle =
  "height: 28px; min-height: 28px; display: flex; align-items: center; " <>
  "justify-content: space-between; padding: 0 12px; " <>
  "background: var(--lattice-surface-0); border-bottom: 1px solid var(--lattice-border-subtle);"

toolbarStyle :: String
toolbarStyle =
  "min-height: 54px; display: flex; align-items: center; gap: 8px; " <>
  "padding: 8px 12px; background: var(--lattice-surface-1); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

contentStyle :: String
contentStyle =
  "flex: 1; display: flex; overflow: hidden;"

sidebarStyle :: Number -> String
sidebarStyle width =
  "width: " <> show width <> "%; min-width: 200px; max-width: 400px; " <>
  "background: var(--lattice-surface-1); border-right: 1px solid var(--lattice-border-subtle); " <>
  "overflow-y: auto;"

centerStyle :: String
centerStyle =
  "flex: 1; display: flex; flex-direction: column; overflow: hidden;"

viewportStyle :: Number -> String
viewportStyle timelineHeight =
  "flex: 1; min-height: 0; background: var(--lattice-surface-0); " <>
  "display: flex; flex-direction: column;"

timelineStyle :: Number -> String
timelineStyle height =
  "height: " <> show height <> "%; min-height: 150px; " <>
  "background: var(--lattice-surface-1); border-top: 1px solid var(--lattice-border-subtle);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action Slots o m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  SetLeftTab tab -> H.modify_ _ { activeLeftTab = tab }
  
  HandleLayerList output -> case output of
    LayerList.SelectLayer layerId -> 
      H.modify_ _ { selectedLayerIds = [layerId] }
    LayerList.ToggleVisibility _layerId -> pure unit
    LayerList.ToggleLock _layerId -> pure unit
    LayerList.ReorderLayer _layerId _index -> pure unit
  
  HandleTimeline output -> case output of
    Timeline.SeekToFrame frame -> 
      H.modify_ _ { currentFrame = frame }
    Timeline.TogglePlayback -> 
      H.modify_ \s -> s { isPlaying = not s.isPlaying }
    Timeline.SelectLayer layerId -> 
      H.modify_ _ { selectedLayerIds = [layerId] }
    Timeline.ToggleLayerExpanded _layerId -> pure unit
  
  HandleProperties _output -> pure unit
