-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Workspace Layout Render Functions
-- |
-- | Core render functions for viewports, menubar, toolbar, and left sidebar.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Layout.WorkspaceLayout.Render
  ( render
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.UI.Components.LayerList as LayerList
import Lattice.UI.Components.Timeline as Timeline

import Lattice.UI.Layout.WorkspaceLayout.Types
  ( State
  , Action(..)
  , Slots
  , LeftTab(..)
  , _layerList
  , _timeline
  )
import Lattice.UI.Layout.WorkspaceLayout.Styles as S
import Lattice.UI.Layout.WorkspaceLayout.RenderAI (renderRightSidebar)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-workspace" ]
    , HP.attr (HH.AttrName "style") S.workspaceStyle
    ]
    [ -- menu bar
      renderMenuBar
    
      -- toolbar
    , renderToolbar
    
      -- main content area (3-column split)
    , HH.div
        [ cls [ "lattice-workspace-content" ]
        , HP.attr (HH.AttrName "style") S.contentStyle
        ]
        [ -- left sidebar
          HH.div
            [ cls [ "lattice-sidebar lattice-sidebar-left" ]
            , HP.attr (HH.AttrName "style") (S.sidebarStyle state.leftSidebarWidth "right")
            ]
            [ renderLeftSidebar state ]
        
          -- center (dual viewports + timeline)
        , HH.div
            [ cls [ "lattice-center" ]
            , HP.attr (HH.AttrName "style") S.centerStyle
            ]
            [ -- dual viewport container
              HH.div
                [ cls [ "lattice-viewport-container" ]
                , HP.attr (HH.AttrName "style") S.viewportContainerStyle
                ]
                [ -- left: 3d scene view (working)
                  renderSceneViewport state
                  -- right: render preview (final output)
                , renderRenderViewport state
                ]
            
              -- timeline
            , HH.div
                [ cls [ "lattice-timeline-container" ]
                , HP.attr (HH.AttrName "style") (S.timelineStyle state.timelineHeight)
                ]
                [ renderTimeline state ]
            ]
        
          -- right sidebar (from RenderAI module)
        , HH.div
            [ cls [ "lattice-sidebar lattice-sidebar-right" ]
            , HP.attr (HH.AttrName "style") (S.sidebarStyle state.rightSidebarWidth "left")
            ]
            [ renderRightSidebar state ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // dual viewports
-- ════════════════════════════════════════════════════════════════════════════

-- | 3d scene view - interactive editing viewport
-- | shows composition with shadowbox for dimensions
-- | user can rotate/pan/zoom camera in z-space
renderSceneViewport :: forall m. State -> H.ComponentHTML Action Slots m
renderSceneViewport state =
  HH.div
    [ cls [ "lattice-scene-viewport" ]
    , HP.attr (HH.AttrName "style") S.sceneViewportStyle
    ]
    [ -- header
      HH.div [ cls [ "lattice-viewport-header" ] ]
        [ HH.span [ cls [ "lattice-viewport-title" ] ] 
            [ HH.text "Scene" ]
        , HH.div [ cls [ "lattice-viewport-controls" ] ]
            [ HH.button 
                [ cls [ "lattice-viewport-btn" ]
                , HP.title "Reset Camera"
                , HE.onClick \_ -> ResetSceneCamera
                ]
                [ HH.text "[R]" ]
            ]
        ]
    
      -- scene canvas with shadowbox
    , HH.div 
        [ cls [ "lattice-scene-canvas" ]
        , HP.attr (HH.AttrName "style") S.sceneCanvasStyle
        ]
        [ -- shadowbox overlay showing composition bounds
          HH.div 
            [ cls [ "lattice-shadowbox" ]
            , HP.attr (HH.AttrName "style") (S.shadowboxStyle state.compositionDimensions)
            ]
            []
        
          -- scene content area (layers, keyframes, paths)
        , HH.div [ cls [ "lattice-scene-content" ] ]
            [ -- placeholder for 3d scene rendering
              HH.div [ cls [ "lattice-scene-placeholder" ] ]
                [ HH.text "3D Scene View"
                , HH.br_
                , HH.span [ cls [ "lattice-text-muted" ] ]
                    [ HH.text (show state.compositionDimensions.width <> " x " <> show state.compositionDimensions.height) ]
                ]
            ]
        ]
    
      -- camera info
    , HH.div [ cls [ "lattice-viewport-footer" ] ]
        [ HH.span_ 
            [ HH.text ("Zoom: " <> show (state.sceneCameraZoom * 100.0) <> "%") ]
        ]
    ]

-- | render preview - final output display
-- | shows rendered frames from backend
-- | starts black, updates when render completes
renderRenderViewport :: forall m. State -> H.ComponentHTML Action Slots m
renderRenderViewport state =
  HH.div
    [ cls [ "lattice-render-viewport" ]
    , HP.attr (HH.AttrName "style") S.renderViewportStyle
    ]
    [ -- header
      HH.div [ cls [ "lattice-viewport-header" ] ]
        [ HH.span [ cls [ "lattice-viewport-title" ] ] 
            [ HH.text "Preview" ]
        , if state.isRendering
            then HH.span [ cls [ "lattice-rendering-indicator" ] ]
                [ HH.text "Rendering..." ]
            else HH.text ""
        ]
    
      -- render output area
    , HH.div 
        [ cls [ "lattice-render-canvas" ]
        , HP.attr (HH.AttrName "style") S.renderCanvasStyle
        ]
        [ case state.renderPreviewUrl of
            Nothing ->
              -- black placeholder when no render
              HH.div 
                [ cls [ "lattice-render-placeholder" ]
                , HP.attr (HH.AttrName "style") S.renderPlaceholderStyle
                ]
                [ HH.div [ cls [ "lattice-placeholder-content" ] ]
                    [ HH.span [ cls [ "lattice-text-muted" ] ]
                        [ HH.text "No render" ]
                    , HH.br_
                    , HH.span [ cls [ "lattice-text-xs" ] ]
                        [ HH.text "Generate or import a layer" ]
                    ]
                ]
            Just url ->
              -- display rendered frame
              HH.img
                [ cls [ "lattice-render-output" ]
                , HP.src url
                , HP.alt "Rendered frame"
                , HP.attr (HH.AttrName "style") S.renderOutputStyle
                ]
        ]
    
      -- frame info
    , HH.div [ cls [ "lattice-viewport-footer" ] ]
        [ HH.span_ 
            [ HH.text ("Frame " <> show state.currentFrame <> " / " <> show state.totalFrames) ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // menubar // toolbar
-- ════════════════════════════════════════════════════════════════════════════

renderMenuBar :: forall m. H.ComponentHTML Action Slots m
renderMenuBar =
  HH.div
    [ cls [ "lattice-menubar" ]
    , HP.attr (HH.AttrName "style") S.menuBarStyle
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
    , HP.attr (HH.AttrName "style") S.toolbarStyle
    ]
    [ -- tool group: selection
      HH.div [ cls [ "lattice-tool-group" ] ]
        [ toolButton "select" "Selection Tool" true
        , toolButton "hand" "Pan Tool" false
        , toolButton "zoom" "Zoom Tool" false
        ]
    
      -- tool group: transform
    , HH.div [ cls [ "lattice-tool-group" ] ]
        [ toolButton "move" "Move" false
        , toolButton "rotate" "Rotate" false
        , toolButton "scale" "Scale" false
        ]
    
      -- tool group: create
    , HH.div [ cls [ "lattice-tool-group" ] ]
        [ toolButton "pen" "Pen Tool" false
        , toolButton "rectangle" "Rectangle" false
        , toolButton "ellipse" "Ellipse" false
        , toolButton "text" "Text Tool" false
        ]
    
      -- spacer
    , HH.div [ cls [ "lattice-toolbar-spacer" ] ] []
    
      -- playback controls
    , HH.div [ cls [ "lattice-tool-group lattice-playback" ] ]
        [ toolButton "skip-back" "Go to Start" false
        , toolButton "step-back" "Previous Frame" false
        , toolButton "play" "Play/Pause" false
        , toolButton "step-forward" "Next Frame" false
        , toolButton "skip-forward" "Go to End" false
        ]
    
      -- time display
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
        [] -- icon rendered via css data-icon attribute
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // left sidebar
-- ════════════════════════════════════════════════════════════════════════════

renderLeftSidebar :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderLeftSidebar state =
  HH.div [ cls [ "lattice-sidebar-content" ] ]
    [ -- tabs: project / assets / draw
      HH.div [ cls [ "lattice-sidebar-tabs" ] ]
        [ HH.button 
            [ cls [ "lattice-tabs-trigger" ]
            , HP.attr (HH.AttrName "data-state") (if state.activeLeftTab == TabProject then "active" else "inactive")
            , HE.onClick \_ -> SetLeftTab TabProject
            ]
            [ HH.text "Project" ]
        , HH.button 
            [ cls [ "lattice-tabs-trigger" ]
            , HP.attr (HH.AttrName "data-state") (if state.activeLeftTab == TabAssets then "active" else "inactive")
            , HE.onClick \_ -> SetLeftTab TabAssets
            ]
            [ HH.text "Assets" ]
        , HH.button 
            [ cls [ "lattice-tabs-trigger" ]
            , HP.attr (HH.AttrName "data-state") (if state.activeLeftTab == TabDraw then "active" else "inactive")
            , HE.onClick \_ -> SetLeftTab TabDraw
            ]
            [ HH.text "Draw" ]
        ]
    
      -- tab content
    , case state.activeLeftTab of
        TabProject -> renderProjectTab state
        TabAssets -> renderAssetsTab
        TabDraw -> renderDrawingTab state
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

-- | drawing canvas tab - for controlnet mask painting
renderDrawingTab :: forall m. State -> H.ComponentHTML Action Slots m
renderDrawingTab state =
  HH.div [ cls [ "lattice-sidebar-panel lattice-draw-panel" ] ]
    [ HH.div [ cls [ "lattice-panel-header" ] ]
        [ HH.text "Drawing Canvas" ]
    
      -- brush tools
    , HH.div [ cls [ "lattice-brush-tools" ] ]
        [ HH.div [ cls [ "lattice-brush-control" ] ]
            [ HH.label_ [ HH.text "Size" ]
            , HH.input
                [ HP.type_ HP.InputRange
                , HP.attr (HH.AttrName "min") "1"
                , HP.attr (HH.AttrName "max") "100"
                , HP.attr (HH.AttrName "value") "10"
                ]
            ]
        , HH.div [ cls [ "lattice-brush-control" ] ]
            [ HH.label_ [ HH.text "Opacity" ]
            , HH.input
                [ HP.type_ HP.InputRange
                , HP.attr (HH.AttrName "min") "0"
                , HP.attr (HH.AttrName "max") "100"
                , HP.attr (HH.AttrName "value") "100"
                ]
            ]
        , HH.div [ cls [ "lattice-brush-control" ] ]
            [ HH.label_ [ HH.text "Color" ]
            , HH.input
                [ HP.type_ HP.InputColor
                , HP.attr (HH.AttrName "value") "#FFFFFF"
                ]
            ]
        ]
    
      -- drawing canvas (scaled to fit sidebar)
    , HH.div 
        [ cls [ "lattice-draw-canvas-container" ]
        , HP.attr (HH.AttrName "style") S.drawCanvasContainerStyle
        ]
        [ HH.canvas
            [ cls [ "lattice-draw-canvas" ]
            , HP.id "lattice-draw-canvas"
            , HP.width state.compositionDimensions.width
            , HP.height state.compositionDimensions.height
            , HP.attr (HH.AttrName "style") S.drawCanvasStyle
            ]
        ]
    
      -- actions
    , HH.div [ cls [ "lattice-draw-actions" ] ]
        [ HH.button 
            [ cls [ "lattice-btn lattice-btn-ghost" ]
            , HE.onClick \_ -> ClearDrawingCanvas
            ]
            [ HH.text "Clear" ]
        , HH.button 
            [ cls [ "lattice-btn lattice-btn-primary" ] ]
            [ HH.text "Use as ControlNet Layer" ]
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
