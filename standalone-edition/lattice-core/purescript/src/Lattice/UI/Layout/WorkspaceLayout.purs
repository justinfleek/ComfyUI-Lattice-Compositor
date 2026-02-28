-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // lattice // ui // workspace-layout
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Workspace Layout Component
-- |
-- | The main workspace layout for the Lattice Compositor.
-- | Composes child components: MenuBar, Toolbar, LeftSidebar, CenterViewport, RightSidebar.
-- |
-- | ┌─────────────────────────────────────────────────────────────────────────┐
-- | │ MenuBar (28px)                                                          │
-- | ├─────────────────────────────────────────────────────────────────────────┤
-- | │ Toolbar (54px)                                                          │
-- | ├────────┬────────────────────────────────────────────────┬───────────────┤
-- | │        │  ┌─────────────────────────────────────────┐   │               │
-- | │  Left  │  │         Center Viewport                 │   │    Right      │
-- | │ Sidebar│  │  (Canvas + Grid + Rulers + Timeline)    │   │   Sidebar     │
-- | │ (14%)  │  │                                         │   │    (20%)      │
-- | │        │  └─────────────────────────────────────────┘   │               │
-- | │ Tabs:  │                                                │  Properties   │
-- | │-Project│                                                │  + AI Panel   │
-- | │-Effects│                                                │               │
-- | │-Assets │                                                │               │
-- | └────────┴────────────────────────────────────────────────┴───────────────┘
-- |
module Lattice.UI.Layout.WorkspaceLayout
  ( component
  , Input
  , Output
  , Query
  , Slot
  ) where

import Prelude

import Data.Array (length, filter)
import Data.Maybe (Maybe(..))
import Type.Proxy (Proxy(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.UI.Layout.MenuBar as MenuBar
import Lattice.UI.Layout.Toolbar as Toolbar
import Lattice.UI.Layout.LeftSidebar as LeftSidebar
import Lattice.UI.Layout.RightSidebar as RightSidebar
import Lattice.UI.Layout.CenterViewport as CenterViewport
import Lattice.Services.Bridge.Client as Bridge

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input = 
  { bridgeClient :: Maybe Bridge.BridgeClient
  }

type Output = Void

data Query a

type Slot id = H.Slot Query Output id

type State =
  { -- Layout
    leftSidebarWidth :: Number  -- Percentage (default 14%)
  , rightSidebarWidth :: Number -- Percentage (default 20%)
    -- Project
  , projectName :: String
  , hasUnsavedChanges :: Boolean
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Number
  , isPlaying :: Boolean
  , canUndo :: Boolean
  , canRedo :: Boolean
  , hasSelection :: Boolean
  , selectedLayerId :: Maybe String
    -- Composition
  , compWidth :: Int
  , compHeight :: Int
    -- Tool state
  , currentTool :: Toolbar.Tool
  , gpuTier :: String
    -- Left sidebar
  , leftTab :: LeftSidebar.LeftTab
  , compositionCount :: Int
  , assetCount :: Int
    -- Right sidebar
  , aiTab :: RightSidebar.AITab
  , expandedPanels :: RightSidebar.ExpandedPanels
    -- Center viewport
  , viewportTab :: CenterViewport.ViewportTab
  , viewOptions :: CenterViewport.ViewOptions
  , showCurveEditor :: Boolean
  , guides :: Array CenterViewport.Guide
  , snapEnabled :: Boolean
  , snapIndicatorX :: Maybe Number
  , snapIndicatorY :: Maybe Number
    -- Bridge
  , bridgeClient :: Maybe Bridge.BridgeClient
    -- Generation
  , isRendering :: Boolean
  , renderError :: Maybe String
  }

data Action
  = Initialize
  | Receive Input
  | HandleMenuBar MenuBar.Output
  | HandleToolbar Toolbar.Output
  | HandleLeftSidebar LeftSidebar.Output
  | HandleRightSidebar RightSidebar.Output
  | HandleCenterViewport CenterViewport.Output

type Slots =
  ( menuBar :: MenuBar.Slot Unit
  , toolbar :: Toolbar.Slot Unit
  , leftSidebar :: LeftSidebar.Slot Unit
  , rightSidebar :: RightSidebar.Slot Unit
  , centerViewport :: CenterViewport.Slot Unit
  )

_menuBar :: Proxy "menuBar"
_menuBar = Proxy

_toolbar :: Proxy "toolbar"
_toolbar = Proxy

_leftSidebar :: Proxy "leftSidebar"
_leftSidebar = Proxy

_rightSidebar :: Proxy "rightSidebar"
_rightSidebar = Proxy

_centerViewport :: Proxy "centerViewport"
_centerViewport = Proxy

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q o m. MonadAff m => H.Component q Input o m
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
  { leftSidebarWidth: 14.0
  , rightSidebarWidth: 20.0
  , projectName: "Untitled Project"
  , hasUnsavedChanges: false
  , currentFrame: 0
  , totalFrames: 81
  , fps: 16.0
  , isPlaying: false
  , canUndo: false
  , canRedo: false
  , hasSelection: false
  , selectedLayerId: Nothing
  , compWidth: 1920
  , compHeight: 1080
  , currentTool: Toolbar.ToolSelect
  , gpuTier: "webgpu"
  , leftTab: LeftSidebar.TabProject
  , compositionCount: 1
  , assetCount: 0
  , aiTab: RightSidebar.AIChat
  , expandedPanels: defaultExpandedPanels
  , viewportTab: CenterViewport.TabComposition
  , viewOptions: defaultViewOptions
  , showCurveEditor: false
  , guides: []
  , snapEnabled: true
  , snapIndicatorX: Nothing
  , snapIndicatorY: Nothing
  , bridgeClient: input.bridgeClient
  , isRendering: false
  , renderError: Nothing
  }

defaultExpandedPanels :: RightSidebar.ExpandedPanels
defaultExpandedPanels =
  { properties: true
  , effects: false
  , drivers: false
  , scopes: false
  , camera: false
  , audio: false
  , align: false
  , preview: false
  }

defaultViewOptions :: CenterViewport.ViewOptions
defaultViewOptions =
  { showGrid: false
  , showRulers: false
  , showAxes: false
  , showCameraFrustum: false
  , showCompositionBounds: true
  , showFocalPlane: false
  , showLayerOutlines: true
  , showSafeZones: false
  , showGuides: true
  , gridSize: 50
  , gridDivisions: 5
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
      HH.slot _menuBar unit MenuBar.component
        { projectName: state.projectName
        , hasUnsavedChanges: state.hasUnsavedChanges
        , canUndo: state.canUndo
        , canRedo: state.canRedo
        , hasSelection: state.hasSelection
        }
        HandleMenuBar
    
      -- Toolbar
    , HH.slot _toolbar unit Toolbar.component
        { currentTool: state.currentTool
        , isPlaying: state.isPlaying
        , currentFrame: state.currentFrame
        , totalFrames: state.totalFrames
        , fps: state.fps
        , canUndo: state.canUndo
        , canRedo: state.canRedo
        , gpuTier: state.gpuTier
        }
        HandleToolbar
    
      -- Main content area (3-column split)
    , HH.div
        [ cls [ "lattice-workspace-content" ]
        , HP.attr (HH.AttrName "style") contentStyle
        ]
        [ -- Left Sidebar
          HH.div
            [ cls [ "lattice-sidebar", "lattice-sidebar-left" ]
            , HP.attr (HH.AttrName "style") (sidebarStyle state.leftSidebarWidth "right")
            ]
            [ HH.slot _leftSidebar unit LeftSidebar.component
                { activeTab: state.leftTab
                , projectName: state.projectName
                , compositionCount: state.compositionCount
                , assetCount: state.assetCount
                }
                HandleLeftSidebar
            ]
        
          -- Center (Viewport + Timeline)
        , HH.div
            [ cls [ "lattice-center" ]
            , HP.attr (HH.AttrName "style") centerStyle
            ]
            [ HH.slot _centerViewport unit CenterViewport.component
                { viewportTab: state.viewportTab
                , viewOptions: state.viewOptions
                , showCurveEditor: state.showCurveEditor
                , guides: state.guides
                , snapEnabled: state.snapEnabled
                , snapIndicatorX: state.snapIndicatorX
                , snapIndicatorY: state.snapIndicatorY
                , compWidth: state.compWidth
                , compHeight: state.compHeight
                , currentFrame: state.currentFrame
                , totalFrames: state.totalFrames
                , fps: state.fps
                }
                HandleCenterViewport
            ]
        
          -- Right Sidebar
        , HH.div
            [ cls [ "lattice-sidebar", "lattice-sidebar-right" ]
            , HP.attr (HH.AttrName "style") (sidebarStyle state.rightSidebarWidth "left")
            ]
            [ HH.slot _rightSidebar unit RightSidebar.component
                { aiTab: state.aiTab
                , expandedPanels: state.expandedPanels
                , selectedLayerId: state.selectedLayerId
                , hasSelection: state.hasSelection
                }
                HandleRightSidebar
            ]
        ]
    
      -- Connection status footer
    , renderConnectionStatus state
    ]

renderConnectionStatus :: forall m. State -> H.ComponentHTML Action Slots m
renderConnectionStatus state =
  HH.div
    [ cls [ "lattice-status-bar" ]
    , HP.attr (HH.AttrName "style") statusBarStyle
    ]
    [ case state.bridgeClient of
        Nothing -> 
          HH.span 
            [ cls [ "lattice-status", "lattice-status-disconnected" ] ]
            [ HH.text "Backend disconnected" ]
        Just _ ->
          HH.span 
            [ cls [ "lattice-status", "lattice-status-connected" ] ]
            [ HH.text "Connected" ]
    , case state.renderError of
        Just err -> 
          HH.span [ cls [ "lattice-error-status" ] ] [ HH.text err ]
        Nothing -> HH.text ""
    , HH.span [ cls [ "lattice-frame-status" ] ]
        [ HH.text (show state.compWidth <> " × " <> show state.compHeight <> " @ " <> show state.fps <> " fps") ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

workspaceStyle :: String
workspaceStyle = 
  "display: flex; flex-direction: column; height: 100vh; " <>
  "background: var(--lattice-void, #050505); overflow: hidden;"

contentStyle :: String
contentStyle =
  "flex: 1; display: flex; overflow: hidden;"

sidebarStyle :: Number -> String -> String
sidebarStyle width borderSide =
  "width: " <> show width <> "%; min-width: 200px; max-width: 400px; " <>
  "background: var(--lattice-surface-1, #121212); " <>
  "border-" <> borderSide <> ": 1px solid var(--lattice-border-subtle, #2a2a2a); " <>
  "overflow: hidden; display: flex; flex-direction: column;"

centerStyle :: String
centerStyle =
  "flex: 1; display: flex; flex-direction: column; overflow: hidden; " <>
  "min-width: 400px;"

statusBarStyle :: String
statusBarStyle =
  "height: 22px; display: flex; align-items: center; justify-content: space-between; " <>
  "padding: 0 12px; gap: 16px; " <>
  "background: var(--lattice-surface-0, #0a0a0a); " <>
  "border-top: 1px solid var(--lattice-border-subtle, #2a2a2a); " <>
  "font-size: 10px; color: var(--lattice-text-secondary, #888);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action Slots o m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> 
    H.modify_ _ { bridgeClient = input.bridgeClient }
  
  HandleMenuBar output -> case output of
    MenuBar.MenuActionSelected action -> handleMenuAction action
  
  HandleToolbar output -> case output of
    Toolbar.ToolbarActionSelected action -> handleToolbarAction action
  
  HandleLeftSidebar output -> case output of
    LeftSidebar.SidebarActionSelected action -> handleLeftSidebarAction action
  
  HandleRightSidebar output -> case output of
    RightSidebar.RightSidebarActionSelected action -> handleRightSidebarAction action
  
  HandleCenterViewport output -> case output of
    CenterViewport.ViewportActionSelected action -> handleViewportAction action

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // action handlers
-- ════════════════════════════════════════════════════════════════════════════

handleMenuAction :: forall o m. MonadAff m => MenuBar.MenuAction -> H.HalogenM State Action Slots o m Unit
handleMenuAction action = case action of
  MenuBar.SaveProject -> H.modify_ _ { hasUnsavedChanges = false }
  MenuBar.Undo -> H.modify_ _ { canUndo = false }
  MenuBar.Redo -> H.modify_ _ { canRedo = false }
  MenuBar.DeselectAll -> H.modify_ _ { hasSelection = false, selectedLayerId = Nothing }
  MenuBar.ToggleGrid -> 
    H.modify_ \s -> s { viewOptions = s.viewOptions { showGrid = not s.viewOptions.showGrid } }
  MenuBar.ToggleRulers -> 
    H.modify_ \s -> s { viewOptions = s.viewOptions { showRulers = not s.viewOptions.showRulers } }
  MenuBar.ToggleGuides -> 
    H.modify_ \s -> s { viewOptions = s.viewOptions { showGuides = not s.viewOptions.showGuides } }
  MenuBar.ToggleSafeZones -> 
    H.modify_ \s -> s { viewOptions = s.viewOptions { showSafeZones = not s.viewOptions.showSafeZones } }
  MenuBar.ToggleCurveEditor -> 
    H.modify_ \s -> s { showCurveEditor = not s.showCurveEditor }
  MenuBar.ShowProperties -> 
    H.modify_ \s -> s { expandedPanels = s.expandedPanels { properties = true } }
  MenuBar.ShowEffects -> 
    H.modify_ \s -> s { expandedPanels = s.expandedPanels { effects = true } }
  MenuBar.ShowCamera -> 
    H.modify_ \s -> s { expandedPanels = s.expandedPanels { camera = true } }
  MenuBar.ShowAudio -> 
    H.modify_ \s -> s { expandedPanels = s.expandedPanels { audio = true } }
  MenuBar.ShowAlign -> 
    H.modify_ \s -> s { expandedPanels = s.expandedPanels { align = true } }
  MenuBar.ShowAIChat -> 
    H.modify_ _ { aiTab = RightSidebar.AIChat }
  MenuBar.ShowAIGenerate -> 
    H.modify_ _ { aiTab = RightSidebar.AIGenerate }
  MenuBar.ShowPreview -> 
    H.modify_ \s -> s { expandedPanels = s.expandedPanels { preview = true } }
  -- All other menu actions are not yet implemented
  _ -> pure unit

handleToolbarAction :: forall o m. MonadAff m => Toolbar.ToolbarAction -> H.HalogenM State Action Slots o m Unit
handleToolbarAction = case _ of
  Toolbar.SetTool tool -> 
    H.modify_ _ { currentTool = tool }
  Toolbar.GoToStart -> 
    H.modify_ _ { currentFrame = 0 }
  Toolbar.StepBackward -> 
    H.modify_ \s -> s { currentFrame = max 0 (s.currentFrame - 1) }
  Toolbar.TogglePlayback -> 
    H.modify_ \s -> s { isPlaying = not s.isPlaying }
  Toolbar.StepForward -> 
    H.modify_ \s -> s { currentFrame = min s.totalFrames (s.currentFrame + 1) }
  Toolbar.GoToEnd -> 
    H.modify_ \s -> s { currentFrame = s.totalFrames }
  Toolbar.UndoAction -> 
    H.modify_ _ { canUndo = false }  -- Would call Bridge.undo
  Toolbar.RedoAction -> 
    H.modify_ _ { canRedo = false }
  Toolbar.ImportAction -> pure unit
  Toolbar.ShowPreview -> pure unit
  Toolbar.ShowTemplateBuilder -> pure unit
  Toolbar.ShowExport -> pure unit
  Toolbar.ShowComfyUI -> pure unit

handleLeftSidebarAction :: forall o m. MonadAff m => LeftSidebar.SidebarAction -> H.HalogenM State Action Slots o m Unit
handleLeftSidebarAction = case _ of
  LeftSidebar.TabChanged tab -> 
    H.modify_ _ { leftTab = tab }
  LeftSidebar.OpenCompositionSettings -> pure unit
  LeftSidebar.CreateLayersFromSvg _svgId -> pure unit
  LeftSidebar.UseMeshAsEmitter _meshId -> pure unit
  LeftSidebar.EnvironmentUpdate _settings -> pure unit
  LeftSidebar.EnvironmentLoad _settings -> pure unit
  LeftSidebar.EnvironmentClear -> pure unit
  LeftSidebar.SelectComposition _compId -> pure unit
  LeftSidebar.SelectAsset _assetId -> pure unit
  LeftSidebar.ApplyEffectFromLibrary _effectName -> pure unit

handleRightSidebarAction :: forall o m. MonadAff m => RightSidebar.RightSidebarAction -> H.HalogenM State Action Slots o m Unit
handleRightSidebarAction = case _ of
  RightSidebar.AITabChanged tab -> 
    H.modify_ _ { aiTab = tab }
  RightSidebar.PanelToggled key expanded -> 
    H.modify_ \s -> s { expandedPanels = updatePanel s.expandedPanels key expanded }
  RightSidebar.CameraUpdated -> pure unit
  RightSidebar.SendChatMessage _message -> pure unit  -- Would send to AI via Bridge
  RightSidebar.GenerateDepthMap -> startGeneration "depth"
  RightSidebar.GenerateNormalMap -> startGeneration "normal"
  RightSidebar.GenerateSegmentation -> startGeneration "segment"
  RightSidebar.StartFlowGeneration -> startGeneration "flow"
  RightSidebar.StartDecomposition -> startGeneration "decompose"

updatePanel :: RightSidebar.ExpandedPanels -> String -> Boolean -> RightSidebar.ExpandedPanels
updatePanel panels key expanded = case key of
  "properties" -> panels { properties = expanded }
  "effects" -> panels { effects = expanded }
  "drivers" -> panels { drivers = expanded }
  "scopes" -> panels { scopes = expanded }
  "camera" -> panels { camera = expanded }
  "audio" -> panels { audio = expanded }
  "align" -> panels { align = expanded }
  "preview" -> panels { preview = expanded }
  _ -> panels

startGeneration :: forall o m. MonadAff m => String -> H.HalogenM State Action Slots o m Unit
startGeneration _genType = do
  state <- H.get
  case state.bridgeClient of
    Nothing -> 
      H.modify_ _ { renderError = Just "Backend not connected" }
    Just _client -> do
      H.modify_ _ { isRendering = true, renderError = Nothing }
      -- Would call appropriate Bridge.generate* function
      pure unit

handleViewportAction :: forall o m. MonadAff m => CenterViewport.ViewportAction -> H.HalogenM State Action Slots o m Unit
handleViewportAction = case _ of
  CenterViewport.ViewportTabChanged tab -> 
    H.modify_ _ { viewportTab = tab }
  CenterViewport.ViewOptionsChanged options -> 
    H.modify_ _ { viewOptions = options }
  CenterViewport.ToggleCurveEditor -> 
    H.modify_ \s -> s { showCurveEditor = not s.showCurveEditor }
  CenterViewport.GuideCreated orientation position -> 
    H.modify_ \s -> s { guides = s.guides <> [{ id: "guide-" <> show (1 + length s.guides), orientation, position }] }
  CenterViewport.GuideMoved guideId newPosition -> 
    H.modify_ \s -> s { guides = map (\g -> if g.id == guideId then g { position = newPosition } else g) s.guides }
  CenterViewport.GuideDeleted guideId -> 
    H.modify_ \s -> s { guides = filter (\g -> g.id /= guideId) s.guides }
  CenterViewport.AllGuidesCleared -> 
    H.modify_ _ { guides = [] }
  CenterViewport.OpenCompositionSettings -> pure unit
  CenterViewport.OpenPathSuggestion -> pure unit
  CenterViewport.CanvasClicked _x _y -> pure unit
  CenterViewport.CanvasZoomed _delta -> pure unit
