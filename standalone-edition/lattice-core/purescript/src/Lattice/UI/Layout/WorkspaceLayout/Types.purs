-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Workspace Layout Types
-- |
-- | Type definitions for the main workspace layout component.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Layout.WorkspaceLayout.Types
  ( Input
  , Output
  , Query
  , Slot
  , CompositionDimensions
  , State
  , LeftTab(..)
  , GenerationMode(..)
  , Action(..)
  , Slots
    -- proxies
  , _menuBar
  , _toolbar
  , _leftSidebar
  , _sceneViewport
  , _renderViewport
  , _timeline
  , _rightSidebar
  , _layerList
  , _properties
  ) where

import Prelude

import Data.Const (Const)
import Data.Either (Either)
import Data.Maybe (Maybe)
import Type.Proxy (Proxy(..))
import Halogen as H

import Lattice.UI.Components.LayerList as LayerList
import Lattice.UI.Components.Timeline as Timeline
import Lattice.UI.Components.PropertiesPanel as PropertiesPanel
import Lattice.Project (LayerBase)
import Lattice.Services.Bridge.Client as Bridge

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // input // output
-- ════════════════════════════════════════════════════════════════════════════

type Input = 
  { bridgeClient :: Maybe Bridge.BridgeClient
  }

type Output = Void

data Query a

type Slot id = H.Slot Query Output id

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // state
-- ════════════════════════════════════════════════════════════════════════════

type CompositionDimensions =
  { width :: Int
  , height :: Int
  }

type State =
  { -- layout
    leftSidebarWidth :: Number  -- percentage (default 14%)
  , rightSidebarWidth :: Number -- percentage (default 20%)
  , timelineHeight :: Number    -- percentage (default 35%)
  , viewportSplit :: Number     -- left/right viewport split (default 50%)
    -- project
  , layers :: Array LayerBase
  , selectedLayerIds :: Array String
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Number
  , isPlaying :: Boolean
    -- composition
  , compositionDimensions :: CompositionDimensions
    -- tabs
  , activeLeftTab :: LeftTab
    -- render state
  , renderPreviewUrl :: Maybe String  -- base64 or url of rendered frame
  , isRendering :: Boolean
  , renderError :: Maybe String       -- error message if render failed
    -- generation progress
  , generationProgress :: Number      -- 0.0 to 100.0
  , generationStage :: String         -- "idle" | "encoding" | "sampling" | "decoding"
  , generationEta :: Maybe Number     -- estimated seconds remaining
    -- 3d scene state
  , sceneCameraRotation :: { x :: Number, y :: Number, z :: Number }
  , sceneCameraPosition :: { x :: Number, y :: Number, z :: Number }
  , sceneCameraZoom :: Number
    -- bridge
  , bridgeClient :: Maybe Bridge.BridgeClient
    -- ai generation
  , promptText :: String
  , negativePrompt :: String
  , generationMode :: GenerationMode
  , selectedModel :: String
  , sourceImageUrl :: Maybe String  -- for i2v/edit mode
  , maskImageUrl :: Maybe String    -- for edit mode (white = edit, black = keep)
  , numFrames :: Int
  , cfgScale :: Number
  , steps :: Int
  , seed :: Maybe Int               -- random seed (Nothing = auto)
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // tabs // modes
-- ════════════════════════════════════════════════════════════════════════════

data LeftTab 
  = TabProject   -- layer list
  | TabAssets    -- imported files browser
  | TabDraw      -- drawing canvas for controlnet
derive instance eqLeftTab :: Eq LeftTab

-- | Generation mode - determines which models are available
data GenerationMode
  = TextToImage   -- t2i - generate still image from prompt
  | ImageEdit     -- edit - inpaint/outpaint with mask
  | ImageToVideo  -- i2v - animate an image with prompt
  | TextToVideo   -- t2v - generate video from prompt
  | TextTo3D      -- 3d - generate 3d model from prompt/image
derive instance eqGenerationMode :: Eq GenerationMode

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

data Action
  = Initialize
  | Receive Input
  | SetLeftTab LeftTab
  | HandleLayerList LayerList.Output
  | HandleTimeline Timeline.Output
  | HandleProperties PropertiesPanel.Output
    -- viewport actions
  | RotateSceneCamera Number Number
  | PanSceneCamera Number Number
  | ZoomSceneCamera Number
  | ResetSceneCamera
    -- drawing canvas actions
  | SetBrushSize Number
  | SetBrushColor String
  | SetBrushOpacity Number
  | ClearDrawingCanvas
    -- ai generation actions
  | SetPromptText String
  | SetNegativePrompt String
  | SetGenerationMode GenerationMode
  | SetModel String
  | SetNumFrames Int
  | SetCfgScale Number
  | SetSteps Int
  | SetSourceImage String
  | GenerateFromPrompt
  | ReceiveGenerateProgress Number String  -- percentage, stage
  | ReceiveGenerateResult (Either String Bridge.GenerateResult)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // slots
-- ════════════════════════════════════════════════════════════════════════════

type Slots =
  ( menuBar :: H.Slot (Const Void) Void Unit
  , toolbar :: H.Slot (Const Void) Void Unit
  , leftSidebar :: H.Slot (Const Void) Void Unit
  , sceneViewport :: H.Slot (Const Void) Void Unit
  , renderViewport :: H.Slot (Const Void) Void Unit
  , timeline :: Timeline.Slot Unit
  , rightSidebar :: H.Slot (Const Void) Void Unit
  , layerList :: LayerList.Slot Unit
  , properties :: PropertiesPanel.Slot Unit
  )

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // proxies
-- ════════════════════════════════════════════════════════════════════════════

_menuBar :: Proxy "menuBar"
_menuBar = Proxy

_toolbar :: Proxy "toolbar"
_toolbar = Proxy

_leftSidebar :: Proxy "leftSidebar"
_leftSidebar = Proxy

_sceneViewport :: Proxy "sceneViewport"
_sceneViewport = Proxy

_renderViewport :: Proxy "renderViewport"
_renderViewport = Proxy

_timeline :: Proxy "timeline"
_timeline = Proxy

_rightSidebar :: Proxy "rightSidebar"
_rightSidebar = Proxy

_layerList :: Proxy "layerList"
_layerList = Proxy

_properties :: Proxy "properties"
_properties = Proxy
