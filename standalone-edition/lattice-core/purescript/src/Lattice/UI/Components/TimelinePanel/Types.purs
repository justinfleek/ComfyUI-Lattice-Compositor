-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | TimelinePanel Types
-- |
-- | Type definitions for timeline and layer management.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.TimelinePanel.Types
  ( Input
  , Output(..)
  , Query
  , Slot
  , LayerType(..)
  , WorkArea
  , State
  , Action(..)
  , Slots
  , Proxy(..)
  ) where

import Prelude

import Halogen as H
import Lattice.UI.Components.CompositionTabs as CompositionTabs
import Lattice.UI.Components.EnhancedLayerTrack as EnhancedLayerTrack

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // layer types
-- ════════════════════════════════════════════════════════════════════════════

data LayerType
  = Solid
  | Text
  | Shape
  | Spline
  | Path
  | Particles
  | Control
  | Camera
  | Light
  | Video
  | Model3D
  | PointCloud
  | DepthMap
  | NormalMap
  | Audio
  | AIGenerated
  | Group

derive instance eqLayerType :: Eq LayerType

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // work area
-- ════════════════════════════════════════════════════════════════════════════

type WorkArea =
  { start :: Int
  , end :: Int
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // input
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { layers :: Array EnhancedLayerTrack.EnhancedLayerInfo
  , compositions :: Array CompositionTabs.CompositionInfo
  , activeCompositionId :: String
  , mainCompositionId :: String
  , breadcrumbs :: Array CompositionTabs.BreadcrumbItem
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Int
  , isPlaying :: Boolean
  , selectedLayerIds :: Array String
  , expandedLayerIds :: Array String
  , workArea :: Maybe WorkArea
  , hasAudio :: Boolean
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // output
-- ════════════════════════════════════════════════════════════════════════════

data Output
  = SeekToFrame Int
  | TogglePlayback
  | GoToStart
  | GoToEnd
  | PrevFrame
  | NextFrame
  | SetZoom Number
  | AddLayer LayerType
  | DeleteSelectedLayers
  | SelectLayer String
  | ToggleLayerExpanded String Boolean
  | UpdateLayer EnhancedLayerTrack.Output
  | OpenCompositionSettings
  | OpenPathSuggestion
  | SetWorkArea (Maybe WorkArea)
  | CompositionTabsOutput CompositionTabs.Output

data Query a

type Slot id = H.Slot Query Output id

-- ════════════════════════════════════════════════════════════════════════════
--                                                              // state
-- ════════════════════════════════════════════════════════════════════════════

type State =
  { layers :: Array EnhancedLayerTrack.EnhancedLayerInfo
  , compositions :: Array CompositionTabs.CompositionInfo
  , activeCompositionId :: String
  , mainCompositionId :: String
  , breadcrumbs :: Array CompositionTabs.BreadcrumbItem
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Int
  , isPlaying :: Boolean
  , selectedLayerIds :: Array String
  , expandedLayerIds :: Array String
  , workArea :: Maybe WorkArea
  , hasAudio :: Boolean
  -- UI state
  , zoomPercent :: Number
  , sidebarWidth :: Int
  , showAddLayerMenu :: Boolean
  , viewportWidth :: Number
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // action
-- ════════════════════════════════════════════════════════════════════════════

data Action
  = Initialize
  | Receive Input
  -- Playback
  | HandleTogglePlayback
  | HandleGoToStart
  | HandleGoToEnd
  | HandlePrevFrame
  | HandleNextFrame
  -- Frame input
  | HandleSetFrame Int
  -- Zoom
  | HandleZoomChange Number
  -- Add layer menu
  | HandleToggleAddLayerMenu
  | HandleAddLayer LayerType
  -- Delete
  | HandleDeleteSelected
  -- Settings
  | HandleOpenCompSettings
  | HandleOpenAI
  -- Sidebar resize
  | HandleSidebarResize Int
  -- Work area
  | HandleSetWorkAreaStart Int
  | HandleSetWorkAreaEnd Int
  | HandleClearWorkArea
  -- Ruler scrub
  | HandleRulerScrub Int
  -- Child outputs
  | HandleCompositionTabsOutput CompositionTabs.Output
  | HandleLayerTrackOutput Int EnhancedLayerTrack.Output
  -- Keyboard
  | HandleKeydown String

-- ════════════════════════════════════════════════════════════════════════════
--                                                              // slots
-- ════════════════════════════════════════════════════════════════════════════

type Slots =
  ( compositionTabs :: CompositionTabs.Slot Unit
  , layerTrack :: EnhancedLayerTrack.Slot Int
  )

data Proxy (sym :: Symbol) = Proxy
