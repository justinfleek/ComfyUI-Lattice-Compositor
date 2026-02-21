-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // enhanced-layer-track // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Type definitions for EnhancedLayerTrack component.
-- |
-- | System F/Omega: Layer = Record Fields, DragMode = Sum Type
-- |
module Lattice.UI.Components.EnhancedLayerTrack.Types
  ( AnimatablePropertyInfo
  , PropertyGroup
  , LayerTimingInfo
  , MarkerInfo
  , ParentLayerRef
  , EnhancedLayerInfo
  , LayoutMode(..)
  , DragMode(..)
  , Input
  , Output(..)
  , Query
  , Slot
  , State
  , Action(..)
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Set (Set)
import Halogen as H
import Web.UIEvent.MouseEvent (MouseEvent)

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // domain // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Animatable property info for property groups
type AnimatablePropertyInfo =
  { path :: String
  , name :: String
  , animated :: Boolean
  , hasKeyframes :: Boolean
  }

-- | Property group (Transform, Material Options, et al.)
type PropertyGroup =
  { name :: String
  , properties :: Array AnimatablePropertyInfo
  }

-- | Layer timing info for snap targets (simplified version of EnhancedLayerInfo)
type LayerTimingInfo =
  { id :: String
  , inPoint :: Int
  , outPoint :: Int
  }

-- | Marker info for snap targets
type MarkerInfo =
  { frame :: Int
  , label :: String
  }

-- | Parent layer reference for linking
type ParentLayerRef =
  { id :: String
  , index :: Int
  , name :: String
  }

-- | Enhanced layer info with all AE-style features
type EnhancedLayerInfo =
  { id :: String
  , name :: String
  , layerType :: String
  , index :: Int
  -- ── av features ──────────────────────────────────────────────────────────
  , visible :: Boolean
  , audioEnabled :: Boolean
  , isolate :: Boolean
  , locked :: Boolean
  -- ── switches ─────────────────────────────────────────────────────────────
  , minimized :: Boolean
  , flattenTransform :: Boolean
  , quality :: String  -- "best" | "draft"
  , effectsEnabled :: Boolean
  , frameBlending :: Boolean
  , motionBlur :: Boolean
  , effectLayer :: Boolean
  , threeD :: Boolean
  -- ── timing ───────────────────────────────────────────────────────────────
  , inPoint :: Int
  , outPoint :: Int
  -- ── appearance ───────────────────────────────────────────────────────────
  , labelColor :: String
  -- ── parenting ────────────────────────────────────────────────────────────
  , parentId :: Maybe String
  -- ── property groups (computed) ───────────────────────────────────────────
  , propertyGroups :: Array PropertyGroup
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // component // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Layout mode determines sidebar vs track rendering
data LayoutMode = SidebarLayout | TrackLayout

derive instance eqLayoutMode :: Eq LayoutMode

-- | Drag mode for layer bar interactions
data DragMode
  = NotDragging
  | DraggingBar       -- moving entire layer
  | ResizingLeft      -- trimming in-point
  | ResizingRight     -- trimming out-point

derive instance eqDragMode :: Eq DragMode

-- ────────────────────────────────────────────────────────────────────────────
--                                                           // input
-- ────────────────────────────────────────────────────────────────────────────

type Input =
  { layer :: EnhancedLayerInfo
  , layoutMode :: LayoutMode
  , isExpanded :: Boolean
  , isSelected :: Boolean
  , frameCount :: Int
  , pixelsPerFrame :: Number
  , availableParents :: Array ParentLayerRef
  , hasAudioCapability :: Boolean
  -- ── snap targets ─────────────────────────────────────────────────────────
  , allLayers :: Array LayerTimingInfo
  , currentFrame :: Int
  , markers :: Array MarkerInfo
  }

-- ────────────────────────────────────────────────────────────────────────────
--                                                           // output
-- ────────────────────────────────────────────────────────────────────────────

data Output
  = SelectLayer String
  | ToggleExpand String Boolean
  | UpdateLayerVisibility String Boolean
  | UpdateLayerAudio String Boolean
  | UpdateLayerIsolate String Boolean
  | UpdateLayerLocked String Boolean
  | UpdateLayerMinimized String Boolean
  | UpdateLayerFlattenTransform String Boolean
  | UpdateLayerQuality String String
  | UpdateLayerEffectsEnabled String Boolean
  | UpdateLayerFrameBlending String Boolean
  | UpdateLayerMotionBlur String Boolean
  | UpdateLayerEffectLayer String Boolean
  | UpdateLayer3D String Boolean
  | UpdateLayerParent String (Maybe String)
  | UpdateLayerLabelColor String String
  | UpdateLayerTiming String Int Int
  | RenameLayer String String
  | DuplicateLayer String
  | DeleteLayer String
  | NestLayer String
  | ConvertToSplines String
  | ResetTransform String
  | EnterNestedComp String
  | ReorderLayer String Int

-- ────────────────────────────────────────────────────────────────────────────
--                                                           // query // slot
-- ────────────────────────────────────────────────────────────────────────────

data Query a

type Slot id = H.Slot Query Output id

-- ────────────────────────────────────────────────────────────────────────────
--                                                           // state
-- ────────────────────────────────────────────────────────────────────────────

type State =
  { layer :: EnhancedLayerInfo
  , layoutMode :: LayoutMode
  , isExpanded :: Boolean
  , isSelected :: Boolean
  , frameCount :: Int
  , pixelsPerFrame :: Number
  , availableParents :: Array ParentLayerRef
  , hasAudioCapability :: Boolean
  -- ── snap targets ─────────────────────────────────────────────────────────
  , allLayers :: Array LayerTimingInfo
  , currentFrame :: Int
  , markers :: Array MarkerInfo
  -- ── ui state ─────────────────────────────────────────────────────────────
  , expandedGroups :: Set String
  , isRenaming :: Boolean
  , renameValue :: String
  , isDragTarget :: Boolean
  , showColorPicker :: Boolean
  , colorPickerPos :: { x :: Number, y :: Number }
  , contextMenu :: Maybe { x :: Number, y :: Number }
  -- ── drag/resize state ────────────────────────────────────────────────────
  , dragMode :: DragMode
  , dragStartX :: Number
  , dragStartInPoint :: Int
  , dragStartOutPoint :: Int
  }

-- ────────────────────────────────────────────────────────────────────────────
--                                                           // action
-- ────────────────────────────────────────────────────────────────────────────

data Action
  = Initialize
  | Receive Input
  | HandleSelectLayer
  | HandleToggleExpand
  | HandleToggleGroup String
  -- ── av features ──────────────────────────────────────────────────────────
  | HandleToggleVisibility
  | HandleToggleAudio
  | HandleToggleIsolate
  | HandleToggleLock
  -- ── switches ─────────────────────────────────────────────────────────────
  | HandleToggleMinimized
  | HandleToggleFlattenTransform
  | HandleToggleQuality
  | HandleToggleEffects
  | HandleToggleFrameBlend
  | HandleToggleMotionBlur
  | HandleToggleEffectLayer
  | HandleToggle3D
  -- ── parenting ────────────────────────────────────────────────────────────
  | HandleSetParent (Maybe String)
  -- ── color picker ─────────────────────────────────────────────────────────
  | HandleShowColorPicker Number Number
  | HandleHideColorPicker
  | HandleSetLabelColor String
  -- ── renaming ─────────────────────────────────────────────────────────────
  | HandleStartRename
  | HandleRenameInput String
  | HandleFinishRename
  | HandleCancelRename
  -- ── context menu ─────────────────────────────────────────────────────────
  | HandleShowContextMenu Number Number
  | HandleHideContextMenu
  | HandleDuplicate
  | HandleDelete
  | HandleNest
  | HandleConvertToSplines
  | HandleResetTransform
  -- ── drag/drop for layer reordering ───────────────────────────────────────
  | HandleReorderDragStart
  | HandleReorderDragOver
  | HandleReorderDragLeave
  | HandleReorderDrop String
  -- ── double-click actions ─────────────────────────────────────────────────
  | HandleDoubleClick
  -- ── layer bar drag/resize ────────────────────────────────────────────────
  | StartBarDrag MouseEvent
  | StartResizeLeft MouseEvent
  | StartResizeRight MouseEvent
  | OnGlobalMouseMove MouseEvent
  | OnGlobalMouseUp MouseEvent
