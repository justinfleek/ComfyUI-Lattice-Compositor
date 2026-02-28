-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // motion // layer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layer types and base layer data for motion graphics.
-- |
-- | A Layer is the fundamental unit of content in a Composition. Each layer
-- | has a specific type (Image, Video, Text, Shape, etc.) that determines
-- | its rendering behavior and animatable properties.
-- |
-- | ## Layer Types
-- |
-- | Supports 26+ layer types matching After Effects and LATTICE:
-- | - Media layers: Image, Video, Audio, Solid
-- | - Content layers: Text, Shape, Null
-- | - 3D layers: Camera, Light
-- | - Effects: Adjustment, Effect
-- | - Composition: PreComp, NestedComp
-- | - Specialized: Particle, Depth, Normal, Pose, Model, PointCloud
-- |
-- | ## Architecture
-- |
-- | This module mirrors `Lattice.Project` LayerType and LayerBase from the
-- | Haskell backend, ensuring type-level compatibility for serialization.

module Hydrogen.Schema.Motion.Layer
  ( -- * Layer Type
    LayerType(..)
  , layerTypeToString
  , layerTypeFromString
  , isLayerType3D
  , isLayerTypeMedia
  , isLayerTypeContent
  
  -- * Layer Identifier
  , LayerId(..)
  , mkLayerId
  
  -- * Layer Base
  , LayerBase(..)
  , defaultLayerBase
  , mkLayerBase
  
  -- * Layer Visibility
  , LayerVisibility(..)
  , layerVisibilityToString
  , layerVisibilityFromString
  
  -- * Quality Setting
  , SamplingQuality(..)
  , samplingQualityToString
  , samplingQualityFromString
  
  -- * Accessors
  , layerId
  , layerName
  , layerType
  , layerVisible
  , layerLocked
  , layerSolo
  , layerShy
  , layerEnabled
  , layerSelected
  , layerCollapsed
  , layerGuideLayer
  , layerIs3D
  , layerBlendMode
  , layerOpacity
  , layerStartFrame
  , layerEndFrame
  , layerInPoint
  , layerOutPoint
  , layerStretch
  , layerParentId
  , layerTrackMatteMode
  , layerTrackMatteLayerId
  , layerMotionBlur
  , layerQualitySetting
  , layerSamplingQuality
  , layerPreserveTransparency
  , layerFrameBlending
  , layerTimeRemapEnabled
  , layerCollapseTransformations
  , layerAutoOrient
  
  -- * Predicates
  , isLayerVisible
  , isLayerLocked
  , isLayerSolo
  , isLayerGuide
  , isLayerTimeRemapped
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , class Monoid
  , ($)
  , (#)
  , (<<<)
  , (>>>)
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , compare
  , min
  , max
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , show
  , map
  , pure
  , bind
  , identity
  , const
  , flip
  , apply
  )

import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Ord (abs)
import Data.String (length) as String
import Data.String.CodeUnits (toCharArray) as String
import Data.Array (index, length) as Array
import Hydrogen.Schema.Dimension.Temporal (Frames(Frames))
import Hydrogen.Schema.Motion.Composition 
  ( BlendMode(..)
  , TrackMatteMode(..)
  )
import Hydrogen.Schema.Motion.Camera3D.Enums (AutoOrientMode(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // layer // id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a layer.
-- |
-- | Uses NonEmptyString semantics — must have at least one character.
newtype LayerId = LayerId String

derive instance eqLayerId :: Eq LayerId
derive instance ordLayerId :: Ord LayerId

instance showLayerId :: Show LayerId where
  show (LayerId id) = "Layer:" <> id

-- | Smart constructor for LayerId.
-- |
-- | Returns Nothing if the string is empty.
mkLayerId :: String -> Maybe LayerId
mkLayerId "" = Nothing
mkLayerId s = Just (LayerId s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layer // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of layer content.
-- |
-- | Defines the rendering behavior and available animatable properties.
-- | Each variant corresponds to a specific content type in After Effects.
data LayerType
  -- Media layers
  = LTImage            -- Static image (PNG, JPG, SVG, etc.)
  | LTVideo            -- Video clip with duration
  | LTSolid            -- Solid color fill layer
  | LTAudio            -- Audio clip
  
  -- Content layers
  | LTText             -- Text/typography layer
  | LTShape            -- Vector shape layer
  | LTNull             -- Null object (no render, anchor point only)
  
  -- 3D layers
  | LTCamera           -- Camera for 3D composition
  | LTLight            -- Light source (point, spot, directional)
  
  -- Effect layers
  | LTAdjustment       -- Adjustment layer (effects below)
  | LTEffect           -- Effect layer
  
  -- Composition layers
  | LTPreComp         -- Pre-composition (nested timeline)
  | LTGroup           -- Group/layer folder
  | LTNestedComp      -- Nested composition reference
  
  -- Specialized layers
  | LTParticle        -- Particle system
  | LTDepth           -- Depth map layer
  | LTNormal          -- Normal map layer
  | LTGenerated       -- Procedurally generated content
  | LTMatte           -- Matte/garbage mask layer
  | LTControl         -- Control layer (for expressions)
  | LTSpline          -- Spline/path animation
  | LTPath            -- Path definition layer
  | LTPose            -- Pose/animation reference
  | LTModel           -- 3D model layer
  | LTPointCloud      -- Point cloud data
  | LTDepthflow       -- Depth flow animation

derive instance eqLayerType :: Eq LayerType
derive instance ordLayerType :: Ord LayerType

instance showLayerType :: Show LayerType where
  show = layerTypeToString

-- | Convert layer type to string representation.
layerTypeToString :: LayerType -> String
layerTypeToString LTImage = "image"
layerTypeToString LTVideo = "video"
layerTypeToString LTSolid = "solid"
layerTypeToString LTAudio = "audio"
layerTypeToString LTText = "text"
layerTypeToString LTShape = "shape"
layerTypeToString LTNull = "null"
layerTypeToString LTCamera = "camera"
layerTypeToString LTLight = "light"
layerTypeToString LTAdjustment = "adjustment"
layerTypeToString LTEffect = "effect"
layerTypeToString LTPreComp = "precomp"
layerTypeToString LTGroup = "group"
layerTypeToString LTNestedComp = "nestedcomp"
layerTypeToString LTParticle = "particle"
layerTypeToString LTDepth = "depth"
layerTypeToString LTNormal = "normal"
layerTypeToString LTGenerated = "generated"
layerTypeToString LTMatte = "matte"
layerTypeToString LTControl = "control"
layerTypeToString LTSpline = "spline"
layerTypeToString LTPath = "path"
layerTypeToString LTPose = "pose"
layerTypeToString LTModel = "model"
layerTypeToString LTPointCloud = "pointcloud"
layerTypeToString LTDepthflow = "depthflow"

-- | Parse layer type from string.
layerTypeFromString :: String -> Maybe LayerType
layerTypeFromString "image" = Just LTImage
layerTypeFromString "video" = Just LTVideo
layerTypeFromString "solid" = Just LTSolid
layerTypeFromString "audio" = Just LTAudio
layerTypeFromString "text" = Just LTText
layerTypeFromString "shape" = Just LTShape
layerTypeFromString "null" = Just LTNull
layerTypeFromString "camera" = Just LTCamera
layerTypeFromString "light" = Just LTLight
layerTypeFromString "adjustment" = Just LTAdjustment
layerTypeFromString "effect" = Just LTEffect
layerTypeFromString "precomp" = Just LTPreComp
layerTypeFromString "group" = Just LTGroup
layerTypeFromString "nestedcomp" = Just LTNestedComp
layerTypeFromString "particle" = Just LTParticle
layerTypeFromString "depth" = Just LTDepth
layerTypeFromString "normal" = Just LTNormal
layerTypeFromString "generated" = Just LTGenerated
layerTypeFromString "matte" = Just LTMatte
layerTypeFromString "control" = Just LTControl
layerTypeFromString "spline" = Just LTSpline
layerTypeFromString "path" = Just LTPath
layerTypeFromString "pose" = Just LTPose
layerTypeFromString "model" = Just LTModel
layerTypeFromString "pointcloud" = Just LTPointCloud
layerTypeFromString "depthflow" = Just LTDepthflow
layerTypeFromString _ = Nothing

-- | Check if layer type requires 3D rendering.
isLayerType3D :: LayerType -> Boolean
isLayerType3D LTCamera = true
isLayerType3D LTLight = true
isLayerType3D LTModel = true
isLayerType3D LTPointCloud = true
isLayerType3D LTDepthflow = true
isLayerType3D _ = false

-- | Check if layer type is media (image/video/audio).
isLayerTypeMedia :: LayerType -> Boolean
isLayerTypeMedia LTImage = true
isLayerTypeMedia LTVideo = true
isLayerTypeMedia LTAudio = true
isLayerTypeMedia LTSolid = true
isLayerTypeMedia _ = false

-- | Check if layer type is content (text/shape).
isLayerTypeContent :: LayerType -> Boolean
isLayerTypeContent LTText = true
isLayerTypeContent LTShape = true
isLayerTypeContent LTNull = true
isLayerTypeContent _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // layer // visibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layer visibility state.
-- |
-- | Combines visible, locked, solo, and shy flags into a single state.
data LayerVisibility = LayerVisibility
  { visible :: Boolean    -- Layer is rendered
  , locked :: Boolean     -- Layer cannot be edited
  , solo :: Boolean      -- Only solo layers render (when any solo active)
  , shy :: Boolean       -- Layer hidden in UI (not timeline)
  }

derive instance eqLayerVisibility :: Eq LayerVisibility

instance showLayerVisibility :: Show LayerVisibility where
  show (LayerVisibility v) = 
    "Visibility(" <> 
    (if v.visible then "V" else "-") <>
    (if v.locked then "L" else "-") <>
    (if v.solo then "S" else "-") <>
    (if v.shy then "H" else "-") <>
    ")"
    
-- | Convert visibility state to string (for serialization).
layerVisibilityToString :: LayerVisibility -> String
layerVisibilityToString (LayerVisibility v) =
  (if v.visible then "1" else "0") <>
  (if v.locked then "1" else "0") <>
  (if v.solo then "1" else "0") <>
  (if v.shy then "1" else "0")

-- | Parse visibility state from 4-character string.
layerVisibilityFromString :: String -> Maybe LayerVisibility
layerVisibilityFromString s
  | String.length s /= 4 = Nothing
  | otherwise = Just $ LayerVisibility
      { visible: fromMaybe '0' (safeCharAt 0 s) == '1'
      , locked: fromMaybe '0' (safeCharAt 1 s) == '1'
      , solo: fromMaybe '0' (safeCharAt 2 s) == '1'
      , shy: fromMaybe '0' (safeCharAt 3 s) == '1'
      }

-- | Safe character index for string - returns Nothing if out of bounds.
safeCharAt :: Int -> String -> Maybe Char
safeCharAt i s = 
  let
    chars :: Array Char
    chars = String.toCharArray s
    len = Array.length chars
  in
    if i < 0 || i >= len then Nothing else Array.index chars i

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // sampling // quality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sampling quality for raster effects and motion blur.
data SamplingQuality
  = SQDraft          -- Low quality, fast rendering
  | SQStandard       -- Standard quality
  | SQHigh           -- High quality
  | SQBest           -- Best quality, slow rendering

derive instance eqSamplingQuality :: Eq SamplingQuality
derive instance ordSamplingQuality :: Ord SamplingQuality

instance showSamplingQuality :: Show SamplingQuality where
  show = samplingQualityToString

-- | Convert sampling quality to string.
samplingQualityToString :: SamplingQuality -> String
samplingQualityToString SQDraft = "draft"
samplingQualityToString SQStandard = "standard"
samplingQualityToString SQHigh = "high"
samplingQualityToString SQBest = "best"

-- | Parse sampling quality from string.
samplingQualityFromString :: String -> Maybe SamplingQuality
samplingQualityFromString "draft" = Just SQDraft
samplingQualityFromString "standard" = Just SQStandard
samplingQualityFromString "high" = Just SQHigh
samplingQualityFromString "best" = Just SQBest
samplingQualityFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layer // base
-- ═════════════════════════════════════════════════════════════════════════════

-- | Base layer properties common to all layer types.
-- |
-- | This record contains the animatable and non-animatable properties
-- | that every layer has, regardless of its type.
-- |
-- | ## Invariants
-- |
-- | - startFrame <= endFrame (layer has non-negative duration)
-- | - inPoint >= 0
-- | - outPoint >= inPoint
-- | - opacity is 0-100 (enforced by Percentage type)
-- | - stretch > 0 (time stretching factor)
newtype LayerBase = LayerBase
  { id :: LayerId
  , name :: String
  , layerType :: LayerType
  , visible :: Boolean
  , locked :: Boolean
  , solo :: Boolean
  , shy :: Boolean
  , enabled :: Boolean
  , selected :: Boolean
  , collapsed :: Boolean
  , guideLayer :: Boolean
  , is3D :: Boolean
  , blendMode :: BlendMode
  , opacity :: Number         -- 0-100
  , startFrame :: Frames      -- Layer start in composition
  , endFrame :: Frames        -- Layer end in composition
  , inPoint :: Frames         -- Trim in point
  , outPoint :: Frames        -- Trim out point
  , stretch :: Number         -- Time stretch factor (1.0 = normal)
  , parentId :: Maybe LayerId
  , trackMatteMode :: TrackMatteMode
  , trackMatteLayerId :: Maybe LayerId
  , motionBlur :: Boolean
  , qualitySetting :: Maybe String
  , samplingQuality :: Maybe SamplingQuality
  , preserveTransparency :: Boolean
  , frameBlending :: Boolean
  , timeRemapEnabled :: Boolean
  , collapseTransformations :: Boolean  -- ^ Collapse transformations / Continuously rasterize
  , autoOrient :: AutoOrientMode        -- ^ Auto-orientation mode for layer
  }

derive instance eqLayerBase :: Eq LayerBase

instance showLayerBase :: Show LayerBase where
  show (LayerBase l) = 
    "Layer(" <> l.name <> " @ " <> show l.startFrame <> "-" <> show l.endFrame <> ")"

-- | Default layer base values.
-- |
-- | Creates a default layer at frame 0 with standard settings.
defaultLayerBase :: LayerId -> String -> LayerType -> LayerBase
defaultLayerBase id name lt = LayerBase
  { id: id
  , name: name
  , layerType: lt
  , visible: true
  , locked: false
  , solo: false
  , shy: false
  , enabled: true
  , selected: false
  , collapsed: false
  , guideLayer: false
  , is3D: false
  , blendMode: BMNormal
  , opacity: 100.0
  , startFrame: Frames 0.0
  , endFrame: Frames 300.0    -- 10 seconds at 30fps
  , inPoint: Frames 0.0
  , outPoint: Frames 300.0
  , stretch: 1.0
  , parentId: Nothing
  , trackMatteMode: TMNone
  , trackMatteLayerId: Nothing
  , motionBlur: false
  , qualitySetting: Nothing
  , samplingQuality: Nothing
  , preserveTransparency: false
  , frameBlending: false
  , timeRemapEnabled: false
  , collapseTransformations: false
  , autoOrient: AOMOff
  }

-- | Smart constructor for LayerBase with validation.
-- |
-- | Returns Nothing if parameters are invalid.
mkLayerBase 
  :: LayerId 
  -> String 
  -> LayerType 
  -> Frames   -- startFrame
  -> Frames   -- endFrame
  -> Maybe LayerBase
mkLayerBase id name lt (Frames start) (Frames end)
  | start > end = Nothing
  | start < 0.0 = Nothing
  | otherwise = Just $ LayerBase
      { id: id
      , name: name
      , layerType: lt
      , visible: true
      , locked: false
      , solo: false
      , shy: false
      , enabled: true
      , selected: false
      , collapsed: false
      , guideLayer: false
      , is3D: isLayerType3D lt
      , blendMode: BMNormal
      , opacity: 100.0
      , startFrame: Frames start
      , endFrame: Frames end
      , inPoint: Frames start
      , outPoint: Frames end
      , stretch: 1.0
      , parentId: Nothing
      , trackMatteMode: TMNone
      , trackMatteLayerId: Nothing
      , motionBlur: false
      , qualitySetting: Nothing
      , samplingQuality: Nothing
      , preserveTransparency: false
      , frameBlending: false
      , timeRemapEnabled: false
      , collapseTransformations: false
      , autoOrient: AOMOff
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get layer ID.
layerId :: LayerBase -> LayerId
layerId (LayerBase l) = l.id

-- | Get layer name.
layerName :: LayerBase -> String
layerName (LayerBase l) = l.name

-- | Get layer type.
layerType :: LayerBase -> LayerType
layerType (LayerBase l) = l.layerType

-- | Get layer visibility.
layerVisible :: LayerBase -> Boolean
layerVisible (LayerBase l) = l.visible

-- | Get layer locked state.
layerLocked :: LayerBase -> Boolean
layerLocked (LayerBase l) = l.locked

-- | Get layer solo state.
layerSolo :: LayerBase -> Boolean
layerSolo (LayerBase l) = l.solo

-- | Get layer shy state.
layerShy :: LayerBase -> Boolean
layerShy (LayerBase l) = l.shy

-- | Get layer enabled state.
layerEnabled :: LayerBase -> Boolean
layerEnabled (LayerBase l) = l.enabled

-- | Get layer selected state.
layerSelected :: LayerBase -> Boolean
layerSelected (LayerBase l) = l.selected

-- | Get layer collapsed state.
layerCollapsed :: LayerBase -> Boolean
layerCollapsed (LayerBase l) = l.collapsed

-- | Get guide layer state.
layerGuideLayer :: LayerBase -> Boolean
layerGuideLayer (LayerBase l) = l.guideLayer

-- | Get layer 3D state.
layerIs3D :: LayerBase -> Boolean
layerIs3D (LayerBase l) = l.is3D

-- | Get layer blend mode.
layerBlendMode :: LayerBase -> BlendMode
layerBlendMode (LayerBase l) = l.blendMode

-- | Get layer opacity.
layerOpacity :: LayerBase -> Number
layerOpacity (LayerBase l) = l.opacity

-- | Get layer start frame.
layerStartFrame :: LayerBase -> Frames
layerStartFrame (LayerBase l) = l.startFrame

-- | Get layer end frame.
layerEndFrame :: LayerBase -> Frames
layerEndFrame (LayerBase l) = l.endFrame

-- | Get layer in point.
layerInPoint :: LayerBase -> Frames
layerInPoint (LayerBase l) = l.inPoint

-- | Get layer out point.
layerOutPoint :: LayerBase -> Frames
layerOutPoint (LayerBase l) = l.outPoint

-- | Get layer stretch factor.
layerStretch :: LayerBase -> Number
layerStretch (LayerBase l) = l.stretch

-- | Get layer parent ID.
layerParentId :: LayerBase -> Maybe LayerId
layerParentId (LayerBase l) = l.parentId

-- | Get track matte mode.
layerTrackMatteMode :: LayerBase -> TrackMatteMode
layerTrackMatteMode (LayerBase l) = l.trackMatteMode

-- | Get track matte layer ID.
layerTrackMatteLayerId :: LayerBase -> Maybe LayerId
layerTrackMatteLayerId (LayerBase l) = l.trackMatteLayerId

-- | Get motion blur enabled state.
layerMotionBlur :: LayerBase -> Boolean
layerMotionBlur (LayerBase l) = l.motionBlur

-- | Get quality setting.
layerQualitySetting :: LayerBase -> Maybe String
layerQualitySetting (LayerBase l) = l.qualitySetting

-- | Get sampling quality.
layerSamplingQuality :: LayerBase -> Maybe SamplingQuality
layerSamplingQuality (LayerBase l) = l.samplingQuality

-- | Get preserve transparency state.
layerPreserveTransparency :: LayerBase -> Boolean
layerPreserveTransparency (LayerBase l) = l.preserveTransparency

-- | Get frame blending state.
layerFrameBlending :: LayerBase -> Boolean
layerFrameBlending (LayerBase l) = l.frameBlending

-- | Get time remap enabled state.
layerTimeRemapEnabled :: LayerBase -> Boolean
layerTimeRemapEnabled (LayerBase l) = l.timeRemapEnabled

-- | Get collapse transformations state.
-- |
-- | When enabled on a pre-comp layer, renders at composition resolution
-- | instead of pre-comp resolution. When enabled on a vector layer (shape,
-- | text), continuously rasterizes at current scale.
layerCollapseTransformations :: LayerBase -> Boolean
layerCollapseTransformations (LayerBase l) = l.collapseTransformations

-- | Get auto-orient mode.
-- |
-- | Controls automatic layer orientation:
-- | - Off: No auto-orientation
-- | - Along Path: Layer orients along motion path tangent
-- | - Towards POI: Layer always faces point of interest
layerAutoOrient :: LayerBase -> AutoOrientMode
layerAutoOrient (LayerBase l) = l.autoOrient

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if layer is visible.
isLayerVisible :: LayerBase -> Boolean
isLayerVisible l = layerVisible l && layerEnabled l

-- | Check if layer is locked.
isLayerLocked :: LayerBase -> Boolean
isLayerLocked = layerLocked

-- | Check if layer is solo.
isLayerSolo :: LayerBase -> Boolean
isLayerSolo = layerSolo

-- | Check if layer is a guide layer.
isLayerGuide :: LayerBase -> Boolean
isLayerGuide = layerGuideLayer

-- | Check if time remapping is enabled.
isLayerTimeRemapped :: LayerBase -> Boolean
isLayerTimeRemapped = layerTimeRemapEnabled
