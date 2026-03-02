-- | Lattice.Schemas.Layers.LayerDataSchema.Render - Render layer enums
-- |
-- | Enums for Camera, Light, Control, Model, PointCloud, Matte, and Depthflow layers.

module Lattice.Schemas.Layers.LayerDataSchema.Render
  ( -- Control Layer
    IconShape(..), iconShapeFromString
    -- Camera Layer
  , CameraType(..), cameraTypeFromString
  , CameraLookMode(..), cameraLookModeFromString
  , CameraShakeType(..), cameraShakeTypeFromString
  , RackFocusEasing(..), rackFocusEasingFromString
  , AutoFocusMode(..), autoFocusModeFromString
    -- Light Layer
  , LightType(..), lightTypeFromString
  , LightFalloff(..), lightFalloffFromString
    -- Pose Layer
  , PoseFormat(..), poseFormatFromString
    -- Model Layer
  , ModelType(..), modelTypeFromString
    -- Point Cloud Layer
  , PointCloudFormat(..), pointCloudFormatFromString
  , PointCloudColorMode(..), pointCloudColorModeFromString
    -- Matte Layer
  , MatteType(..), matteTypeFromString
  , MattePreviewMode(..), mattePreviewModeFromString
    -- Procedural Matte
  , ProceduralMatteType(..), proceduralMatteTypeFromString
  , WaveType(..), waveTypeFromString
    -- Depthflow Layer
  , DepthflowPreset(..), depthflowPresetFromString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Control Layer
--------------------------------------------------------------------------------

data IconShape = IconCrosshair | IconDiamond | IconCircle | IconSquare

derive instance Eq IconShape
derive instance Generic IconShape _
instance Show IconShape where show = genericShow

iconShapeFromString :: String -> Maybe IconShape
iconShapeFromString = case _ of
  "crosshair" -> Just IconCrosshair
  "diamond" -> Just IconDiamond
  "circle" -> Just IconCircle
  "square" -> Just IconSquare
  _ -> Nothing

--------------------------------------------------------------------------------
-- Camera Layer
--------------------------------------------------------------------------------

data CameraType = CamOneNode | CamTwoNode

derive instance Eq CameraType
derive instance Generic CameraType _
instance Show CameraType where show = genericShow

cameraTypeFromString :: String -> Maybe CameraType
cameraTypeFromString = case _ of
  "one-node" -> Just CamOneNode
  "two-node" -> Just CamTwoNode
  _ -> Nothing

data CameraLookMode = LookTangent | LookTarget | LookFixed

derive instance Eq CameraLookMode
derive instance Generic CameraLookMode _
instance Show CameraLookMode where show = genericShow

cameraLookModeFromString :: String -> Maybe CameraLookMode
cameraLookModeFromString = case _ of
  "tangent" -> Just LookTangent
  "target" -> Just LookTarget
  "fixed" -> Just LookFixed
  _ -> Nothing

data CameraShakeType = ShakeHandheld | ShakeImpact | ShakeEarthquake | ShakeSubtle | ShakeCustom

derive instance Eq CameraShakeType
derive instance Generic CameraShakeType _
instance Show CameraShakeType where show = genericShow

cameraShakeTypeFromString :: String -> Maybe CameraShakeType
cameraShakeTypeFromString = case _ of
  "handheld" -> Just ShakeHandheld
  "impact" -> Just ShakeImpact
  "earthquake" -> Just ShakeEarthquake
  "subtle" -> Just ShakeSubtle
  "custom" -> Just ShakeCustom
  _ -> Nothing

data RackFocusEasing = RfLinear | RfEaseIn | RfEaseOut | RfEaseInOut | RfSnap

derive instance Eq RackFocusEasing
derive instance Generic RackFocusEasing _
instance Show RackFocusEasing where show = genericShow

rackFocusEasingFromString :: String -> Maybe RackFocusEasing
rackFocusEasingFromString = case _ of
  "linear" -> Just RfLinear
  "ease-in" -> Just RfEaseIn
  "ease-out" -> Just RfEaseOut
  "ease-in-out" -> Just RfEaseInOut
  "snap" -> Just RfSnap
  _ -> Nothing

data AutoFocusMode = AfCenter | AfPoint | AfNearest | AfFarthest

derive instance Eq AutoFocusMode
derive instance Generic AutoFocusMode _
instance Show AutoFocusMode where show = genericShow

autoFocusModeFromString :: String -> Maybe AutoFocusMode
autoFocusModeFromString = case _ of
  "center" -> Just AfCenter
  "point" -> Just AfPoint
  "nearest" -> Just AfNearest
  "farthest" -> Just AfFarthest
  _ -> Nothing

--------------------------------------------------------------------------------
-- Light Layer
--------------------------------------------------------------------------------

data LightType = LightPoint | LightSpot | LightDirectional | LightAmbient

derive instance Eq LightType
derive instance Generic LightType _
instance Show LightType where show = genericShow

lightTypeFromString :: String -> Maybe LightType
lightTypeFromString = case _ of
  "point" -> Just LightPoint
  "spot" -> Just LightSpot
  "directional" -> Just LightDirectional
  "ambient" -> Just LightAmbient
  _ -> Nothing

data LightFalloff = FalloffNone | FalloffLinear | FalloffQuadratic | FalloffSmooth

derive instance Eq LightFalloff
derive instance Generic LightFalloff _
instance Show LightFalloff where show = genericShow

lightFalloffFromString :: String -> Maybe LightFalloff
lightFalloffFromString = case _ of
  "none" -> Just FalloffNone
  "linear" -> Just FalloffLinear
  "quadratic" -> Just FalloffQuadratic
  "smooth" -> Just FalloffSmooth
  _ -> Nothing

--------------------------------------------------------------------------------
-- Pose Layer
--------------------------------------------------------------------------------

data PoseFormat = PoseCoco18 | PoseBody25 | PoseCustom

derive instance Eq PoseFormat
derive instance Generic PoseFormat _
instance Show PoseFormat where show = genericShow

poseFormatFromString :: String -> Maybe PoseFormat
poseFormatFromString = case _ of
  "coco18" -> Just PoseCoco18
  "body25" -> Just PoseBody25
  "custom" -> Just PoseCustom
  _ -> Nothing

--------------------------------------------------------------------------------
-- Model Layer
--------------------------------------------------------------------------------

data ModelType = ModelGltf | ModelObj | ModelFbx | ModelUsd

derive instance Eq ModelType
derive instance Generic ModelType _
instance Show ModelType where show = genericShow

modelTypeFromString :: String -> Maybe ModelType
modelTypeFromString = case _ of
  "gltf" -> Just ModelGltf
  "obj" -> Just ModelObj
  "fbx" -> Just ModelFbx
  "usd" -> Just ModelUsd
  _ -> Nothing

--------------------------------------------------------------------------------
-- Point Cloud Layer
--------------------------------------------------------------------------------

data PointCloudFormat = PcPly | PcPcd | PcLas | PcXyz

derive instance Eq PointCloudFormat
derive instance Generic PointCloudFormat _
instance Show PointCloudFormat where show = genericShow

pointCloudFormatFromString :: String -> Maybe PointCloudFormat
pointCloudFormatFromString = case _ of
  "ply" -> Just PcPly
  "pcd" -> Just PcPcd
  "las" -> Just PcLas
  "xyz" -> Just PcXyz
  _ -> Nothing

data PointCloudColorMode = PcRgb | PcHeight | PcIntensity | PcClassification

derive instance Eq PointCloudColorMode
derive instance Generic PointCloudColorMode _
instance Show PointCloudColorMode where show = genericShow

pointCloudColorModeFromString :: String -> Maybe PointCloudColorMode
pointCloudColorModeFromString = case _ of
  "rgb" -> Just PcRgb
  "height" -> Just PcHeight
  "intensity" -> Just PcIntensity
  "classification" -> Just PcClassification
  _ -> Nothing

--------------------------------------------------------------------------------
-- Matte Layer
--------------------------------------------------------------------------------

data MatteType = MatteLum | MatteAlpha | MatteRed | MatteGreen | MatteBlue | MatteHue | MatteSat

derive instance Eq MatteType
derive instance Generic MatteType _
instance Show MatteType where show = genericShow

matteTypeFromString :: String -> Maybe MatteType
matteTypeFromString = case _ of
  "luminance" -> Just MatteLum
  "alpha" -> Just MatteAlpha
  "red" -> Just MatteRed
  "green" -> Just MatteGreen
  "blue" -> Just MatteBlue
  "hue" -> Just MatteHue
  "saturation" -> Just MatteSat
  _ -> Nothing

data MattePreviewMode = PreviewMatte | PreviewComposite | PreviewOverlay

derive instance Eq MattePreviewMode
derive instance Generic MattePreviewMode _
instance Show MattePreviewMode where show = genericShow

mattePreviewModeFromString :: String -> Maybe MattePreviewMode
mattePreviewModeFromString = case _ of
  "matte" -> Just PreviewMatte
  "composite" -> Just PreviewComposite
  "overlay" -> Just PreviewOverlay
  _ -> Nothing

--------------------------------------------------------------------------------
-- Procedural Matte
--------------------------------------------------------------------------------

data ProceduralMatteType
  = PmLinearGrad | PmRadialGrad | PmAngularGrad | PmRamp | PmNoise
  | PmCheckerboard | PmCircle | PmRectangle | PmGrid | PmWave
  | PmVenetianBlinds | PmIris | PmRadialWipe | PmDissolve

derive instance Eq ProceduralMatteType
derive instance Generic ProceduralMatteType _
instance Show ProceduralMatteType where show = genericShow

proceduralMatteTypeFromString :: String -> Maybe ProceduralMatteType
proceduralMatteTypeFromString = case _ of
  "linear_gradient" -> Just PmLinearGrad
  "radial_gradient" -> Just PmRadialGrad
  "angular_gradient" -> Just PmAngularGrad
  "ramp" -> Just PmRamp
  "noise" -> Just PmNoise
  "checkerboard" -> Just PmCheckerboard
  "circle" -> Just PmCircle
  "rectangle" -> Just PmRectangle
  "grid" -> Just PmGrid
  "wave" -> Just PmWave
  "venetian_blinds" -> Just PmVenetianBlinds
  "iris" -> Just PmIris
  "radial_wipe" -> Just PmRadialWipe
  "dissolve" -> Just PmDissolve
  _ -> Nothing

data WaveType = WaveSine | WaveTriangle | WaveSquare | WaveSawtooth

derive instance Eq WaveType
derive instance Generic WaveType _
instance Show WaveType where show = genericShow

waveTypeFromString :: String -> Maybe WaveType
waveTypeFromString = case _ of
  "sine" -> Just WaveSine
  "triangle" -> Just WaveTriangle
  "square" -> Just WaveSquare
  "sawtooth" -> Just WaveSawtooth
  _ -> Nothing

--------------------------------------------------------------------------------
-- Depthflow Layer
--------------------------------------------------------------------------------

data DepthflowPreset
  = DfStatic | DfZoomIn | DfZoomOut | DfDollyZoomIn | DfDollyZoomOut
  | DfPanLeft | DfPanRight | DfPanUp | DfPanDown
  | DfCircleCW | DfCircleCCW | DfHorizSwing | DfVertSwing | DfCustom

derive instance Eq DepthflowPreset
derive instance Generic DepthflowPreset _
instance Show DepthflowPreset where show = genericShow

depthflowPresetFromString :: String -> Maybe DepthflowPreset
depthflowPresetFromString = case _ of
  "static" -> Just DfStatic
  "zoom_in" -> Just DfZoomIn
  "zoom_out" -> Just DfZoomOut
  "dolly_zoom_in" -> Just DfDollyZoomIn
  "dolly_zoom_out" -> Just DfDollyZoomOut
  "pan_left" -> Just DfPanLeft
  "pan_right" -> Just DfPanRight
  "pan_up" -> Just DfPanUp
  "pan_down" -> Just DfPanDown
  "circle_cw" -> Just DfCircleCW
  "circle_ccw" -> Just DfCircleCCW
  "horizontal_swing" -> Just DfHorizSwing
  "vertical_swing" -> Just DfVertSwing
  "custom" -> Just DfCustom
  _ -> Nothing
