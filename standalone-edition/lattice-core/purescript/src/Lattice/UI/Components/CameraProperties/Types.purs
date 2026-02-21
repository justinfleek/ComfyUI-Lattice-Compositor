-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- camera-properties // types
-- all type definitions for the camera properties panel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.CameraProperties.Types
  ( -- ── input/output ──
    Input
  , Output(..)
  , Query
  , Slot
  , State
  , Action(..)
  , Slots
  , ExpandedSections
    -- ── camera types ──
  , Camera3D
  , Vec3
  , CameraType(..)
  , AutoOrientMode(..)
  , MeasureFilmSize(..)
  , DepthOfFieldSettings
  , IrisSettings
  , HighlightSettings
    -- ── trajectory types ──
  , TrajectoryType(..)
  , TrajectoryConfig
  , EasingMode(..)
    -- ── shake types ──
  , ShakeType(..)
  , ShakeConfig
    -- ── presets ──
  , CameraPreset
  , cameraPresets
    -- ── parsers ──
  , parseCameraType
  , parseAutoOrient
  , parseMeasureFilmSize
  , parseTrajectoryType
  , parseEasingMode
  , parseShakeType
    -- ── labels ──
  , cameraTypeLabel
  , autoOrientLabel
  , trajectoryLabel
  , trajectoryDescription
  , shakeLabel
  , shakeDescription
    -- ── helpers ──
  , isOrbitalTrajectory
  , allTrajectoryTypes
    -- ── defaults ──
  , defaultExpandedSections
  , defaultTrajectoryConfig
  , defaultShakeConfig
  ) where

import Prelude

import Data.Array (elem)
import Data.Maybe (Maybe)
import Halogen as H

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // component types
-- ═══════════════════════════════════════════════════════════════════════════

type Input =
  { camera :: Maybe Camera3D
  , cameraName :: String
  }

data Output
  = CameraUpdated Camera3D
  | CreateCameraRequested
  | PreviewTrajectoryRequested TrajectoryConfig
  | ApplyTrajectoryRequested TrajectoryConfig
  | PreviewShakeRequested ShakeConfig
  | ApplyShakeRequested ShakeConfig

data Query a

type Slot id = H.Slot Query Output id

type State =
  { camera :: Maybe Camera3D
  , cameraName :: String
  , expandedSections :: ExpandedSections
  , trajectoryConfig :: TrajectoryConfig
  , shakeConfig :: ShakeConfig
  }

type ExpandedSections =
  { transform :: Boolean
  , lens :: Boolean
  , dof :: Boolean
  , iris :: Boolean
  , highlight :: Boolean
  , autoOrient :: Boolean
  , clipping :: Boolean
  , trajectory :: Boolean
  , shake :: Boolean
  }

data Action
  = Initialize
  | Receive Input
  | ToggleSection String
  -- camera properties
  | SetCameraType String
  | SetPositionX String | SetPositionY String | SetPositionZ String
  | SetPOIX String | SetPOIY String | SetPOIZ String
  | SetOrientationX String | SetOrientationY String | SetOrientationZ String
  | SetXRotation String | SetYRotation String | SetZRotation String
  | SetFocalLength String
  | SetAngleOfView String
  | SetFilmSize String
  | SetMeasureFilmSize String
  | ApplyPreset CameraPreset
  -- dof
  | ToggleDOF
  | SetFocusDistance String
  | SetFStop String
  | SetBlurLevel String
  | ToggleLockToZoom
  -- iris
  | SetIrisShape String
  | SetIrisRotation String
  | SetIrisRoundness String
  | SetIrisAspectRatio String
  | SetDiffractionFringe String
  -- highlight
  | SetHighlightGain String
  | SetHighlightThreshold String
  | SetHighlightSaturation String
  -- auto-orient & clipping
  | SetAutoOrient String
  | SetNearClip String
  | SetFarClip String
  -- trajectory
  | SetTrajectoryType String
  | SetTrajectoryDuration String
  | SetTrajectoryAmplitude String
  | SetTrajectoryLoops String
  | SetTrajectoryEasing String
  | ToggleAudioReactive
  | SetAudioFeature String
  | SetAudioSensitivity String
  | PreviewTrajectory
  | ApplyTrajectory
  -- shake
  | SetShakeType String
  | SetShakeIntensity String
  | SetShakeFrequency String
  | SetShakeDuration String
  | ToggleShakeRotation
  | SetShakeRotationScale String
  | SetShakeDecay String
  | SetShakeSeed String
  | PreviewShake
  | ApplyShake
  -- actions
  | CreateCamera

type Slots = ()

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // camera type
-- ═══════════════════════════════════════════════════════════════════════════

type Camera3D =
  { id :: String
  , name :: String
  , cameraType :: CameraType
  , position :: Vec3
  , pointOfInterest :: Vec3
  , orientation :: Vec3
  , xRotation :: Number
  , yRotation :: Number
  , zRotation :: Number
  , focalLength :: Number
  , angleOfView :: Number
  , filmSize :: Number
  , measureFilmSize :: MeasureFilmSize
  , zoom :: Number
  , depthOfField :: DepthOfFieldSettings
  , iris :: IrisSettings
  , highlight :: HighlightSettings
  , autoOrient :: AutoOrientMode
  , nearClip :: Number
  , farClip :: Number
  }

type Vec3 = { x :: Number, y :: Number, z :: Number }

data CameraType = OneNode | TwoNode

derive instance eqCameraType :: Eq CameraType

instance showCameraType :: Show CameraType where
  show = case _ of
    OneNode -> "one-node"
    TwoNode -> "two-node"

cameraTypeLabel :: CameraType -> String
cameraTypeLabel = case _ of
  OneNode -> "One-Node Camera"
  TwoNode -> "Two-Node Camera"

parseCameraType :: String -> CameraType
parseCameraType = case _ of
  "two-node" -> TwoNode
  _ -> OneNode

data AutoOrientMode
  = AutoOrientOff
  | OrientAlongPath
  | OrientTowardsPOI

derive instance eqAutoOrientMode :: Eq AutoOrientMode

instance showAutoOrientMode :: Show AutoOrientMode where
  show = case _ of
    AutoOrientOff -> "off"
    OrientAlongPath -> "orient-along-path"
    OrientTowardsPOI -> "orient-towards-poi"

autoOrientLabel :: AutoOrientMode -> String
autoOrientLabel = case _ of
  AutoOrientOff -> "Off"
  OrientAlongPath -> "Orient Along Path"
  OrientTowardsPOI -> "Orient Towards Point of Interest"

parseAutoOrient :: String -> AutoOrientMode
parseAutoOrient = case _ of
  "orient-along-path" -> OrientAlongPath
  "orient-towards-poi" -> OrientTowardsPOI
  _ -> AutoOrientOff

data MeasureFilmSize = Horizontal | Vertical | Diagonal

derive instance eqMeasureFilmSize :: Eq MeasureFilmSize

instance showMeasureFilmSize :: Show MeasureFilmSize where
  show = case _ of
    Horizontal -> "horizontal"
    Vertical -> "vertical"
    Diagonal -> "diagonal"

parseMeasureFilmSize :: String -> MeasureFilmSize
parseMeasureFilmSize = case _ of
  "vertical" -> Vertical
  "diagonal" -> Diagonal
  _ -> Horizontal

type DepthOfFieldSettings =
  { enabled :: Boolean
  , focusDistance :: Number
  , fStop :: Number
  , blurLevel :: Number
  , lockToZoom :: Boolean
  }

type IrisSettings =
  { shape :: Int
  , rotation :: Number
  , roundness :: Number
  , aspectRatio :: Number
  , diffractionFringe :: Number
  }

type HighlightSettings =
  { gain :: Number
  , threshold :: Number
  , saturation :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                           // trajectory types
-- ═══════════════════════════════════════════════════════════════════════════

data TrajectoryType
  = TrajectoryOrbit
  | TrajectoryOrbitReverse
  | TrajectoryCircle
  | TrajectoryFigure8
  | TrajectorySpiralIn
  | TrajectorySpiralOut
  | TrajectoryPan
  | TrajectoryTilt
  | TrajectoryPush
  | TrajectoryPull
  | TrajectoryRoll
  | TrajectoryTruck
  | TrajectoryPedestal
  | TrajectoryDollyZoom
  | TrajectoryWobble
  | TrajectoryFloat
  | TrajectoryShake

derive instance eqTrajectoryType :: Eq TrajectoryType

instance showTrajectoryType :: Show TrajectoryType where
  show = case _ of
    TrajectoryOrbit -> "orbit"
    TrajectoryOrbitReverse -> "orbit_reverse"
    TrajectoryCircle -> "circle"
    TrajectoryFigure8 -> "figure8"
    TrajectorySpiralIn -> "spiral_in"
    TrajectorySpiralOut -> "spiral_out"
    TrajectoryPan -> "pan"
    TrajectoryTilt -> "tilt"
    TrajectoryPush -> "push"
    TrajectoryPull -> "pull"
    TrajectoryRoll -> "roll"
    TrajectoryTruck -> "truck"
    TrajectoryPedestal -> "pedestal"
    TrajectoryDollyZoom -> "dolly_zoom"
    TrajectoryWobble -> "wobble"
    TrajectoryFloat -> "float"
    TrajectoryShake -> "shake"

trajectoryLabel :: TrajectoryType -> String
trajectoryLabel = case _ of
  TrajectoryOrbit -> "Orbit"
  TrajectoryOrbitReverse -> "Orbit Reverse"
  TrajectoryCircle -> "Circle"
  TrajectoryFigure8 -> "Figure 8"
  TrajectorySpiralIn -> "Spiral In"
  TrajectorySpiralOut -> "Spiral Out"
  TrajectoryPan -> "Pan"
  TrajectoryTilt -> "Tilt"
  TrajectoryPush -> "Push"
  TrajectoryPull -> "Pull"
  TrajectoryRoll -> "Roll"
  TrajectoryTruck -> "Truck"
  TrajectoryPedestal -> "Pedestal"
  TrajectoryDollyZoom -> "Dolly Zoom"
  TrajectoryWobble -> "Wobble"
  TrajectoryFloat -> "Float"
  TrajectoryShake -> "Shake"

trajectoryDescription :: TrajectoryType -> String
trajectoryDescription = case _ of
  TrajectoryOrbit -> "Rotates camera around the point of interest in a circular arc"
  TrajectoryOrbitReverse -> "Rotates camera around POI in reverse direction"
  TrajectoryCircle -> "Full 360-degree rotation around the subject"
  TrajectoryFigure8 -> "Creates a smooth figure-8 pattern for dynamic movement"
  TrajectorySpiralIn -> "Spirals inward toward the point of interest"
  TrajectorySpiralOut -> "Spirals outward from the point of interest"
  TrajectoryPan -> "Rotates the camera horizontally on its axis"
  TrajectoryTilt -> "Rotates the camera vertically on its axis"
  TrajectoryPush -> "Moves camera toward the subject (push in)"
  TrajectoryPull -> "Moves camera away from the subject (pull back)"
  TrajectoryRoll -> "Rotates camera along its view axis"
  TrajectoryTruck -> "Moves camera left or right perpendicular to view"
  TrajectoryPedestal -> "Moves camera up or down vertically"
  TrajectoryDollyZoom -> "Classic vertigo effect - dolly while zooming"
  TrajectoryWobble -> "Subtle organic camera wobble"
  TrajectoryFloat -> "Gentle floating motion with slight drift"
  TrajectoryShake -> "Intense camera shake for impact"

parseTrajectoryType :: String -> TrajectoryType
parseTrajectoryType = case _ of
  "orbit_reverse" -> TrajectoryOrbitReverse
  "circle" -> TrajectoryCircle
  "figure8" -> TrajectoryFigure8
  "spiral_in" -> TrajectorySpiralIn
  "spiral_out" -> TrajectorySpiralOut
  "pan" -> TrajectoryPan
  "tilt" -> TrajectoryTilt
  "push" -> TrajectoryPush
  "pull" -> TrajectoryPull
  "roll" -> TrajectoryRoll
  "truck" -> TrajectoryTruck
  "pedestal" -> TrajectoryPedestal
  "dolly_zoom" -> TrajectoryDollyZoom
  "wobble" -> TrajectoryWobble
  "float" -> TrajectoryFloat
  "shake" -> TrajectoryShake
  _ -> TrajectoryOrbit

isOrbitalTrajectory :: TrajectoryType -> Boolean
isOrbitalTrajectory t = t `elem` 
  [TrajectoryOrbit, TrajectoryOrbitReverse, TrajectoryCircle, 
   TrajectoryFigure8, TrajectorySpiralIn, TrajectorySpiralOut]

allTrajectoryTypes :: Array TrajectoryType
allTrajectoryTypes =
  [ TrajectoryOrbit, TrajectoryOrbitReverse, TrajectoryCircle, TrajectoryFigure8
  , TrajectorySpiralIn, TrajectorySpiralOut, TrajectoryPan, TrajectoryTilt
  , TrajectoryPush, TrajectoryPull, TrajectoryRoll, TrajectoryTruck
  , TrajectoryPedestal, TrajectoryDollyZoom, TrajectoryWobble, TrajectoryFloat
  , TrajectoryShake
  ]

type TrajectoryConfig =
  { trajectoryType :: TrajectoryType
  , duration :: Int
  , amplitude :: Number
  , loops :: Number
  , easing :: EasingMode
  , audioReactive :: Boolean
  , audioFeature :: String
  , audioSensitivity :: Number
  }

data EasingMode
  = EasingLinear
  | EasingEaseIn
  | EasingEaseOut
  | EasingEaseInOut
  | EasingBounce

derive instance eqEasingMode :: Eq EasingMode

instance showEasingMode :: Show EasingMode where
  show = case _ of
    EasingLinear -> "linear"
    EasingEaseIn -> "ease-in"
    EasingEaseOut -> "ease-out"
    EasingEaseInOut -> "ease-in-out"
    EasingBounce -> "bounce"

parseEasingMode :: String -> EasingMode
parseEasingMode = case _ of
  "ease-in" -> EasingEaseIn
  "ease-out" -> EasingEaseOut
  "ease-in-out" -> EasingEaseInOut
  "bounce" -> EasingBounce
  _ -> EasingLinear

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // shake types
-- ═══════════════════════════════════════════════════════════════════════════

data ShakeType
  = ShakeHandheld
  | ShakeSubtle
  | ShakeImpact
  | ShakeEarthquake
  | ShakeCustom

derive instance eqShakeType :: Eq ShakeType

instance showShakeType :: Show ShakeType where
  show = case _ of
    ShakeHandheld -> "handheld"
    ShakeSubtle -> "subtle"
    ShakeImpact -> "impact"
    ShakeEarthquake -> "earthquake"
    ShakeCustom -> "custom"

shakeLabel :: ShakeType -> String
shakeLabel = case _ of
  ShakeHandheld -> "Handheld"
  ShakeSubtle -> "Subtle"
  ShakeImpact -> "Impact"
  ShakeEarthquake -> "Earthquake"
  ShakeCustom -> "Custom"

shakeDescription :: ShakeType -> String
shakeDescription = case _ of
  ShakeHandheld -> "Simulates natural handheld camera movement"
  ShakeSubtle -> "Gentle shake for atmospheric tension"
  ShakeImpact -> "Sharp, sudden shake for impacts or explosions"
  ShakeEarthquake -> "Violent, sustained shaking"
  ShakeCustom -> "Custom shake parameters"

parseShakeType :: String -> ShakeType
parseShakeType = case _ of
  "subtle" -> ShakeSubtle
  "impact" -> ShakeImpact
  "earthquake" -> ShakeEarthquake
  "custom" -> ShakeCustom
  _ -> ShakeHandheld

type ShakeConfig =
  { shakeType :: ShakeType
  , intensity :: Number
  , frequency :: Number
  , duration :: Int
  , rotationEnabled :: Boolean
  , rotationScale :: Number
  , decay :: Number
  , seed :: Int
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                             // lens presets
-- ═══════════════════════════════════════════════════════════════════════════

type CameraPreset =
  { name :: String
  , focalLength :: Number
  , angleOfView :: Number
  , zoom :: Number
  }

cameraPresets :: Array CameraPreset
cameraPresets =
  [ { name: "Wide", focalLength: 24.0, angleOfView: 84.0, zoom: 1.0 }
  , { name: "35mm", focalLength: 35.0, angleOfView: 63.0, zoom: 1.0 }
  , { name: "50mm", focalLength: 50.0, angleOfView: 46.0, zoom: 1.0 }
  , { name: "85mm", focalLength: 85.0, angleOfView: 28.0, zoom: 1.0 }
  , { name: "Tele", focalLength: 200.0, angleOfView: 12.0, zoom: 1.0 }
  ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // defaults
-- ═══════════════════════════════════════════════════════════════════════════

defaultExpandedSections :: ExpandedSections
defaultExpandedSections =
  { transform: true
  , lens: true
  , dof: false
  , iris: false
  , highlight: false
  , autoOrient: false
  , clipping: false
  , trajectory: false
  , shake: false
  }

defaultTrajectoryConfig :: TrajectoryConfig
defaultTrajectoryConfig =
  { trajectoryType: TrajectoryOrbit
  , duration: 81
  , amplitude: 1.0
  , loops: 1.0
  , easing: EasingLinear
  , audioReactive: false
  , audioFeature: "amplitude"
  , audioSensitivity: 1.0
  }

defaultShakeConfig :: ShakeConfig
defaultShakeConfig =
  { shakeType: ShakeHandheld
  , intensity: 0.3
  , frequency: 1.0
  , duration: 81
  , rotationEnabled: false
  , rotationScale: 1.0
  , decay: 0.0
  , seed: 12345
  }
