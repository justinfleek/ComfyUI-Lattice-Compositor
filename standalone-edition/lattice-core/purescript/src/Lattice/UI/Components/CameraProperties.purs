-- | Camera Properties Panel Component
-- |
-- | Full-featured camera properties editor for 3D camera layers.
-- | Features:
-- | - Camera type (one-node/two-node)
-- | - Transform: position, orientation, point of interest
-- | - Lens: focal length, angle of view, film size, presets
-- | - Depth of Field: focus distance, f-stop, blur level
-- | - Iris: shape, rotation, roundness, aspect ratio, diffraction
-- | - Highlight: gain, threshold, saturation
-- | - Auto-orient modes
-- | - Clipping planes
-- | - Camera trajectory (Uni3C-style motion presets)
-- | - Camera shake with presets
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/CameraProperties.vue
module Lattice.UI.Components.CameraProperties
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , Camera3D
  , CameraType(..)
  , AutoOrientMode(..)
  , MeasureFilmSize(..)
  , TrajectoryType(..)
  , ShakeType(..)
  , EasingMode(..)
  ) where

import Prelude

import Data.Array (filter, elem)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (abs)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls)
import Lattice.UI.Utils as Utils

-- =============================================================================
--                                                                      // types
-- =============================================================================

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

-- =============================================================================
--                                                                // camera type
-- =============================================================================

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

-- =============================================================================
--                                                             // trajectory types
-- =============================================================================

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

-- =============================================================================
--                                                                // shake types
-- =============================================================================

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

-- =============================================================================
--                                                               // lens presets
-- =============================================================================

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

-- =============================================================================
--                                                                     // state
-- =============================================================================

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
  -- Camera properties
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
  -- DOF
  | ToggleDOF
  | SetFocusDistance String
  | SetFStop String
  | SetBlurLevel String
  | ToggleLockToZoom
  -- Iris
  | SetIrisShape String
  | SetIrisRotation String
  | SetIrisRoundness String
  | SetIrisAspectRatio String
  | SetDiffractionFringe String
  -- Highlight
  | SetHighlightGain String
  | SetHighlightThreshold String
  | SetHighlightSaturation String
  -- Auto-Orient & Clipping
  | SetAutoOrient String
  | SetNearClip String
  | SetFarClip String
  -- Trajectory
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
  -- Shake
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
  -- Actions
  | CreateCamera

type Slots = ()

-- =============================================================================
--                                                                  // component
-- =============================================================================

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
  { camera: input.camera
  , cameraName: input.cameraName
  , expandedSections: defaultExpandedSections
  , trajectoryConfig: defaultTrajectoryConfig
  , shakeConfig: defaultShakeConfig
  }

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

-- =============================================================================
--                                                                     // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "camera-properties" ]
    , HP.attr (HH.AttrName "style") panelStyle
    ]
    [ renderHeader state
    , case state.camera of
        Just cam -> renderPropertiesContent state cam
        Nothing -> renderNoCamera
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.span [ cls [ "panel-title" ] ] [ HH.text "Camera" ]
    , HH.span [ cls [ "camera-name" ], HP.attr (HH.AttrName "style") cameraNameStyle ]
        [ HH.text state.cameraName ]
    ]

renderNoCamera :: forall m. H.ComponentHTML Action Slots m
renderNoCamera =
  HH.div
    [ cls [ "no-camera" ]
    , HP.attr (HH.AttrName "style") noCameraStyle
    ]
    [ HH.p_ [ HH.text "No camera selected" ]
    , HH.button
        [ cls [ "create-camera-btn" ]
        , HP.attr (HH.AttrName "style") createBtnStyle
        , HE.onClick \_ -> CreateCamera
        ]
        [ HH.text "Create Camera" ]
    ]

renderPropertiesContent :: forall m. State -> Camera3D -> H.ComponentHTML Action Slots m
renderPropertiesContent state cam =
  HH.div
    [ cls [ "properties-content" ]
    , HP.attr (HH.AttrName "style") contentStyle
    ]
    [ renderTypeSection cam
    , renderTransformSection state cam
    , renderLensSection state cam
    , renderDOFSection state cam
    , renderIrisSection state cam
    , renderHighlightSection state cam
    , renderAutoOrientSection state cam
    , renderClippingSection state cam
    , renderTrajectorySection state
    , renderShakeSection state
    ]

renderTypeSection :: forall m. Camera3D -> H.ComponentHTML Action Slots m
renderTypeSection cam =
  HH.div
    [ cls [ "property-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div [ cls [ "section-header" ] ] [ HH.text "Type" ]
    , HH.div [ cls [ "property-row" ] ]
        [ HH.select
            [ cls [ "type-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetCameraType
            ]
            [ HH.option [ HP.value "one-node", HP.selected (cam.cameraType == OneNode) ]
                [ HH.text "One-Node Camera" ]
            , HH.option [ HP.value "two-node", HP.selected (cam.cameraType == TwoNode) ]
                [ HH.text "Two-Node Camera" ]
            ]
        ]
    ]

renderTransformSection :: forall m. State -> Camera3D -> H.ComponentHTML Action Slots m
renderTransformSection state cam =
  collapsibleSection "Transform" "transform" state.expandedSections.transform
    [ -- Position
      propertyGroup "Position"
        [ xyzInputs
            [ { label: "X", value: cam.position.x, onInput: SetPositionX }
            , { label: "Y", value: cam.position.y, onInput: SetPositionY }
            , { label: "Z", value: cam.position.z, onInput: SetPositionZ }
            ]
        ]
    
    -- Point of Interest (two-node only)
    , if cam.cameraType == TwoNode
        then propertyGroup "Point of Interest"
          [ xyzInputs
              [ { label: "X", value: cam.pointOfInterest.x, onInput: SetPOIX }
              , { label: "Y", value: cam.pointOfInterest.y, onInput: SetPOIY }
              , { label: "Z", value: cam.pointOfInterest.z, onInput: SetPOIZ }
              ]
          ]
        else HH.text ""
    
    -- Orientation
    , propertyGroup "Orientation"
        [ xyzInputs
            [ { label: "X", value: cam.orientation.x, onInput: SetOrientationX }
            , { label: "Y", value: cam.orientation.y, onInput: SetOrientationY }
            , { label: "Z", value: cam.orientation.z, onInput: SetOrientationZ }
            ]
        ]
    
    -- Individual rotations
    , propertyGroup "X Rotation"
        [ numberInput cam.xRotation "\x{00B0}" SetXRotation ]
    , propertyGroup "Y Rotation"
        [ numberInput cam.yRotation "\x{00B0}" SetYRotation ]
    , propertyGroup "Z Rotation"
        [ numberInput cam.zRotation "\x{00B0}" SetZRotation ]
    ]

renderLensSection :: forall m. State -> Camera3D -> H.ComponentHTML Action Slots m
renderLensSection state cam =
  collapsibleSection "Lens" "lens" state.expandedSections.lens
    [ -- Preset buttons
      HH.div [ cls [ "preset-row" ], HP.attr (HH.AttrName "style") presetRowStyle ]
        (map (presetButton cam.focalLength) cameraPresets)
    
    -- Focal Length
    , propertyGroup "Focal Length"
        [ numberInput cam.focalLength "mm" SetFocalLength ]
    
    -- Angle of View
    , propertyGroup "Angle of View"
        [ numberInput cam.angleOfView "\x{00B0}" SetAngleOfView ]
    
    -- Film Size
    , propertyGroup "Film Size"
        [ numberInput cam.filmSize "mm" SetFilmSize ]
    
    -- Measure Film Size
    , propertyGroup "Measure Film Size"
        [ HH.select
            [ cls [ "settings-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetMeasureFilmSize
            ]
            [ HH.option [ HP.value "horizontal", HP.selected (cam.measureFilmSize == Horizontal) ]
                [ HH.text "Horizontal" ]
            , HH.option [ HP.value "vertical", HP.selected (cam.measureFilmSize == Vertical) ]
                [ HH.text "Vertical" ]
            , HH.option [ HP.value "diagonal", HP.selected (cam.measureFilmSize == Diagonal) ]
                [ HH.text "Diagonal" ]
            ]
        ]
    ]

presetButton :: forall m. Number -> CameraPreset -> H.ComponentHTML Action Slots m
presetButton currentFocal preset =
  let isActive = abs (currentFocal - preset.focalLength) < 0.5
  in HH.button
       [ cls [ "preset-btn" ]
       , HP.attr (HH.AttrName "style") (presetBtnStyle isActive)
       , HE.onClick \_ -> ApplyPreset preset
       ]
       [ HH.text preset.name ]

renderDOFSection :: forall m. State -> Camera3D -> H.ComponentHTML Action Slots m
renderDOFSection state cam =
  collapsibleSection "Depth of Field" "dof" state.expandedSections.dof
    [ checkboxRow "Enable DOF" cam.depthOfField.enabled ToggleDOF
    
    , if cam.depthOfField.enabled
        then HH.div_
          [ propertyGroup "Focus Distance"
              [ numberInput cam.depthOfField.focusDistance "px" SetFocusDistance ]
          , propertyGroup "f-Stop"
              [ numberInput cam.depthOfField.fStop "" SetFStop ]
          , propertyGroup "Blur Level"
              [ sliderInput cam.depthOfField.blurLevel 0.0 1.0 0.01 SetBlurLevel ]
          , checkboxRow "Lock to Zoom" cam.depthOfField.lockToZoom ToggleLockToZoom
          ]
        else HH.text ""
    ]

renderIrisSection :: forall m. State -> Camera3D -> H.ComponentHTML Action Slots m
renderIrisSection state cam =
  collapsibleSection "Iris" "iris" state.expandedSections.iris
    [ propertyGroup ("Shape (" <> show cam.iris.shape <> "-gon)")
        [ sliderInput (Utils.toNumber cam.iris.shape) 3.0 10.0 1.0 SetIrisShape ]
    , propertyGroup "Rotation"
        [ numberInput cam.iris.rotation "\x{00B0}" SetIrisRotation ]
    , propertyGroup "Roundness"
        [ sliderInput cam.iris.roundness 0.0 1.0 0.01 SetIrisRoundness ]
    , propertyGroup "Aspect Ratio"
        [ sliderInput cam.iris.aspectRatio 0.5 2.0 0.01 SetIrisAspectRatio ]
    , propertyGroup "Diffraction Fringe"
        [ sliderInput cam.iris.diffractionFringe 0.0 1.0 0.01 SetDiffractionFringe ]
    ]

renderHighlightSection :: forall m. State -> Camera3D -> H.ComponentHTML Action Slots m
renderHighlightSection state cam =
  collapsibleSection "Highlight" "highlight" state.expandedSections.highlight
    [ propertyGroup "Gain"
        [ sliderInput cam.highlight.gain 0.0 1.0 0.01 SetHighlightGain ]
    , propertyGroup "Threshold"
        [ sliderInput cam.highlight.threshold 0.0 1.0 0.01 SetHighlightThreshold ]
    , propertyGroup "Saturation"
        [ sliderInput cam.highlight.saturation 0.0 1.0 0.01 SetHighlightSaturation ]
    ]

renderAutoOrientSection :: forall m. State -> Camera3D -> H.ComponentHTML Action Slots m
renderAutoOrientSection state cam =
  collapsibleSection "Auto-Orient" "autoOrient" state.expandedSections.autoOrient
    [ propertyGroup ""
        [ HH.select
            [ cls [ "settings-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetAutoOrient
            ]
            [ HH.option [ HP.value "off", HP.selected (cam.autoOrient == AutoOrientOff) ]
                [ HH.text "Off" ]
            , HH.option [ HP.value "orient-along-path", HP.selected (cam.autoOrient == OrientAlongPath) ]
                [ HH.text "Orient Along Path" ]
            , HH.option [ HP.value "orient-towards-poi", HP.selected (cam.autoOrient == OrientTowardsPOI) ]
                [ HH.text "Orient Towards Point of Interest" ]
            ]
        ]
    ]

renderClippingSection :: forall m. State -> Camera3D -> H.ComponentHTML Action Slots m
renderClippingSection state cam =
  collapsibleSection "Clipping" "clipping" state.expandedSections.clipping
    [ propertyGroup "Near Clip"
        [ numberInput cam.nearClip "" SetNearClip ]
    , propertyGroup "Far Clip"
        [ numberInput cam.farClip "" SetFarClip ]
    ]

renderTrajectorySection :: forall m. State -> H.ComponentHTML Action Slots m
renderTrajectorySection state =
  let cfg = state.trajectoryConfig
  in collapsibleSection "Trajectory" "trajectory" state.expandedSections.trajectory
    [ -- Motion Preset
      propertyGroup "Motion Preset"
        [ HH.select
            [ cls [ "trajectory-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetTrajectoryType
            ]
            (map (trajectoryOption cfg.trajectoryType) allTrajectoryTypes)
        ]
    
    -- Description
    , HH.div [ cls [ "trajectory-description" ], HP.attr (HH.AttrName "style") descriptionStyle ]
        [ HH.text (trajectoryDescription cfg.trajectoryType) ]
    
    -- Duration
    , propertyGroup "Duration (frames)"
        [ numberInput (Utils.toNumber cfg.duration) "" SetTrajectoryDuration ]
    
    -- Amplitude
    , propertyGroup "Amplitude"
        [ sliderInput (abs cfg.amplitude) 0.1 2.0 0.1 SetTrajectoryAmplitude ]
    
    -- Loops (for orbital)
    , if isOrbitalTrajectory cfg.trajectoryType
        then propertyGroup "Loops"
          [ numberInput cfg.loops "" SetTrajectoryLoops ]
        else HH.text ""
    
    -- Easing
    , propertyGroup "Easing"
        [ HH.select
            [ cls [ "settings-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetTrajectoryEasing
            ]
            [ HH.option [ HP.value "linear", HP.selected (cfg.easing == EasingLinear) ] 
                [ HH.text "Linear" ]
            , HH.option [ HP.value "ease-in", HP.selected (cfg.easing == EasingEaseIn) ]
                [ HH.text "Ease In" ]
            , HH.option [ HP.value "ease-out", HP.selected (cfg.easing == EasingEaseOut) ]
                [ HH.text "Ease Out" ]
            , HH.option [ HP.value "ease-in-out", HP.selected (cfg.easing == EasingEaseInOut) ]
                [ HH.text "Ease In-Out" ]
            , HH.option [ HP.value "bounce", HP.selected (cfg.easing == EasingBounce) ]
                [ HH.text "Bounce" ]
            ]
        ]
    
    -- Audio Reactive
    , checkboxRow "Audio Reactive" cfg.audioReactive ToggleAudioReactive
    
    , if cfg.audioReactive
        then HH.div_
          [ propertyGroup "Audio Feature"
              [ HH.select
                  [ cls [ "settings-select" ]
                  , HP.attr (HH.AttrName "style") selectStyle
                  , HE.onValueChange SetAudioFeature
                  ]
                  [ HH.option [ HP.value "amplitude" ] [ HH.text "Amplitude" ]
                  , HH.option [ HP.value "bass" ] [ HH.text "Bass" ]
                  , HH.option [ HP.value "mid" ] [ HH.text "Mid" ]
                  , HH.option [ HP.value "high" ] [ HH.text "High" ]
                  , HH.option [ HP.value "onsets" ] [ HH.text "Onsets" ]
                  ]
              ]
          , propertyGroup "Sensitivity"
              [ sliderInput cfg.audioSensitivity 0.1 3.0 0.1 SetAudioSensitivity ]
          ]
        else HH.text ""
    
    -- Action buttons
    , HH.div [ cls [ "trajectory-actions" ], HP.attr (HH.AttrName "style") actionsStyle ]
        [ HH.button
            [ cls [ "action-btn", "preview" ]
            , HP.attr (HH.AttrName "style") previewBtnStyle
            , HE.onClick \_ -> PreviewTrajectory
            ]
            [ HH.text "Preview" ]
        , HH.button
            [ cls [ "action-btn", "apply" ]
            , HP.attr (HH.AttrName "style") applyBtnStyle
            , HE.onClick \_ -> ApplyTrajectory
            ]
            [ HH.text "Apply Keyframes" ]
        ]
    ]

allTrajectoryTypes :: Array TrajectoryType
allTrajectoryTypes =
  [ TrajectoryOrbit, TrajectoryOrbitReverse, TrajectoryCircle, TrajectoryFigure8
  , TrajectorySpiralIn, TrajectorySpiralOut, TrajectoryPan, TrajectoryTilt
  , TrajectoryPush, TrajectoryPull, TrajectoryRoll, TrajectoryTruck
  , TrajectoryPedestal, TrajectoryDollyZoom, TrajectoryWobble, TrajectoryFloat
  , TrajectoryShake
  ]

trajectoryOption :: forall m. TrajectoryType -> TrajectoryType -> H.ComponentHTML Action Slots m
trajectoryOption current opt =
  HH.option 
    [ HP.value (show opt), HP.selected (current == opt) ]
    [ HH.text (trajectoryLabel opt) ]

renderShakeSection :: forall m. State -> H.ComponentHTML Action Slots m
renderShakeSection state =
  let cfg = state.shakeConfig
  in collapsibleSection "Camera Shake" "shake" state.expandedSections.shake
    [ -- Preset
      propertyGroup "Preset"
        [ HH.select
            [ cls [ "settings-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetShakeType
            ]
            [ HH.option [ HP.value "handheld", HP.selected (cfg.shakeType == ShakeHandheld) ]
                [ HH.text "Handheld" ]
            , HH.option [ HP.value "subtle", HP.selected (cfg.shakeType == ShakeSubtle) ]
                [ HH.text "Subtle" ]
            , HH.option [ HP.value "impact", HP.selected (cfg.shakeType == ShakeImpact) ]
                [ HH.text "Impact" ]
            , HH.option [ HP.value "earthquake", HP.selected (cfg.shakeType == ShakeEarthquake) ]
                [ HH.text "Earthquake" ]
            , HH.option [ HP.value "custom", HP.selected (cfg.shakeType == ShakeCustom) ]
                [ HH.text "Custom" ]
            ]
        ]
    
    -- Description
    , HH.div [ cls [ "shake-description" ], HP.attr (HH.AttrName "style") descriptionStyle ]
        [ HH.text (shakeDescription cfg.shakeType) ]
    
    -- Intensity
    , propertyGroup "Intensity"
        [ sliderInput cfg.intensity 0.0 1.0 0.05 SetShakeIntensity ]
    
    -- Frequency
    , propertyGroup "Frequency"
        [ sliderInput cfg.frequency 0.1 5.0 0.1 SetShakeFrequency ]
    
    -- Duration
    , propertyGroup "Duration (frames)"
        [ numberInput (Utils.toNumber cfg.duration) "" SetShakeDuration ]
    
    -- Rotation Shake
    , checkboxRow "Rotation Shake" cfg.rotationEnabled ToggleShakeRotation
    
    , if cfg.rotationEnabled
        then propertyGroup "Rotation Scale"
          [ sliderInput cfg.rotationScale 0.0 2.0 0.1 SetShakeRotationScale ]
        else HH.text ""
    
    -- Decay
    , propertyGroup "Decay"
        [ sliderInput cfg.decay 0.0 1.0 0.05 SetShakeDecay ]
    
    -- Seed
    , propertyGroup "Seed"
        [ numberInput (Utils.toNumber cfg.seed) "" SetShakeSeed ]
    
    -- Action buttons
    , HH.div [ cls [ "shake-actions" ], HP.attr (HH.AttrName "style") actionsStyle ]
        [ HH.button
            [ cls [ "action-btn", "preview" ]
            , HP.attr (HH.AttrName "style") previewBtnStyle
            , HE.onClick \_ -> PreviewShake
            ]
            [ HH.text "Preview" ]
        , HH.button
            [ cls [ "action-btn", "apply" ]
            , HP.attr (HH.AttrName "style") applyBtnStyle
            , HE.onClick \_ -> ApplyShake
            ]
            [ HH.text "Apply Keyframes" ]
        ]
    ]

-- =============================================================================
--                                                               // ui helpers
-- =============================================================================

collapsibleSection :: forall m. String -> String -> Boolean -> Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
collapsibleSection title sectionId isExpanded children =
  HH.div
    [ cls [ "property-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div
        [ cls [ "section-header" ]
        , HP.attr (HH.AttrName "style") sectionHeaderStyle
        , HE.onClick \_ -> ToggleSection sectionId
        , ARIA.role "button"
        , HP.attr (HH.AttrName "aria-expanded") (if isExpanded then "true" else "false")
        ]
        [ HH.span [ cls [ "toggle-icon" ], HP.attr (HH.AttrName "style") toggleIconStyle ]
            [ HH.text (if isExpanded then "\x{25BC}" else "\x{25B6}") ]
        , HH.text title
        ]
    , if isExpanded
        then HH.div [ cls [ "section-content" ], HP.attr (HH.AttrName "style") sectionContentStyle ]
               children
        else HH.text ""
    ]

propertyGroup :: forall m. String -> Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
propertyGroup labelText children =
  HH.div [ cls [ "property-group" ], HP.attr (HH.AttrName "style") propertyGroupStyle ]
    ([ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text labelText ] ] <> children)

type XYZInput = { label :: String, value :: Number, onInput :: String -> Action }

xyzInputs :: forall m. Array XYZInput -> H.ComponentHTML Action Slots m
xyzInputs inputs =
  HH.div [ cls [ "xyz-inputs" ], HP.attr (HH.AttrName "style") xyzStyle ]
    (map xyzSingleInput inputs)

xyzSingleInput :: forall m. XYZInput -> H.ComponentHTML Action Slots m
xyzSingleInput { label, value, onInput } =
  HH.div [ cls [ "xyz-input" ], HP.attr (HH.AttrName "style") xyzInputStyle ]
    [ HH.span [ cls [ "axis-label" ], HP.attr (HH.AttrName "style") (axisLabelStyle label) ]
        [ HH.text label ]
    , HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (Utils.formatNumber 1 value)
        , HP.attr (HH.AttrName "style") xyzNumberStyle
        , HE.onValueInput onInput
        ]
    ]

numberInput :: forall m. Number -> String -> (String -> Action) -> H.ComponentHTML Action Slots m
numberInput value unit onInput =
  HH.div [ cls [ "number-input-row" ], HP.attr (HH.AttrName "style") numberRowStyle ]
    [ HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (Utils.formatNumber 1 value)
        , HP.attr (HH.AttrName "style") numberInputStyle
        , HE.onValueInput onInput
        ]
    , if unit /= ""
        then HH.span [ cls [ "unit" ], HP.attr (HH.AttrName "style") unitStyle ] [ HH.text unit ]
        else HH.text ""
    ]

sliderInput :: forall m. Number -> Number -> Number -> Number -> (String -> Action) -> H.ComponentHTML Action Slots m
sliderInput value minVal maxVal stepVal onInput =
  HH.div [ cls [ "slider-row" ], HP.attr (HH.AttrName "style") sliderRowStyle ]
    [ HH.input
        [ HP.type_ HP.InputRange
        , HP.value (show value)
        , HP.attr (HH.AttrName "min") (show minVal)
        , HP.attr (HH.AttrName "max") (show maxVal)
        , HP.attr (HH.AttrName "step") (show stepVal)
        , HP.attr (HH.AttrName "style") sliderStyle
        , HE.onValueInput onInput
        ]
    , HH.span [ cls [ "slider-value" ], HP.attr (HH.AttrName "style") sliderValueStyle ]
        [ HH.text (Utils.formatNumber 2 value) ]
    ]

checkboxRow :: forall m. String -> Boolean -> Action -> H.ComponentHTML Action Slots m
checkboxRow labelText checked action =
  HH.div [ cls [ "checkbox-group" ], HP.attr (HH.AttrName "style") checkboxGroupStyle ]
    [ HH.label [ HP.attr (HH.AttrName "style") checkboxLabelStyle ]
        [ HH.input
            [ HP.type_ HP.InputCheckbox
            , HP.checked checked
            , HE.onChecked \_ -> action
            ]
        , HH.text labelText
        ]
    ]

-- =============================================================================
--                                                                     // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: #1E1E1E; color: #E0E0E0; font-size: 12px; overflow: hidden;"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 8px 12px; background: #252525; border-bottom: 1px solid #333;"

cameraNameStyle :: String
cameraNameStyle =
  "color: #888; font-size: 13px;"

contentStyle :: String
contentStyle =
  "flex: 1; overflow-y: auto; padding: 8px;"

noCameraStyle :: String
noCameraStyle =
  "flex: 1; display: flex; flex-direction: column; align-items: center; " <>
  "justify-content: center; gap: 12px; color: #666;"

createBtnStyle :: String
createBtnStyle =
  "padding: 8px 16px; border: 1px solid #7C9CFF; border-radius: 4px; " <>
  "background: transparent; color: #7C9CFF; cursor: pointer;"

sectionStyle :: String
sectionStyle =
  "margin-bottom: 8px; border: 1px solid #333; border-radius: 4px; overflow: hidden;"

sectionHeaderStyle :: String
sectionHeaderStyle =
  "display: flex; align-items: center; gap: 6px; padding: 8px; " <>
  "background: #252525; cursor: pointer; user-select: none;"

toggleIconStyle :: String
toggleIconStyle =
  "font-size: 11px; color: #666;"

sectionContentStyle :: String
sectionContentStyle =
  "padding: 8px;"

propertyGroupStyle :: String
propertyGroupStyle =
  "margin-bottom: 8px;"

labelStyle :: String
labelStyle =
  "display: block; color: #888; font-size: 12px; margin-bottom: 4px;"

xyzStyle :: String
xyzStyle =
  "display: grid; grid-template-columns: 1fr 1fr 1fr; gap: 4px;"

xyzInputStyle :: String
xyzInputStyle =
  "display: flex; align-items: center; gap: 4px;"

axisLabelStyle :: String -> String
axisLabelStyle axis =
  let color = case axis of
        "X" -> "#FF6B6B"
        "Y" -> "#69DB7C"
        _ -> "#74C0FC"
  in "font-size: 12px; font-weight: 600; width: 14px; color: " <> color <> ";"

xyzNumberStyle :: String
xyzNumberStyle =
  "flex: 1; width: 100%; padding: 4px; background: #2A2A2A; " <>
  "border: 1px solid #444; border-radius: 3px; color: #DDD; font-size: 11px;"

numberRowStyle :: String
numberRowStyle =
  "display: flex; align-items: center; gap: 4px;"

numberInputStyle :: String
numberInputStyle =
  "flex: 1; padding: 4px 8px; background: #2A2A2A; border: 1px solid #444; " <>
  "border-radius: 3px; color: #DDD; font-size: 12px;"

unitStyle :: String
unitStyle =
  "color: #888; font-size: 11px; min-width: 20px;"

selectStyle :: String
selectStyle =
  "width: 100%; padding: 6px 8px; background: #2A2A2A; border: 1px solid #444; " <>
  "border-radius: 3px; color: #DDD; font-size: 12px; cursor: pointer;"

presetRowStyle :: String
presetRowStyle =
  "display: flex; flex-wrap: wrap; gap: 4px; margin-bottom: 12px;"

presetBtnStyle :: Boolean -> String
presetBtnStyle isActive =
  "padding: 4px 8px; border: 1px solid " <> 
  (if isActive then "#7C9CFF" else "#3D3D3D") <> "; " <>
  "border-radius: 3px; " <>
  "background: " <> (if isActive then "#7C9CFF" else "#2A2A2A") <> "; " <>
  "color: " <> (if isActive then "#FFF" else "#888") <> "; " <>
  "font-size: 12px; cursor: pointer;"

sliderRowStyle :: String
sliderRowStyle =
  "display: flex; align-items: center; gap: 8px;"

sliderStyle :: String
sliderStyle =
  "flex: 1; height: 4px; appearance: none; " <>
  "background: var(--lattice-surface-3, #222222); border-radius: 2px;"

sliderValueStyle :: String
sliderValueStyle =
  "min-width: 45px; text-align: right; color: #9CA3AF; font-family: monospace;"

checkboxGroupStyle :: String
checkboxGroupStyle =
  "margin-bottom: 8px;"

checkboxLabelStyle :: String
checkboxLabelStyle =
  "display: flex; align-items: center; gap: 6px; cursor: pointer;"

descriptionStyle :: String
descriptionStyle =
  "padding: 8px; background: #252525; border-radius: 4px; " <>
  "color: #888; font-size: 12px; font-style: italic; " <>
  "margin-bottom: 12px; line-height: 1.4;"

actionsStyle :: String
actionsStyle =
  "display: flex; gap: 8px; margin-top: 12px;"

previewBtnStyle :: String
previewBtnStyle =
  "flex: 1; padding: 8px 12px; border: 1px solid #5A8FD9; border-radius: 4px; " <>
  "background: #2A2A2A; color: #5A8FD9; font-size: 13px; cursor: pointer;"

applyBtnStyle :: String
applyBtnStyle =
  "flex: 1; padding: 8px 12px; border: 1px solid #4CAF50; border-radius: 4px; " <>
  "background: #2A2A2A; color: #4CAF50; font-size: 13px; cursor: pointer;"

-- =============================================================================
--                                                                    // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> H.modify_ _ { camera = input.camera, cameraName = input.cameraName }
  
  ToggleSection sectionId ->
    H.modify_ \s -> s { expandedSections = toggleSectionState sectionId s.expandedSections }
  
  SetCameraType val -> updateCamera \c -> c { cameraType = parseCameraType val }
  
  SetPositionX val -> updateCameraVec3 "position" "x" val
  SetPositionY val -> updateCameraVec3 "position" "y" val
  SetPositionZ val -> updateCameraVec3 "position" "z" val
  
  SetPOIX val -> updateCameraVec3 "pointOfInterest" "x" val
  SetPOIY val -> updateCameraVec3 "pointOfInterest" "y" val
  SetPOIZ val -> updateCameraVec3 "pointOfInterest" "z" val
  
  SetOrientationX val -> updateCameraVec3 "orientation" "x" val
  SetOrientationY val -> updateCameraVec3 "orientation" "y" val
  SetOrientationZ val -> updateCameraVec3 "orientation" "z" val
  
  SetXRotation val -> updateCamera \c -> c { xRotation = Utils.parseFloatOr c.xRotation val }
  SetYRotation val -> updateCamera \c -> c { yRotation = Utils.parseFloatOr c.yRotation val }
  SetZRotation val -> updateCamera \c -> c { zRotation = Utils.parseFloatOr c.zRotation val }
  
  SetFocalLength val -> updateCamera \c -> c { focalLength = Utils.parseFloatOr c.focalLength val }
  SetAngleOfView val -> updateCamera \c -> c { angleOfView = Utils.parseFloatOr c.angleOfView val }
  SetFilmSize val -> updateCamera \c -> c { filmSize = Utils.parseFloatOr c.filmSize val }
  SetMeasureFilmSize val -> updateCamera \c -> c { measureFilmSize = parseMeasureFilmSize val }
  
  ApplyPreset preset -> updateCamera \c -> c 
    { focalLength = preset.focalLength
    , angleOfView = preset.angleOfView
    , zoom = preset.zoom
    }
  
  ToggleDOF -> updateCamera \c -> c { depthOfField = c.depthOfField { enabled = not c.depthOfField.enabled } }
  SetFocusDistance val -> updateDOF \d -> d { focusDistance = Utils.parseFloatOr d.focusDistance val }
  SetFStop val -> updateDOF \d -> d { fStop = Utils.parseFloatOr d.fStop val }
  SetBlurLevel val -> updateDOF \d -> d { blurLevel = Utils.parseFloatOr d.blurLevel val }
  ToggleLockToZoom -> updateDOF \d -> d { lockToZoom = not d.lockToZoom }
  
  SetIrisShape val -> updateIris \i -> i { shape = Utils.parseIntOr i.shape val }
  SetIrisRotation val -> updateIris \i -> i { rotation = Utils.parseFloatOr i.rotation val }
  SetIrisRoundness val -> updateIris \i -> i { roundness = Utils.parseFloatOr i.roundness val }
  SetIrisAspectRatio val -> updateIris \i -> i { aspectRatio = Utils.parseFloatOr i.aspectRatio val }
  SetDiffractionFringe val -> updateIris \i -> i { diffractionFringe = Utils.parseFloatOr i.diffractionFringe val }
  
  SetHighlightGain val -> updateHighlight \h -> h { gain = Utils.parseFloatOr h.gain val }
  SetHighlightThreshold val -> updateHighlight \h -> h { threshold = Utils.parseFloatOr h.threshold val }
  SetHighlightSaturation val -> updateHighlight \h -> h { saturation = Utils.parseFloatOr h.saturation val }
  
  SetAutoOrient val -> updateCamera \c -> c { autoOrient = parseAutoOrient val }
  SetNearClip val -> updateCamera \c -> c { nearClip = Utils.parseFloatOr c.nearClip val }
  SetFarClip val -> updateCamera \c -> c { farClip = Utils.parseFloatOr c.farClip val }
  
  -- Trajectory config
  SetTrajectoryType val -> 
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { trajectoryType = parseTrajectoryType val } }
  SetTrajectoryDuration val ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { duration = Utils.parseIntOr s.trajectoryConfig.duration val } }
  SetTrajectoryAmplitude val ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { amplitude = Utils.parseFloatOr s.trajectoryConfig.amplitude val } }
  SetTrajectoryLoops val ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { loops = Utils.parseFloatOr s.trajectoryConfig.loops val } }
  SetTrajectoryEasing val ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { easing = parseEasingMode val } }
  ToggleAudioReactive ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { audioReactive = not s.trajectoryConfig.audioReactive } }
  SetAudioFeature val ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { audioFeature = val } }
  SetAudioSensitivity val ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { audioSensitivity = Utils.parseFloatOr s.trajectoryConfig.audioSensitivity val } }
  PreviewTrajectory -> do
    state <- H.get
    H.raise (PreviewTrajectoryRequested state.trajectoryConfig)
  ApplyTrajectory -> do
    state <- H.get
    H.raise (ApplyTrajectoryRequested state.trajectoryConfig)
  
  -- Shake config
  SetShakeType val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { shakeType = parseShakeType val } }
  SetShakeIntensity val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { intensity = Utils.parseFloatOr s.shakeConfig.intensity val } }
  SetShakeFrequency val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { frequency = Utils.parseFloatOr s.shakeConfig.frequency val } }
  SetShakeDuration val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { duration = Utils.parseIntOr s.shakeConfig.duration val } }
  ToggleShakeRotation ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { rotationEnabled = not s.shakeConfig.rotationEnabled } }
  SetShakeRotationScale val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { rotationScale = Utils.parseFloatOr s.shakeConfig.rotationScale val } }
  SetShakeDecay val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { decay = Utils.parseFloatOr s.shakeConfig.decay val } }
  SetShakeSeed val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { seed = Utils.parseIntOr s.shakeConfig.seed val } }
  PreviewShake -> do
    state <- H.get
    H.raise (PreviewShakeRequested state.shakeConfig)
  ApplyShake -> do
    state <- H.get
    H.raise (ApplyShakeRequested state.shakeConfig)
  
  CreateCamera -> H.raise CreateCameraRequested

-- =============================================================================
--                                                            // update helpers
-- =============================================================================

toggleSectionState :: String -> ExpandedSections -> ExpandedSections
toggleSectionState sectionId sections =
  case sectionId of
    "transform" -> sections { transform = not sections.transform }
    "lens" -> sections { lens = not sections.lens }
    "dof" -> sections { dof = not sections.dof }
    "iris" -> sections { iris = not sections.iris }
    "highlight" -> sections { highlight = not sections.highlight }
    "autoOrient" -> sections { autoOrient = not sections.autoOrient }
    "clipping" -> sections { clipping = not sections.clipping }
    "trajectory" -> sections { trajectory = not sections.trajectory }
    "shake" -> sections { shake = not sections.shake }
    _ -> sections

updateCamera :: forall m. MonadAff m => (Camera3D -> Camera3D) -> H.HalogenM State Action Slots Output m Unit
updateCamera f = do
  state <- H.get
  case state.camera of
    Just cam -> do
      let newCam = f cam
      H.modify_ _ { camera = Just newCam }
      H.raise (CameraUpdated newCam)
    Nothing -> pure unit

updateCameraVec3 :: forall m. MonadAff m => String -> String -> String -> H.HalogenM State Action Slots Output m Unit
updateCameraVec3 field axis val = do
  state <- H.get
  case state.camera of
    Just cam -> do
      let 
        vec = case field of
          "position" -> cam.position
          "pointOfInterest" -> cam.pointOfInterest
          _ -> cam.orientation
        newVec = case axis of
          "x" -> vec { x = Utils.parseFloatOr vec.x val }
          "y" -> vec { y = Utils.parseFloatOr vec.y val }
          _ -> vec { z = Utils.parseFloatOr vec.z val }
        newCam = case field of
          "position" -> cam { position = newVec }
          "pointOfInterest" -> cam { pointOfInterest = newVec }
          _ -> cam { orientation = newVec }
      H.modify_ _ { camera = Just newCam }
      H.raise (CameraUpdated newCam)
    Nothing -> pure unit

updateDOF :: forall m. MonadAff m => (DepthOfFieldSettings -> DepthOfFieldSettings) -> H.HalogenM State Action Slots Output m Unit
updateDOF f = updateCamera \c -> c { depthOfField = f c.depthOfField }

updateIris :: forall m. MonadAff m => (IrisSettings -> IrisSettings) -> H.HalogenM State Action Slots Output m Unit
updateIris f = updateCamera \c -> c { iris = f c.iris }

updateHighlight :: forall m. MonadAff m => (HighlightSettings -> HighlightSettings) -> H.HalogenM State Action Slots Output m Unit
updateHighlight f = updateCamera \c -> c { highlight = f c.highlight }
