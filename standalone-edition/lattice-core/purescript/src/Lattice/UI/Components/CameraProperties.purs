-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- camera-properties // main
-- full-featured camera properties editor for 3D camera layers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Camera Properties Panel Component
-- |
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
  , module Types
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H

import Lattice.UI.Utils as Utils
import Lattice.UI.Components.CameraProperties.Types 
  ( Input
  , Output(..)
  , Query
  , Slot
  , State
  , Action(..)
  , Slots
  , ExpandedSections
  , Camera3D
  , CameraType(..)
  , AutoOrientMode(..)
  , MeasureFilmSize(..)
  , DepthOfFieldSettings
  , IrisSettings
  , HighlightSettings
  , TrajectoryType(..)
  , TrajectoryConfig
  , EasingMode(..)
  , ShakeType(..)
  , ShakeConfig
  , CameraPreset
  , parseCameraType
  , parseAutoOrient
  , parseMeasureFilmSize
  , parseTrajectoryType
  , parseEasingMode
  , parseShakeType
  , defaultExpandedSections
  , defaultTrajectoryConfig
  , defaultShakeConfig
  ) as Types
import Lattice.UI.Components.CameraProperties.Render (render)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                // component
-- ═══════════════════════════════════════════════════════════════════════════

component :: forall q m. MonadAff m => H.Component q Types.Input Types.Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Types.Initialize
      , receive = Just <<< Types.Receive
      }
  }

initialState :: Types.Input -> Types.State
initialState input =
  { camera: input.camera
  , cameraName: input.cameraName
  , expandedSections: Types.defaultExpandedSections
  , trajectoryConfig: Types.defaultTrajectoryConfig
  , shakeConfig: Types.defaultShakeConfig
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // actions
-- ═══════════════════════════════════════════════════════════════════════════

handleAction 
  :: forall m
   . MonadAff m 
  => Types.Action 
  -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
handleAction = case _ of
  Types.Initialize -> pure unit
  
  Types.Receive input -> 
    H.modify_ _ { camera = input.camera, cameraName = input.cameraName }
  
  Types.ToggleSection sectionId ->
    H.modify_ \s -> s { expandedSections = toggleSectionState sectionId s.expandedSections }
  
  Types.SetCameraType val -> 
    updateCamera \c -> c { cameraType = Types.parseCameraType val }
  
  Types.SetPositionX val -> updateCameraVec3 "position" "x" val
  Types.SetPositionY val -> updateCameraVec3 "position" "y" val
  Types.SetPositionZ val -> updateCameraVec3 "position" "z" val
  
  Types.SetPOIX val -> updateCameraVec3 "pointOfInterest" "x" val
  Types.SetPOIY val -> updateCameraVec3 "pointOfInterest" "y" val
  Types.SetPOIZ val -> updateCameraVec3 "pointOfInterest" "z" val
  
  Types.SetOrientationX val -> updateCameraVec3 "orientation" "x" val
  Types.SetOrientationY val -> updateCameraVec3 "orientation" "y" val
  Types.SetOrientationZ val -> updateCameraVec3 "orientation" "z" val
  
  Types.SetXRotation val -> 
    updateCamera \c -> c { xRotation = Utils.parseFloatOr c.xRotation val }
  Types.SetYRotation val -> 
    updateCamera \c -> c { yRotation = Utils.parseFloatOr c.yRotation val }
  Types.SetZRotation val -> 
    updateCamera \c -> c { zRotation = Utils.parseFloatOr c.zRotation val }
  
  Types.SetFocalLength val -> 
    updateCamera \c -> c { focalLength = Utils.parseFloatOr c.focalLength val }
  Types.SetAngleOfView val -> 
    updateCamera \c -> c { angleOfView = Utils.parseFloatOr c.angleOfView val }
  Types.SetFilmSize val -> 
    updateCamera \c -> c { filmSize = Utils.parseFloatOr c.filmSize val }
  Types.SetMeasureFilmSize val -> 
    updateCamera \c -> c { measureFilmSize = Types.parseMeasureFilmSize val }
  
  Types.ApplyPreset preset -> updateCamera \c -> c 
    { focalLength = preset.focalLength
    , angleOfView = preset.angleOfView
    , zoom = preset.zoom
    }
  
  Types.ToggleDOF -> 
    updateCamera \c -> c { depthOfField = c.depthOfField { enabled = not c.depthOfField.enabled } }
  Types.SetFocusDistance val -> 
    updateDOF \d -> d { focusDistance = Utils.parseFloatOr d.focusDistance val }
  Types.SetFStop val -> 
    updateDOF \d -> d { fStop = Utils.parseFloatOr d.fStop val }
  Types.SetBlurLevel val -> 
    updateDOF \d -> d { blurLevel = Utils.parseFloatOr d.blurLevel val }
  Types.ToggleLockToZoom -> 
    updateDOF \d -> d { lockToZoom = not d.lockToZoom }
  
  Types.SetIrisShape val -> 
    updateIris \i -> i { shape = Utils.parseIntOr i.shape val }
  Types.SetIrisRotation val -> 
    updateIris \i -> i { rotation = Utils.parseFloatOr i.rotation val }
  Types.SetIrisRoundness val -> 
    updateIris \i -> i { roundness = Utils.parseFloatOr i.roundness val }
  Types.SetIrisAspectRatio val -> 
    updateIris \i -> i { aspectRatio = Utils.parseFloatOr i.aspectRatio val }
  Types.SetDiffractionFringe val -> 
    updateIris \i -> i { diffractionFringe = Utils.parseFloatOr i.diffractionFringe val }
  
  Types.SetHighlightGain val -> 
    updateHighlight \h -> h { gain = Utils.parseFloatOr h.gain val }
  Types.SetHighlightThreshold val -> 
    updateHighlight \h -> h { threshold = Utils.parseFloatOr h.threshold val }
  Types.SetHighlightSaturation val -> 
    updateHighlight \h -> h { saturation = Utils.parseFloatOr h.saturation val }
  
  Types.SetAutoOrient val -> 
    updateCamera \c -> c { autoOrient = Types.parseAutoOrient val }
  Types.SetNearClip val -> 
    updateCamera \c -> c { nearClip = Utils.parseFloatOr c.nearClip val }
  Types.SetFarClip val -> 
    updateCamera \c -> c { farClip = Utils.parseFloatOr c.farClip val }
  
  -- trajectory config
  Types.SetTrajectoryType val -> 
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { trajectoryType = Types.parseTrajectoryType val } }
  Types.SetTrajectoryDuration val ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { duration = Utils.parseIntOr s.trajectoryConfig.duration val } }
  Types.SetTrajectoryAmplitude val ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { amplitude = Utils.parseFloatOr s.trajectoryConfig.amplitude val } }
  Types.SetTrajectoryLoops val ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { loops = Utils.parseFloatOr s.trajectoryConfig.loops val } }
  Types.SetTrajectoryEasing val ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { easing = Types.parseEasingMode val } }
  Types.ToggleAudioReactive ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { audioReactive = not s.trajectoryConfig.audioReactive } }
  Types.SetAudioFeature val ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { audioFeature = val } }
  Types.SetAudioSensitivity val ->
    H.modify_ \s -> s { trajectoryConfig = s.trajectoryConfig { audioSensitivity = Utils.parseFloatOr s.trajectoryConfig.audioSensitivity val } }
  Types.PreviewTrajectory -> do
    state <- H.get
    H.raise (Types.PreviewTrajectoryRequested state.trajectoryConfig)
  Types.ApplyTrajectory -> do
    state <- H.get
    H.raise (Types.ApplyTrajectoryRequested state.trajectoryConfig)
  
  -- shake config
  Types.SetShakeType val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { shakeType = Types.parseShakeType val } }
  Types.SetShakeIntensity val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { intensity = Utils.parseFloatOr s.shakeConfig.intensity val } }
  Types.SetShakeFrequency val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { frequency = Utils.parseFloatOr s.shakeConfig.frequency val } }
  Types.SetShakeDuration val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { duration = Utils.parseIntOr s.shakeConfig.duration val } }
  Types.ToggleShakeRotation ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { rotationEnabled = not s.shakeConfig.rotationEnabled } }
  Types.SetShakeRotationScale val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { rotationScale = Utils.parseFloatOr s.shakeConfig.rotationScale val } }
  Types.SetShakeDecay val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { decay = Utils.parseFloatOr s.shakeConfig.decay val } }
  Types.SetShakeSeed val ->
    H.modify_ \s -> s { shakeConfig = s.shakeConfig { seed = Utils.parseIntOr s.shakeConfig.seed val } }
  Types.PreviewShake -> do
    state <- H.get
    H.raise (Types.PreviewShakeRequested state.shakeConfig)
  Types.ApplyShake -> do
    state <- H.get
    H.raise (Types.ApplyShakeRequested state.shakeConfig)
  
  Types.CreateCamera -> H.raise Types.CreateCameraRequested

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // update helpers
-- ═══════════════════════════════════════════════════════════════════════════

toggleSectionState :: String -> Types.ExpandedSections -> Types.ExpandedSections
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

updateCamera 
  :: forall m
   . MonadAff m 
  => (Types.Camera3D -> Types.Camera3D) 
  -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
updateCamera f = do
  state <- H.get
  case state.camera of
    Just cam -> do
      let newCam = f cam
      H.modify_ _ { camera = Just newCam }
      H.raise (Types.CameraUpdated newCam)
    Nothing -> pure unit

updateCameraVec3 
  :: forall m
   . MonadAff m 
  => String 
  -> String 
  -> String 
  -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
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
      H.raise (Types.CameraUpdated newCam)
    Nothing -> pure unit

updateDOF 
  :: forall m
   . MonadAff m 
  => (Types.DepthOfFieldSettings -> Types.DepthOfFieldSettings) 
  -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
updateDOF f = updateCamera \c -> c { depthOfField = f c.depthOfField }

updateIris 
  :: forall m
   . MonadAff m 
  => (Types.IrisSettings -> Types.IrisSettings) 
  -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
updateIris f = updateCamera \c -> c { iris = f c.iris }

updateHighlight 
  :: forall m
   . MonadAff m 
  => (Types.HighlightSettings -> Types.HighlightSettings) 
  -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
updateHighlight f = updateCamera \c -> c { highlight = f c.highlight }
