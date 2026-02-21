-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- camera-properties // render
-- render functions for the camera properties panel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.CameraProperties.Render
  ( render
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Number (abs)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.UI.Utils as Utils
import Lattice.UI.Components.CameraProperties.Types as Types
import Lattice.UI.Components.CameraProperties.Styles as Styles
import Lattice.UI.Components.CameraProperties.UIHelpers as UI

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                   // render
-- ═══════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
render state =
  HH.div
    [ cls [ "camera-properties" ]
    , HP.attr (HH.AttrName "style") Styles.panelStyle
    ]
    [ renderHeader state
    , case state.camera of
        Just cam -> renderPropertiesContent state cam
        Nothing -> renderNoCamera
    ]

renderHeader :: forall m. Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderHeader state =
  HH.div
    [ cls [ "panel-header" ]
    , HP.attr (HH.AttrName "style") Styles.headerStyle
    ]
    [ HH.span [ cls [ "panel-title" ] ] [ HH.text "Camera" ]
    , HH.span [ cls [ "camera-name" ], HP.attr (HH.AttrName "style") Styles.cameraNameStyle ]
        [ HH.text state.cameraName ]
    ]

renderNoCamera :: forall m. H.ComponentHTML Types.Action Types.Slots m
renderNoCamera =
  HH.div
    [ cls [ "no-camera" ]
    , HP.attr (HH.AttrName "style") Styles.noCameraStyle
    ]
    [ HH.p_ [ HH.text "No camera selected" ]
    , HH.button
        [ cls [ "create-camera-btn" ]
        , HP.attr (HH.AttrName "style") Styles.createBtnStyle
        , HE.onClick \_ -> Types.CreateCamera
        ]
        [ HH.text "Create Camera" ]
    ]

renderPropertiesContent 
  :: forall m
   . Types.State 
  -> Types.Camera3D 
  -> H.ComponentHTML Types.Action Types.Slots m
renderPropertiesContent state cam =
  HH.div
    [ cls [ "properties-content" ]
    , HP.attr (HH.AttrName "style") Styles.contentStyle
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

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // type section
-- ═══════════════════════════════════════════════════════════════════════════

renderTypeSection :: forall m. Types.Camera3D -> H.ComponentHTML Types.Action Types.Slots m
renderTypeSection cam =
  HH.div
    [ cls [ "property-section" ]
    , HP.attr (HH.AttrName "style") Styles.sectionStyle
    ]
    [ HH.div [ cls [ "section-header" ] ] [ HH.text "Type" ]
    , HH.div [ cls [ "property-row" ] ]
        [ HH.select
            [ cls [ "type-select" ]
            , HP.attr (HH.AttrName "style") Styles.selectStyle
            , HE.onValueChange Types.SetCameraType
            ]
            [ HH.option [ HP.value "one-node", HP.selected (cam.cameraType == Types.OneNode) ]
                [ HH.text "One-Node Camera" ]
            , HH.option [ HP.value "two-node", HP.selected (cam.cameraType == Types.TwoNode) ]
                [ HH.text "Two-Node Camera" ]
            ]
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                       // transform section
-- ═══════════════════════════════════════════════════════════════════════════

renderTransformSection 
  :: forall m
   . Types.State 
  -> Types.Camera3D 
  -> H.ComponentHTML Types.Action Types.Slots m
renderTransformSection state cam =
  UI.collapsibleSection "Transform" "transform" state.expandedSections.transform
    [ -- position
      UI.propertyGroup "Position"
        [ UI.xyzInputs
            [ { label: "X", value: cam.position.x, onInput: Types.SetPositionX }
            , { label: "Y", value: cam.position.y, onInput: Types.SetPositionY }
            , { label: "Z", value: cam.position.z, onInput: Types.SetPositionZ }
            ]
        ]
    
    -- point of interest (two-node only)
    , if cam.cameraType == Types.TwoNode
        then UI.propertyGroup "Point of Interest"
          [ UI.xyzInputs
              [ { label: "X", value: cam.pointOfInterest.x, onInput: Types.SetPOIX }
              , { label: "Y", value: cam.pointOfInterest.y, onInput: Types.SetPOIY }
              , { label: "Z", value: cam.pointOfInterest.z, onInput: Types.SetPOIZ }
              ]
          ]
        else HH.text ""
    
    -- orientation
    , UI.propertyGroup "Orientation"
        [ UI.xyzInputs
            [ { label: "X", value: cam.orientation.x, onInput: Types.SetOrientationX }
            , { label: "Y", value: cam.orientation.y, onInput: Types.SetOrientationY }
            , { label: "Z", value: cam.orientation.z, onInput: Types.SetOrientationZ }
            ]
        ]
    
    -- individual rotations
    , UI.propertyGroup "X Rotation"
        [ UI.numberInput cam.xRotation "\x{00B0}" Types.SetXRotation ]
    , UI.propertyGroup "Y Rotation"
        [ UI.numberInput cam.yRotation "\x{00B0}" Types.SetYRotation ]
    , UI.propertyGroup "Z Rotation"
        [ UI.numberInput cam.zRotation "\x{00B0}" Types.SetZRotation ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // lens section
-- ═══════════════════════════════════════════════════════════════════════════

renderLensSection 
  :: forall m
   . Types.State 
  -> Types.Camera3D 
  -> H.ComponentHTML Types.Action Types.Slots m
renderLensSection state cam =
  UI.collapsibleSection "Lens" "lens" state.expandedSections.lens
    [ -- preset buttons
      HH.div [ cls [ "preset-row" ], HP.attr (HH.AttrName "style") Styles.presetRowStyle ]
        (map (presetButton cam.focalLength) Types.cameraPresets)
    
    -- focal length
    , UI.propertyGroup "Focal Length"
        [ UI.numberInput cam.focalLength "mm" Types.SetFocalLength ]
    
    -- angle of view
    , UI.propertyGroup "Angle of View"
        [ UI.numberInput cam.angleOfView "\x{00B0}" Types.SetAngleOfView ]
    
    -- film size
    , UI.propertyGroup "Film Size"
        [ UI.numberInput cam.filmSize "mm" Types.SetFilmSize ]
    
    -- measure film size
    , UI.propertyGroup "Measure Film Size"
        [ HH.select
            [ cls [ "settings-select" ]
            , HP.attr (HH.AttrName "style") Styles.selectStyle
            , HE.onValueChange Types.SetMeasureFilmSize
            ]
            [ HH.option [ HP.value "horizontal", HP.selected (cam.measureFilmSize == Types.Horizontal) ]
                [ HH.text "Horizontal" ]
            , HH.option [ HP.value "vertical", HP.selected (cam.measureFilmSize == Types.Vertical) ]
                [ HH.text "Vertical" ]
            , HH.option [ HP.value "diagonal", HP.selected (cam.measureFilmSize == Types.Diagonal) ]
                [ HH.text "Diagonal" ]
            ]
        ]
    ]

presetButton 
  :: forall m
   . Number 
  -> Types.CameraPreset 
  -> H.ComponentHTML Types.Action Types.Slots m
presetButton currentFocal preset =
  let isActive = abs (currentFocal - preset.focalLength) < 0.5
  in HH.button
       [ cls [ "preset-btn" ]
       , HP.attr (HH.AttrName "style") (Styles.presetBtnStyle isActive)
       , HE.onClick \_ -> Types.ApplyPreset preset
       ]
       [ HH.text preset.name ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                           // dof section
-- ═══════════════════════════════════════════════════════════════════════════

renderDOFSection 
  :: forall m
   . Types.State 
  -> Types.Camera3D 
  -> H.ComponentHTML Types.Action Types.Slots m
renderDOFSection state cam =
  UI.collapsibleSection "Depth of Field" "dof" state.expandedSections.dof
    [ UI.checkboxRow "Enable DOF" cam.depthOfField.enabled Types.ToggleDOF
    
    , if cam.depthOfField.enabled
        then HH.div_
          [ UI.propertyGroup "Focus Distance"
              [ UI.numberInput cam.depthOfField.focusDistance "px" Types.SetFocusDistance ]
          , UI.propertyGroup "f-Stop"
              [ UI.numberInput cam.depthOfField.fStop "" Types.SetFStop ]
          , UI.propertyGroup "Blur Level"
              [ UI.sliderInput cam.depthOfField.blurLevel 0.0 1.0 0.01 Types.SetBlurLevel ]
          , UI.checkboxRow "Lock to Zoom" cam.depthOfField.lockToZoom Types.ToggleLockToZoom
          ]
        else HH.text ""
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // iris section
-- ═══════════════════════════════════════════════════════════════════════════

renderIrisSection 
  :: forall m
   . Types.State 
  -> Types.Camera3D 
  -> H.ComponentHTML Types.Action Types.Slots m
renderIrisSection state cam =
  UI.collapsibleSection "Iris" "iris" state.expandedSections.iris
    [ UI.propertyGroup ("Shape (" <> show cam.iris.shape <> "-gon)")
        [ UI.sliderInput (Utils.toNumber cam.iris.shape) 3.0 10.0 1.0 Types.SetIrisShape ]
    , UI.propertyGroup "Rotation"
        [ UI.numberInput cam.iris.rotation "\x{00B0}" Types.SetIrisRotation ]
    , UI.propertyGroup "Roundness"
        [ UI.sliderInput cam.iris.roundness 0.0 1.0 0.01 Types.SetIrisRoundness ]
    , UI.propertyGroup "Aspect Ratio"
        [ UI.sliderInput cam.iris.aspectRatio 0.5 2.0 0.01 Types.SetIrisAspectRatio ]
    , UI.propertyGroup "Diffraction Fringe"
        [ UI.sliderInput cam.iris.diffractionFringe 0.0 1.0 0.01 Types.SetDiffractionFringe ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                      // highlight section
-- ═══════════════════════════════════════════════════════════════════════════

renderHighlightSection 
  :: forall m
   . Types.State 
  -> Types.Camera3D 
  -> H.ComponentHTML Types.Action Types.Slots m
renderHighlightSection state cam =
  UI.collapsibleSection "Highlight" "highlight" state.expandedSections.highlight
    [ UI.propertyGroup "Gain"
        [ UI.sliderInput cam.highlight.gain 0.0 1.0 0.01 Types.SetHighlightGain ]
    , UI.propertyGroup "Threshold"
        [ UI.sliderInput cam.highlight.threshold 0.0 1.0 0.01 Types.SetHighlightThreshold ]
    , UI.propertyGroup "Saturation"
        [ UI.sliderInput cam.highlight.saturation 0.0 1.0 0.01 Types.SetHighlightSaturation ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                    // auto-orient section
-- ═══════════════════════════════════════════════════════════════════════════

renderAutoOrientSection 
  :: forall m
   . Types.State 
  -> Types.Camera3D 
  -> H.ComponentHTML Types.Action Types.Slots m
renderAutoOrientSection state cam =
  UI.collapsibleSection "Auto-Orient" "autoOrient" state.expandedSections.autoOrient
    [ UI.propertyGroup ""
        [ HH.select
            [ cls [ "settings-select" ]
            , HP.attr (HH.AttrName "style") Styles.selectStyle
            , HE.onValueChange Types.SetAutoOrient
            ]
            [ HH.option [ HP.value "off", HP.selected (cam.autoOrient == Types.AutoOrientOff) ]
                [ HH.text "Off" ]
            , HH.option [ HP.value "orient-along-path", HP.selected (cam.autoOrient == Types.OrientAlongPath) ]
                [ HH.text "Orient Along Path" ]
            , HH.option [ HP.value "orient-towards-poi", HP.selected (cam.autoOrient == Types.OrientTowardsPOI) ]
                [ HH.text "Orient Towards Point of Interest" ]
            ]
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                      // clipping section
-- ═══════════════════════════════════════════════════════════════════════════

renderClippingSection 
  :: forall m
   . Types.State 
  -> Types.Camera3D 
  -> H.ComponentHTML Types.Action Types.Slots m
renderClippingSection state cam =
  UI.collapsibleSection "Clipping" "clipping" state.expandedSections.clipping
    [ UI.propertyGroup "Near Clip"
        [ UI.numberInput cam.nearClip "" Types.SetNearClip ]
    , UI.propertyGroup "Far Clip"
        [ UI.numberInput cam.farClip "" Types.SetFarClip ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                    // trajectory section
-- ═══════════════════════════════════════════════════════════════════════════

renderTrajectorySection :: forall m. Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderTrajectorySection state =
  let cfg = state.trajectoryConfig
  in UI.collapsibleSection "Trajectory" "trajectory" state.expandedSections.trajectory
    [ -- motion preset
      UI.propertyGroup "Motion Preset"
        [ HH.select
            [ cls [ "trajectory-select" ]
            , HP.attr (HH.AttrName "style") Styles.selectStyle
            , HE.onValueChange Types.SetTrajectoryType
            ]
            (map (trajectoryOption cfg.trajectoryType) Types.allTrajectoryTypes)
        ]
    
    -- description
    , HH.div [ cls [ "trajectory-description" ], HP.attr (HH.AttrName "style") Styles.descriptionStyle ]
        [ HH.text (Types.trajectoryDescription cfg.trajectoryType) ]
    
    -- duration
    , UI.propertyGroup "Duration (frames)"
        [ UI.numberInput (Utils.toNumber cfg.duration) "" Types.SetTrajectoryDuration ]
    
    -- amplitude
    , UI.propertyGroup "Amplitude"
        [ UI.sliderInput (abs cfg.amplitude) 0.1 2.0 0.1 Types.SetTrajectoryAmplitude ]
    
    -- loops (for orbital)
    , if Types.isOrbitalTrajectory cfg.trajectoryType
        then UI.propertyGroup "Loops"
          [ UI.numberInput cfg.loops "" Types.SetTrajectoryLoops ]
        else HH.text ""
    
    -- easing
    , UI.propertyGroup "Easing"
        [ HH.select
            [ cls [ "settings-select" ]
            , HP.attr (HH.AttrName "style") Styles.selectStyle
            , HE.onValueChange Types.SetTrajectoryEasing
            ]
            [ HH.option [ HP.value "linear", HP.selected (cfg.easing == Types.EasingLinear) ] 
                [ HH.text "Linear" ]
            , HH.option [ HP.value "ease-in", HP.selected (cfg.easing == Types.EasingEaseIn) ]
                [ HH.text "Ease In" ]
            , HH.option [ HP.value "ease-out", HP.selected (cfg.easing == Types.EasingEaseOut) ]
                [ HH.text "Ease Out" ]
            , HH.option [ HP.value "ease-in-out", HP.selected (cfg.easing == Types.EasingEaseInOut) ]
                [ HH.text "Ease In-Out" ]
            , HH.option [ HP.value "bounce", HP.selected (cfg.easing == Types.EasingBounce) ]
                [ HH.text "Bounce" ]
            ]
        ]
    
    -- audio reactive
    , UI.checkboxRow "Audio Reactive" cfg.audioReactive Types.ToggleAudioReactive
    
    , if cfg.audioReactive
        then HH.div_
          [ UI.propertyGroup "Audio Feature"
              [ HH.select
                  [ cls [ "settings-select" ]
                  , HP.attr (HH.AttrName "style") Styles.selectStyle
                  , HE.onValueChange Types.SetAudioFeature
                  ]
                  [ HH.option [ HP.value "amplitude" ] [ HH.text "Amplitude" ]
                  , HH.option [ HP.value "bass" ] [ HH.text "Bass" ]
                  , HH.option [ HP.value "mid" ] [ HH.text "Mid" ]
                  , HH.option [ HP.value "high" ] [ HH.text "High" ]
                  , HH.option [ HP.value "onsets" ] [ HH.text "Onsets" ]
                  ]
              ]
          , UI.propertyGroup "Sensitivity"
              [ UI.sliderInput cfg.audioSensitivity 0.1 3.0 0.1 Types.SetAudioSensitivity ]
          ]
        else HH.text ""
    
    -- action buttons
    , HH.div [ cls [ "trajectory-actions" ], HP.attr (HH.AttrName "style") Styles.actionsStyle ]
        [ HH.button
            [ cls [ "action-btn", "preview" ]
            , HP.attr (HH.AttrName "style") Styles.previewBtnStyle
            , HE.onClick \_ -> Types.PreviewTrajectory
            ]
            [ HH.text "Preview" ]
        , HH.button
            [ cls [ "action-btn", "apply" ]
            , HP.attr (HH.AttrName "style") Styles.applyBtnStyle
            , HE.onClick \_ -> Types.ApplyTrajectory
            ]
            [ HH.text "Apply Keyframes" ]
        ]
    ]

trajectoryOption 
  :: forall m
   . Types.TrajectoryType 
  -> Types.TrajectoryType 
  -> H.ComponentHTML Types.Action Types.Slots m
trajectoryOption current opt =
  HH.option 
    [ HP.value (show opt), HP.selected (current == opt) ]
    [ HH.text (Types.trajectoryLabel opt) ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                         // shake section
-- ═══════════════════════════════════════════════════════════════════════════

renderShakeSection :: forall m. Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderShakeSection state =
  let cfg = state.shakeConfig
  in UI.collapsibleSection "Camera Shake" "shake" state.expandedSections.shake
    [ -- preset
      UI.propertyGroup "Preset"
        [ HH.select
            [ cls [ "settings-select" ]
            , HP.attr (HH.AttrName "style") Styles.selectStyle
            , HE.onValueChange Types.SetShakeType
            ]
            [ HH.option [ HP.value "handheld", HP.selected (cfg.shakeType == Types.ShakeHandheld) ]
                [ HH.text "Handheld" ]
            , HH.option [ HP.value "subtle", HP.selected (cfg.shakeType == Types.ShakeSubtle) ]
                [ HH.text "Subtle" ]
            , HH.option [ HP.value "impact", HP.selected (cfg.shakeType == Types.ShakeImpact) ]
                [ HH.text "Impact" ]
            , HH.option [ HP.value "earthquake", HP.selected (cfg.shakeType == Types.ShakeEarthquake) ]
                [ HH.text "Earthquake" ]
            , HH.option [ HP.value "custom", HP.selected (cfg.shakeType == Types.ShakeCustom) ]
                [ HH.text "Custom" ]
            ]
        ]
    
    -- description
    , HH.div [ cls [ "shake-description" ], HP.attr (HH.AttrName "style") Styles.descriptionStyle ]
        [ HH.text (Types.shakeDescription cfg.shakeType) ]
    
    -- intensity
    , UI.propertyGroup "Intensity"
        [ UI.sliderInput cfg.intensity 0.0 1.0 0.05 Types.SetShakeIntensity ]
    
    -- frequency
    , UI.propertyGroup "Frequency"
        [ UI.sliderInput cfg.frequency 0.1 5.0 0.1 Types.SetShakeFrequency ]
    
    -- duration
    , UI.propertyGroup "Duration (frames)"
        [ UI.numberInput (Utils.toNumber cfg.duration) "" Types.SetShakeDuration ]
    
    -- rotation shake
    , UI.checkboxRow "Rotation Shake" cfg.rotationEnabled Types.ToggleShakeRotation
    
    , if cfg.rotationEnabled
        then UI.propertyGroup "Rotation Scale"
          [ UI.sliderInput cfg.rotationScale 0.0 2.0 0.1 Types.SetShakeRotationScale ]
        else HH.text ""
    
    -- decay
    , UI.propertyGroup "Decay"
        [ UI.sliderInput cfg.decay 0.0 1.0 0.05 Types.SetShakeDecay ]
    
    -- seed
    , UI.propertyGroup "Seed"
        [ UI.numberInput (Utils.toNumber cfg.seed) "" Types.SetShakeSeed ]
    
    -- action buttons
    , HH.div [ cls [ "shake-actions" ], HP.attr (HH.AttrName "style") Styles.actionsStyle ]
        [ HH.button
            [ cls [ "action-btn", "preview" ]
            , HP.attr (HH.AttrName "style") Styles.previewBtnStyle
            , HE.onClick \_ -> Types.PreviewShake
            ]
            [ HH.text "Preview" ]
        , HH.button
            [ cls [ "action-btn", "apply" ]
            , HP.attr (HH.AttrName "style") Styles.applyBtnStyle
            , HE.onClick \_ -> Types.ApplyShake
            ]
            [ HH.text "Apply Keyframes" ]
        ]
    ]
