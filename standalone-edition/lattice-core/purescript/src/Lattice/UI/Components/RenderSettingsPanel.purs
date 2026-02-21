-- | Render Settings Panel Component
-- |
-- | Configures render settings for a composition or render queue job.
-- | Settings include:
-- | - Resolution (full, half, third, quarter, custom)
-- | - Frame rate (inherit, 16, 24, 30, 60 fps, custom)
-- | - Quality (draft, standard, best)
-- | - Motion blur (on/off, samples, shutter angle)
-- | - Time span (work area, comp duration, custom)
-- | - Advanced options (skip existing, cache, multi-processing)
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/RenderSettingsPanel.vue
module Lattice.UI.Components.RenderSettingsPanel
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , RenderSettings
  , QualityLevel(..)
  , ResolutionMode(..)
  , FrameRateMode(..)
  , TimeSpanMode(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
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

type Input = RenderSettings

data Output
  = SettingsChanged RenderSettings

data Query a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                       // render settings types
-- =============================================================================

type RenderSettings =
  { quality :: QualityLevel
  , resolution :: ResolutionMode
  , customWidth :: Int
  , customHeight :: Int
  , frameRate :: FrameRateMode
  , customFps :: Int
  , timeSpan :: TimeSpanMode
  , startFrame :: Int
  , endFrame :: Int
  , motionBlur :: Boolean
  , motionBlurSamples :: Int
  , shutterAngle :: Int
  , shutterPhase :: Int
  , skipExisting :: Boolean
  , useCache :: Boolean
  , useMultiProcessing :: Boolean
  }

data QualityLevel
  = QualityDraft
  | QualityStandard
  | QualityBest

derive instance eqQualityLevel :: Eq QualityLevel

instance showQualityLevel :: Show QualityLevel where
  show = case _ of
    QualityDraft -> "draft"
    QualityStandard -> "standard"
    QualityBest -> "best"

qualityLabel :: QualityLevel -> String
qualityLabel = case _ of
  QualityDraft -> "Draft (fast)"
  QualityStandard -> "Standard"
  QualityBest -> "Best (slow)"

data ResolutionMode
  = ResolutionFull
  | ResolutionHalf
  | ResolutionThird
  | ResolutionQuarter
  | ResolutionCustom

derive instance eqResolutionMode :: Eq ResolutionMode

instance showResolutionMode :: Show ResolutionMode where
  show = case _ of
    ResolutionFull -> "full"
    ResolutionHalf -> "half"
    ResolutionThird -> "third"
    ResolutionQuarter -> "quarter"
    ResolutionCustom -> "custom"

resolutionLabel :: ResolutionMode -> String
resolutionLabel = case _ of
  ResolutionFull -> "Full"
  ResolutionHalf -> "Half"
  ResolutionThird -> "Third"
  ResolutionQuarter -> "Quarter"
  ResolutionCustom -> "Custom"

data FrameRateMode
  = FpsInherit
  | Fps16
  | Fps24
  | Fps30
  | Fps60
  | FpsCustom

derive instance eqFrameRateMode :: Eq FrameRateMode

instance showFrameRateMode :: Show FrameRateMode where
  show = case _ of
    FpsInherit -> "inherit"
    Fps16 -> "16"
    Fps24 -> "24"
    Fps30 -> "30"
    Fps60 -> "60"
    FpsCustom -> "custom"

fpsLabel :: FrameRateMode -> String
fpsLabel = case _ of
  FpsInherit -> "Use Comp Settings"
  Fps16 -> "16 fps (Wan 2.1)"
  Fps24 -> "24 fps (Film)"
  Fps30 -> "30 fps (Video)"
  Fps60 -> "60 fps (High)"
  FpsCustom -> "Custom"

data TimeSpanMode
  = TimeSpanWorkArea
  | TimeSpanFull
  | TimeSpanCustom

derive instance eqTimeSpanMode :: Eq TimeSpanMode

instance showTimeSpanMode :: Show TimeSpanMode where
  show = case _ of
    TimeSpanWorkArea -> "workArea"
    TimeSpanFull -> "full"
    TimeSpanCustom -> "custom"

timeSpanLabel :: TimeSpanMode -> String
timeSpanLabel = case _ of
  TimeSpanWorkArea -> "Work Area Only"
  TimeSpanFull -> "Entire Composition"
  TimeSpanCustom -> "Custom"

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { settings :: RenderSettings
  }

data Action
  = Initialize
  | Receive Input
  | SetQuality QualityLevel
  | SetResolution ResolutionMode
  | SetCustomWidth String
  | SetCustomHeight String
  | SetFrameRate FrameRateMode
  | SetCustomFps String
  | SetTimeSpan TimeSpanMode
  | SetStartFrame String
  | SetEndFrame String
  | ToggleMotionBlur
  | SetMotionBlurSamples String
  | SetShutterAngle String
  | SetShutterPhase String
  | ToggleSkipExisting
  | ToggleUseCache
  | ToggleMultiProcessing

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
initialState input = { settings: input }

defaultSettings :: RenderSettings
defaultSettings =
  { quality: QualityStandard
  , resolution: ResolutionFull
  , customWidth: 832
  , customHeight: 480
  , frameRate: FpsInherit
  , customFps: 16
  , timeSpan: TimeSpanWorkArea
  , startFrame: 0
  , endFrame: 80
  , motionBlur: false
  , motionBlurSamples: 8
  , shutterAngle: 180
  , shutterPhase: -90
  , skipExisting: false
  , useCache: true
  , useMultiProcessing: false
  }

-- =============================================================================
--                                                                     // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "render-settings-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    ]
    [ renderQualitySection state
    , renderTimeSpanSection state
    , renderMotionBlurSection state
    , renderAdvancedSection state
    ]

renderQualitySection :: forall m. State -> H.ComponentHTML Action Slots m
renderQualitySection state =
  HH.div
    [ cls [ "panel-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.h4 [ cls [ "section-title" ], HP.attr (HH.AttrName "style") sectionTitleStyle ]
        [ HH.text "Render Settings" ]
    
    -- Quality
    , formRow "Quality"
        [ HH.select
            [ cls [ "settings-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange parseQuality
            ]
            (map (qualityOption state.settings.quality) [QualityDraft, QualityStandard, QualityBest])
        ]
    
    -- Resolution
    , formRow "Resolution"
        [ HH.select
            [ cls [ "settings-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange parseResolution
            ]
            (map (resolutionOption state.settings.resolution) 
              [ResolutionFull, ResolutionHalf, ResolutionThird, ResolutionQuarter, ResolutionCustom])
        ]
    
    -- Custom Resolution
    , if state.settings.resolution == ResolutionCustom
        then subFormRow "Size"
          [ HH.div [ cls [ "dimension-inputs" ], HP.attr (HH.AttrName "style") dimensionInputsStyle ]
              [ HH.input
                  [ HP.type_ HP.InputNumber
                  , HP.value (show state.settings.customWidth)
                  , HP.attr (HH.AttrName "min") "8"
                  , HP.attr (HH.AttrName "step") "8"
                  , HP.attr (HH.AttrName "style") smallInputStyle
                  , HE.onValueInput SetCustomWidth
                  ]
              , HH.span [ HP.attr (HH.AttrName "style") dimSeparatorStyle ] [ HH.text "x" ]
              , HH.input
                  [ HP.type_ HP.InputNumber
                  , HP.value (show state.settings.customHeight)
                  , HP.attr (HH.AttrName "min") "8"
                  , HP.attr (HH.AttrName "step") "8"
                  , HP.attr (HH.AttrName "style") smallInputStyle
                  , HE.onValueInput SetCustomHeight
                  ]
              ]
          ]
        else HH.text ""
    
    -- Frame Rate
    , formRow "Frame Rate"
        [ HH.select
            [ cls [ "settings-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange parseFrameRate
            ]
            (map (fpsOption state.settings.frameRate) 
              [FpsInherit, Fps16, Fps24, Fps30, Fps60, FpsCustom])
        ]
    
    -- Custom FPS
    , if state.settings.frameRate == FpsCustom
        then subFormRow "FPS"
          [ HH.input
              [ HP.type_ HP.InputNumber
              , HP.value (show state.settings.customFps)
              , HP.attr (HH.AttrName "min") "1"
              , HP.attr (HH.AttrName "max") "120"
              , HP.attr (HH.AttrName "style") inputStyle
              , HE.onValueInput SetCustomFps
              ]
          ]
        else HH.text ""
    ]

renderTimeSpanSection :: forall m. State -> H.ComponentHTML Action Slots m
renderTimeSpanSection state =
  HH.div
    [ cls [ "panel-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.h4 [ cls [ "section-title" ], HP.attr (HH.AttrName "style") sectionTitleStyle ]
        [ HH.text "Time Span" ]
    
    -- Time Span Mode
    , formRow "Render"
        [ HH.select
            [ cls [ "settings-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange parseTimeSpan
            ]
            (map (timeSpanOption state.settings.timeSpan) 
              [TimeSpanWorkArea, TimeSpanFull, TimeSpanCustom])
        ]
    
    -- Custom Frame Range
    , if state.settings.timeSpan == TimeSpanCustom
        then subFormRow "Frames"
          [ HH.div [ cls [ "range-inputs" ], HP.attr (HH.AttrName "style") rangeInputsStyle ]
              [ HH.input
                  [ HP.type_ HP.InputNumber
                  , HP.value (show state.settings.startFrame)
                  , HP.attr (HH.AttrName "min") "0"
                  , HP.attr (HH.AttrName "style") smallInputStyle
                  , HE.onValueInput SetStartFrame
                  ]
              , HH.span [ HP.attr (HH.AttrName "style") dimSeparatorStyle ] [ HH.text "to" ]
              , HH.input
                  [ HP.type_ HP.InputNumber
                  , HP.value (show state.settings.endFrame)
                  , HP.attr (HH.AttrName "min") "0"
                  , HP.attr (HH.AttrName "style") smallInputStyle
                  , HE.onValueInput SetEndFrame
                  ]
              ]
          ]
        else HH.text ""
    ]

renderMotionBlurSection :: forall m. State -> H.ComponentHTML Action Slots m
renderMotionBlurSection state =
  HH.div
    [ cls [ "panel-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.h4 [ cls [ "section-title" ], HP.attr (HH.AttrName "style") sectionTitleStyle ]
        [ HH.text "Motion Blur" ]
    
    -- Enable Motion Blur
    , HH.div [ cls [ "form-row" ], HP.attr (HH.AttrName "style") formRowStyle ]
        [ HH.label [ cls [ "checkbox-label" ], HP.attr (HH.AttrName "style") checkboxLabelStyle ]
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.settings.motionBlur
                , HE.onChecked \_ -> ToggleMotionBlur
                ]
            , HH.text "Enable Motion Blur"
            ]
        ]
    
    -- Motion blur settings (only when enabled)
    , if state.settings.motionBlur
        then HH.div_
          [ -- Samples
            subFormRow "Samples"
              [ HH.select
                  [ cls [ "settings-select" ]
                  , HP.attr (HH.AttrName "style") selectStyle
                  , HE.onValueChange SetMotionBlurSamples
                  ]
                  [ HH.option [ HP.value "4", HP.selected (state.settings.motionBlurSamples == 4) ] 
                      [ HH.text "4 (Fast)" ]
                  , HH.option [ HP.value "8", HP.selected (state.settings.motionBlurSamples == 8) ] 
                      [ HH.text "8 (Standard)" ]
                  , HH.option [ HP.value "16", HP.selected (state.settings.motionBlurSamples == 16) ] 
                      [ HH.text "16 (Best)" ]
                  , HH.option [ HP.value "32", HP.selected (state.settings.motionBlurSamples == 32) ] 
                      [ HH.text "32 (Extreme)" ]
                  ]
              ]
          
          -- Shutter Angle
          , subFormRow "Shutter Angle"
              [ HH.div [ cls [ "slider-row" ], HP.attr (HH.AttrName "style") sliderRowStyle ]
                  [ HH.input
                      [ HP.type_ HP.InputRange
                      , HP.value (show state.settings.shutterAngle)
                      , HP.attr (HH.AttrName "min") "0"
                      , HP.attr (HH.AttrName "max") "360"
                      , HP.attr (HH.AttrName "style") sliderStyle
                      , HE.onValueInput SetShutterAngle
                      ]
                  , HH.span [ cls [ "slider-value" ], HP.attr (HH.AttrName "style") sliderValueStyle ]
                      [ HH.text (show state.settings.shutterAngle <> "\x{00B0}") ]
                  ]
              ]
          
          -- Shutter Phase
          , subFormRow "Shutter Phase"
              [ HH.div [ cls [ "slider-row" ], HP.attr (HH.AttrName "style") sliderRowStyle ]
                  [ HH.input
                      [ HP.type_ HP.InputRange
                      , HP.value (show state.settings.shutterPhase)
                      , HP.attr (HH.AttrName "min") "-180"
                      , HP.attr (HH.AttrName "max") "180"
                      , HP.attr (HH.AttrName "style") sliderStyle
                      , HE.onValueInput SetShutterPhase
                      ]
                  , HH.span [ cls [ "slider-value" ], HP.attr (HH.AttrName "style") sliderValueStyle ]
                      [ HH.text (show state.settings.shutterPhase <> "\x{00B0}") ]
                  ]
              ]
          ]
        else HH.text ""
    ]

renderAdvancedSection :: forall m. State -> H.ComponentHTML Action Slots m
renderAdvancedSection state =
  HH.div
    [ cls [ "panel-section" ]
    , HP.attr (HH.AttrName "style") sectionStyleLast
    ]
    [ HH.h4 [ cls [ "section-title" ], HP.attr (HH.AttrName "style") sectionTitleStyle ]
        [ HH.text "Advanced" ]
    
    -- Skip Existing
    , HH.div [ cls [ "form-row" ], HP.attr (HH.AttrName "style") formRowStyle ]
        [ HH.label [ cls [ "checkbox-label" ], HP.attr (HH.AttrName "style") checkboxLabelStyle ]
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.settings.skipExisting
                , HE.onChecked \_ -> ToggleSkipExisting
                ]
            , HH.text "Skip Existing Frames"
            ]
        ]
    
    -- Use Cache
    , HH.div [ cls [ "form-row" ], HP.attr (HH.AttrName "style") formRowStyle ]
        [ HH.label [ cls [ "checkbox-label" ], HP.attr (HH.AttrName "style") checkboxLabelStyle ]
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.settings.useCache
                , HE.onChecked \_ -> ToggleUseCache
                ]
            , HH.text "Use Frame Cache"
            ]
        ]
    
    -- Multi-Processing
    , HH.div [ cls [ "form-row" ], HP.attr (HH.AttrName "style") formRowStyle ]
        [ HH.label [ cls [ "checkbox-label" ], HP.attr (HH.AttrName "style") checkboxLabelStyle ]
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.settings.useMultiProcessing
                , HE.onChecked \_ -> ToggleMultiProcessing
                ]
            , HH.text "Multi-Frame Rendering"
            ]
        ]
    ]

-- =============================================================================
--                                                              // form helpers
-- =============================================================================

formRow :: forall m. String -> Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
formRow labelText children =
  HH.div [ cls [ "form-row" ], HP.attr (HH.AttrName "style") formRowStyle ]
    ([ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text labelText ] ] <> children)

subFormRow :: forall m. String -> Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
subFormRow labelText children =
  HH.div [ cls [ "form-row sub-row" ], HP.attr (HH.AttrName "style") subFormRowStyle ]
    ([ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text labelText ] ] <> children)

qualityOption :: forall m. QualityLevel -> QualityLevel -> H.ComponentHTML Action Slots m
qualityOption current opt =
  HH.option [ HP.value (show opt), HP.selected (current == opt) ] [ HH.text (qualityLabel opt) ]

resolutionOption :: forall m. ResolutionMode -> ResolutionMode -> H.ComponentHTML Action Slots m
resolutionOption current opt =
  HH.option [ HP.value (show opt), HP.selected (current == opt) ] [ HH.text (resolutionLabel opt) ]

fpsOption :: forall m. FrameRateMode -> FrameRateMode -> H.ComponentHTML Action Slots m
fpsOption current opt =
  HH.option [ HP.value (show opt), HP.selected (current == opt) ] [ HH.text (fpsLabel opt) ]

timeSpanOption :: forall m. TimeSpanMode -> TimeSpanMode -> H.ComponentHTML Action Slots m
timeSpanOption current opt =
  HH.option [ HP.value (show opt), HP.selected (current == opt) ] [ HH.text (timeSpanLabel opt) ]

-- =============================================================================
--                                                                    // parsers
-- =============================================================================

parseQuality :: String -> Action
parseQuality = case _ of
  "draft" -> SetQuality QualityDraft
  "standard" -> SetQuality QualityStandard
  "best" -> SetQuality QualityBest
  _ -> SetQuality QualityStandard

parseResolution :: String -> Action
parseResolution = case _ of
  "full" -> SetResolution ResolutionFull
  "half" -> SetResolution ResolutionHalf
  "third" -> SetResolution ResolutionThird
  "quarter" -> SetResolution ResolutionQuarter
  "custom" -> SetResolution ResolutionCustom
  _ -> SetResolution ResolutionFull

parseFrameRate :: String -> Action
parseFrameRate = case _ of
  "inherit" -> SetFrameRate FpsInherit
  "16" -> SetFrameRate Fps16
  "24" -> SetFrameRate Fps24
  "30" -> SetFrameRate Fps30
  "60" -> SetFrameRate Fps60
  "custom" -> SetFrameRate FpsCustom
  _ -> SetFrameRate FpsInherit

parseTimeSpan :: String -> Action
parseTimeSpan = case _ of
  "workArea" -> SetTimeSpan TimeSpanWorkArea
  "full" -> SetTimeSpan TimeSpanFull
  "custom" -> SetTimeSpan TimeSpanCustom
  _ -> SetTimeSpan TimeSpanWorkArea

-- =============================================================================
--                                                                     // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; gap: 16px; padding: 12px; " <>
  "font-size: 12px; color: var(--lattice-text-primary, #E5E5E5);"

sectionStyle :: String
sectionStyle =
  "display: flex; flex-direction: column; gap: 8px; padding-bottom: 12px; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #2A2A2A);"

sectionStyleLast :: String
sectionStyleLast =
  "display: flex; flex-direction: column; gap: 8px;"

sectionTitleStyle :: String
sectionTitleStyle =
  "margin: 0; font-size: 11px; font-weight: 600; text-transform: uppercase; " <>
  "letter-spacing: 0.5px; color: var(--lattice-text-secondary, #9CA3AF);"

formRowStyle :: String
formRowStyle =
  "display: flex; align-items: center; gap: 8px;"

subFormRowStyle :: String
subFormRowStyle =
  "display: flex; align-items: center; gap: 8px; margin-left: 20px;"

labelStyle :: String
labelStyle =
  "flex: 0 0 100px; color: var(--lattice-text-secondary, #9CA3AF);"

selectStyle :: String
selectStyle =
  "flex: 1; padding: 4px 8px; background: var(--lattice-surface-2, #1A1A1A); " <>
  "border: 1px solid var(--lattice-border-default, #333333); border-radius: 4px; " <>
  "color: var(--lattice-text-primary, #E5E5E5); font-size: 12px;"

inputStyle :: String
inputStyle =
  "flex: 1; padding: 4px 8px; background: var(--lattice-surface-2, #1A1A1A); " <>
  "border: 1px solid var(--lattice-border-default, #333333); border-radius: 4px; " <>
  "color: var(--lattice-text-primary, #E5E5E5); font-size: 12px;"

smallInputStyle :: String
smallInputStyle =
  "width: 70px; padding: 4px 8px; background: var(--lattice-surface-2, #1A1A1A); " <>
  "border: 1px solid var(--lattice-border-default, #333333); border-radius: 4px; " <>
  "color: var(--lattice-text-primary, #E5E5E5); font-size: 12px;"

dimensionInputsStyle :: String
dimensionInputsStyle =
  "display: flex; align-items: center; gap: 8px; flex: 1;"

rangeInputsStyle :: String
rangeInputsStyle =
  "display: flex; align-items: center; gap: 8px; flex: 1;"

dimSeparatorStyle :: String
dimSeparatorStyle =
  "color: var(--lattice-text-muted, #6B7280);"

checkboxLabelStyle :: String
checkboxLabelStyle =
  "display: flex; align-items: center; gap: 8px; cursor: pointer; " <>
  "color: var(--lattice-text-primary, #E5E5E5);"

sliderRowStyle :: String
sliderRowStyle =
  "display: flex; align-items: center; gap: 8px; flex: 1;"

sliderStyle :: String
sliderStyle =
  "flex: 1; height: 4px; appearance: none; " <>
  "background: var(--lattice-surface-3, #222222); border-radius: 2px;"

sliderValueStyle :: String
sliderValueStyle =
  "min-width: 45px; text-align: right; " <>
  "color: var(--lattice-text-secondary, #9CA3AF); font-family: monospace;"

-- =============================================================================
--                                                                    // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> H.modify_ _ { settings = input }
  
  SetQuality quality -> updateAndEmit \s -> s { quality = quality }
  
  SetResolution resolution -> do
    H.modify_ \s -> s { settings = s.settings { resolution = resolution } }
    -- Set defaults for custom resolution
    state <- H.get
    when (resolution == ResolutionCustom) do
      when (state.settings.customWidth <= 0) do
        H.modify_ \s -> s { settings = s.settings { customWidth = 832 } }
      when (state.settings.customHeight <= 0) do
        H.modify_ \s -> s { settings = s.settings { customHeight = 480 } }
    emitSettings
  
  SetCustomWidth val -> updateAndEmit \s -> s { customWidth = Utils.parseIntOr s.customWidth val }
  SetCustomHeight val -> updateAndEmit \s -> s { customHeight = Utils.parseIntOr s.customHeight val }
  
  SetFrameRate fps -> updateAndEmit \s -> s { frameRate = fps }
  SetCustomFps val -> updateAndEmit \s -> s { customFps = Utils.parseIntOr s.customFps val }
  
  SetTimeSpan mode -> updateAndEmit \s -> s { timeSpan = mode }
  SetStartFrame val -> updateAndEmit \s -> s { startFrame = Utils.parseIntOr s.startFrame val }
  SetEndFrame val -> updateAndEmit \s -> s { endFrame = Utils.parseIntOr s.endFrame val }
  
  ToggleMotionBlur -> updateAndEmit \s -> s { motionBlur = not s.motionBlur }
  SetMotionBlurSamples val -> updateAndEmit \s -> s { motionBlurSamples = Utils.parseIntOr s.motionBlurSamples val }
  SetShutterAngle val -> updateAndEmit \s -> s { shutterAngle = Utils.parseIntOr s.shutterAngle val }
  SetShutterPhase val -> updateAndEmit \s -> s { shutterPhase = Utils.parseIntOr s.shutterPhase val }
  
  ToggleSkipExisting -> updateAndEmit \s -> s { skipExisting = not s.skipExisting }
  ToggleUseCache -> updateAndEmit \s -> s { useCache = not s.useCache }
  ToggleMultiProcessing -> updateAndEmit \s -> s { useMultiProcessing = not s.useMultiProcessing }

updateAndEmit :: forall m. MonadAff m => (RenderSettings -> RenderSettings) -> H.HalogenM State Action Slots Output m Unit
updateAndEmit f = do
  H.modify_ \s -> s { settings = f s.settings }
  emitSettings

emitSettings :: forall m. MonadAff m => H.HalogenM State Action Slots Output m Unit
emitSettings = do
  state <- H.get
  H.raise (SettingsChanged state.settings)
