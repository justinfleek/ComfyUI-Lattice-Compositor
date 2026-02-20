-- | Audio Panel Component
-- |
-- | Audio source management and analysis panel.
-- | Supports:
-- | - Audio file loading and waveform display
-- | - Volume/mute controls
-- | - Stem separation (vocals, drums, bass, etc.)
-- | - Beat detection with genre presets
-- | - MIDI input monitoring
-- | - MIDI file to keyframes conversion
-- | - Audio path animation
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/AudioPanel.vue
module Lattice.UI.Components.AudioPanel
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  , StemType(..)
  , BeatPreset(..)
  , AudioFeature(..)
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
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
  { hasAudio :: Boolean
  , audioFileName :: String
  , audioDuration :: String
  , audioSampleRate :: String
  , volume :: Int
  , isMuted :: Boolean
  , activeStemName :: Maybe String
  , splineLayers :: Array LayerInfo
  , animatableLayers :: Array LayerInfo
  }

data Output
  = LoadAudioFile
  | RemoveAudio
  | SetVolume Int
  | ToggleMute
  | SeparateStem StemType
  | SeparateAllStems
  | MakeKaraoke
  | PlayStem String
  | DownloadStem String
  | UseStemForReactivity String
  | UseMainAudio
  | AnalyzeBeats
  | SnapToBeats
  | AddBeatMarkers
  | SetBeatPreset BeatPreset
  | SetTimeSignature Int
  | SetFillGaps Boolean
  | SetSnapToGrid Boolean
  | SetTolerance Int
  | ConvertAudioToKeyframes ConvertConfig
  | RefreshMIDIDevices
  | SetMIDIMonitor Boolean
  | LoadMIDIFile
  | RemoveMIDIFile
  | ConvertMIDIToKeyframes MIDIConvertConfig
  | CreatePathAnimator PathAnimConfig

data Query a
  = SetStemSeparationProgress Int String a
  | SetSeparatedStems (Array StemInfo) a
  | SetStemError String a
  | SetBeatGrid BeatGridInfo a
  | SetMIDIDevices (Array MIDIDeviceInfo) a
  | AddMIDIMessage MIDIMessage a
  | SetMIDIFile MIDIFileInfo a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                             // audio // types
-- =============================================================================

data StemType
  = StemVocals
  | StemDrums
  | StemBass
  | StemOther

derive instance eqStemType :: Eq StemType

instance showStemType :: Show StemType where
  show = case _ of
    StemVocals -> "vocals"
    StemDrums -> "drums"
    StemBass -> "bass"
    StemOther -> "other"

stemLabel :: StemType -> String
stemLabel = case _ of
  StemVocals -> "Vocals"
  StemDrums -> "Drums"
  StemBass -> "Bass"
  StemOther -> "Other"

stemIcon :: StemType -> String
stemIcon = case _ of
  StemVocals -> "\x{1F3A4}"
  StemDrums -> "\x{1F941}"
  StemBass -> "\x{1F3B8}"
  StemOther -> "\x{1F3B9}"

data BeatPreset
  = PresetElectronic
  | PresetRock
  | PresetHipHop
  | PresetJazz
  | PresetClassical
  | PresetWaltz
  | PresetCustom

derive instance eqBeatPreset :: Eq BeatPreset

instance showBeatPreset :: Show BeatPreset where
  show = case _ of
    PresetElectronic -> "electronic"
    PresetRock -> "rock"
    PresetHipHop -> "hiphop"
    PresetJazz -> "jazz"
    PresetClassical -> "classical"
    PresetWaltz -> "waltz"
    PresetCustom -> ""

presetLabel :: BeatPreset -> String
presetLabel = case _ of
  PresetElectronic -> "Electronic/EDM"
  PresetRock -> "Rock/Pop"
  PresetHipHop -> "Hip-Hop"
  PresetJazz -> "Jazz"
  PresetClassical -> "Classical"
  PresetWaltz -> "Waltz (3/4)"
  PresetCustom -> "Custom"

data AudioFeature
  = FeatureAmplitude
  | FeatureBass
  | FeatureMid
  | FeatureHigh

derive instance eqAudioFeature :: Eq AudioFeature

instance showAudioFeature :: Show AudioFeature where
  show = case _ of
    FeatureAmplitude -> "amplitude"
    FeatureBass -> "bass"
    FeatureMid -> "mid"
    FeatureHigh -> "high"

featureLabel :: AudioFeature -> String
featureLabel = case _ of
  FeatureAmplitude -> "Overall Amplitude"
  FeatureBass -> "Bass (20-250 Hz)"
  FeatureMid -> "Mid (500-2000 Hz)"
  FeatureHigh -> "High (4000+ Hz)"

type LayerInfo =
  { id :: String
  , name :: String
  }

type StemInfo =
  { name :: String
  , dataUrl :: String
  }

type BeatGridInfo =
  { bpm :: Number
  , bpmConfidence :: Number
  , beatCount :: Int
  , downbeatCount :: Int
  }

type MIDIDeviceInfo =
  { id :: String
  , name :: String
  , manufacturer :: String
  , deviceType :: String
  , state :: String
  }

type MIDIMessage =
  { messageType :: String
  , channel :: Int
  , note :: Maybe Int
  , velocity :: Maybe Int
  , value :: Maybe Int
  }

type MIDIFileInfo =
  { fileName :: String
  , trackCount :: Int
  , totalNotes :: Int
  , bpm :: String
  , duration :: String
  , tracks :: Array MIDITrackInfo
  }

type MIDITrackInfo =
  { index :: Int
  , name :: String
  , noteCount :: Int
  }

type ConvertConfig =
  { layerName :: String
  , amplitudeScale :: Int
  , smoothing :: Int
  }

type MIDIConvertConfig =
  { trackIndex :: Maybe Int
  , channel :: Maybe Int
  , mappingType :: String
  , ccNumber :: Int
  , valueMin :: Int
  , valueMax :: Int
  , interpolation :: String
  , layerName :: String
  }

type PathAnimConfig =
  { splineId :: String
  , targetId :: String
  , mode :: String
  , sensitivity :: Number
  , smoothing :: Number
  , feature :: AudioFeature
  }

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { input :: Input
  , baseId :: String
  -- Stem separation
  , stemSectionExpanded :: Boolean
  , selectedModel :: String
  , isSeparating :: Boolean
  , separationProgress :: Int
  , separationMessage :: String
  , separatedStems :: Array StemInfo
  , separationError :: Maybe String
  -- Beat detection
  , beatSectionExpanded :: Boolean
  , beatPreset :: BeatPreset
  , timeSignature :: Int
  , fillGaps :: Boolean
  , snapToGrid :: Boolean
  , tolerance :: Int
  , isAnalyzingBeats :: Boolean
  , beatGrid :: Maybe BeatGridInfo
  -- Convert audio to keyframes
  , convertSectionExpanded :: Boolean
  , convertLayerName :: String
  , convertAmplitudeScale :: Int
  , convertSmoothing :: Int
  , isConverting :: Boolean
  , convertResult :: Maybe { layerName :: String, keyframeCount :: Int }
  , convertError :: Maybe String
  -- MIDI
  , midiSectionExpanded :: Boolean
  , midiAvailable :: Boolean
  , midiDevices :: Array MIDIDeviceInfo
  , isRefreshingMIDI :: Boolean
  , midiMonitorEnabled :: Boolean
  , recentMIDIMessages :: Array MIDIMessage
  -- MIDI file
  , midiFileSectionExpanded :: Boolean
  , loadedMIDIFile :: Maybe MIDIFileInfo
  , isLoadingMIDI :: Boolean
  , midiTrackIndex :: Maybe Int
  , midiChannel :: Maybe Int
  , midiMappingType :: String
  , midiCCNumber :: Int
  , midiValueMin :: Int
  , midiValueMax :: Int
  , midiInterpolation :: String
  , midiLayerName :: String
  , isConvertingMIDI :: Boolean
  , midiConvertResult :: Maybe { layerName :: String, keyframeCount :: Int }
  , midiConvertError :: Maybe String
  -- Path animation
  , pathAnimSectionExpanded :: Boolean
  , pathAnimSplineId :: String
  , pathAnimTargetId :: String
  , pathAnimMode :: String
  , pathAnimSensitivity :: Number
  , pathAnimSmoothing :: Number
  , pathAnimFeature :: AudioFeature
  , isCreatingPathAnim :: Boolean
  , pathAnimResult :: Maybe String
  , pathAnimError :: Maybe String
  }

data Action
  = Initialize
  | Receive Input
  | LoadAudioAction
  | RemoveAudioAction
  | SetVolumeAction String
  | ToggleMuteAction
  -- Stem actions
  | ToggleStemSection
  | SetModelAction String
  | SeparateStemAction StemType
  | SeparateAllAction
  | MakeKaraokeAction
  | PlayStemAction String
  | DownloadStemAction String
  | UseStemAction String
  | UseMainAudioAction
  -- Beat actions
  | ToggleBeatSection
  | SetBeatPresetAction String
  | SetTimeSignatureAction String
  | SetFillGapsAction Boolean
  | SetSnapToGridAction Boolean
  | SetToleranceAction String
  | AnalyzeBeatsAction
  | SnapToBeatsAction
  | AddBeatMarkersAction
  -- Convert actions
  | ToggleConvertSection
  | SetConvertLayerNameAction String
  | SetConvertAmplitudeScaleAction String
  | SetConvertSmoothingAction String
  | ConvertAudioAction
  -- MIDI actions
  | ToggleMIDISection
  | RefreshMIDIAction
  | SetMIDIMonitorAction Boolean
  -- MIDI file actions
  | ToggleMIDIFileSection
  | LoadMIDIFileAction
  | RemoveMIDIFileAction
  | SetMIDITrackAction String
  | SetMIDIChannelAction String
  | SetMIDIMappingAction String
  | SetMIDICCNumberAction String
  | SetMIDIValueMinAction String
  | SetMIDIValueMaxAction String
  | SetMIDIInterpolationAction String
  | SetMIDILayerNameAction String
  | ConvertMIDIAction
  -- Path animation actions
  | TogglePathAnimSection
  | SetPathSplineAction String
  | SetPathTargetAction String
  | SetPathModeAction String
  | SetPathSensitivityAction String
  | SetPathSmoothingAction String
  | SetPathFeatureAction String
  | CreatePathAnimatorAction

type Slots = ()

-- =============================================================================
--                                                                  // component
-- =============================================================================

component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { input: input
  , baseId: "audio-panel"
  , stemSectionExpanded: false
  , selectedModel: "htdemucs"
  , isSeparating: false
  , separationProgress: 0
  , separationMessage: ""
  , separatedStems: []
  , separationError: Nothing
  , beatSectionExpanded: false
  , beatPreset: PresetCustom
  , timeSignature: 4
  , fillGaps: true
  , snapToGrid: true
  , tolerance: 5
  , isAnalyzingBeats: false
  , beatGrid: Nothing
  , convertSectionExpanded: false
  , convertLayerName: "Audio Amplitude"
  , convertAmplitudeScale: 100
  , convertSmoothing: 3
  , isConverting: false
  , convertResult: Nothing
  , convertError: Nothing
  , midiSectionExpanded: false
  , midiAvailable: true
  , midiDevices: []
  , isRefreshingMIDI: false
  , midiMonitorEnabled: false
  , recentMIDIMessages: []
  , midiFileSectionExpanded: false
  , loadedMIDIFile: Nothing
  , isLoadingMIDI: false
  , midiTrackIndex: Nothing
  , midiChannel: Nothing
  , midiMappingType: "noteVelocity"
  , midiCCNumber: 1
  , midiValueMin: 0
  , midiValueMax: 100
  , midiInterpolation: "linear"
  , midiLayerName: "MIDI Animation"
  , isConvertingMIDI: false
  , midiConvertResult: Nothing
  , midiConvertError: Nothing
  , pathAnimSectionExpanded: false
  , pathAnimSplineId: ""
  , pathAnimTargetId: ""
  , pathAnimMode: "amplitude"
  , pathAnimSensitivity: 1.0
  , pathAnimSmoothing: 0.3
  , pathAnimFeature: FeatureAmplitude
  , isCreatingPathAnim: false
  , pathAnimResult: Nothing
  , pathAnimError: Nothing
  }

-- =============================================================================
--                                                                     // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "audio-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , ARIA.label "Audio Source"
    ]
    [ renderHeader state
    , if state.input.hasAudio
        then renderContent state
        else renderEmptyState
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader _state =
  HH.div
    [ cls [ "panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.span
        [ cls [ "panel-title" ]
        , HP.attr (HH.AttrName "style") titleStyle
        ]
        [ HH.text "Audio Source" ]
    , HH.div
        [ cls [ "header-actions" ]
        , HP.attr (HH.AttrName "style") headerActionsStyle
        ]
        [ HH.button
            [ cls [ "action-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Load Audio"
            , HP.attr (HH.AttrName "style") actionBtnStyle
            , HE.onClick \_ -> LoadAudioAction
            ]
            [ HH.text "\x{1F4C1}" ]
        ]
    ]

renderEmptyState :: forall m. H.ComponentHTML Action Slots m
renderEmptyState =
  HH.div
    [ cls [ "empty-state" ]
    , HP.attr (HH.AttrName "style") emptyStateStyle
    ]
    [ HH.div [ cls [ "empty-icon" ], HP.attr (HH.AttrName "style") emptyIconStyle ] [ HH.text "\x{1F3B5}" ]
    , HH.p_ [ HH.text "No audio loaded" ]
    , HH.button
        [ cls [ "load-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") loadBtnStyle
        , HE.onClick \_ -> LoadAudioAction
        ]
        [ HH.text "Load Audio File" ]
    , HH.p [ cls [ "hint" ], HP.attr (HH.AttrName "style") hintStyle ] 
        [ HH.text "Supports MP3, WAV, OGG, AAC" ]
    ]

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "panel-content" ]
    , HP.attr (HH.AttrName "style") contentStyle
    ]
    [ renderAudioInfo state
    , renderVolumeControl state
    , renderWaveformSection
    , renderStemSection state
    , renderBeatSection state
    , renderConvertSection state
    , renderMIDISection state
    , renderMIDIFileSection state
    , renderPathAnimSection state
    ]

-- =============================================================================
--                                                           // audio info
-- =============================================================================

renderAudioInfo :: forall m. State -> H.ComponentHTML Action Slots m
renderAudioInfo state =
  HH.div
    [ cls [ "audio-info" ]
    , HP.attr (HH.AttrName "style") audioInfoStyle
    ]
    [ HH.div
        [ cls [ "file-info" ]
        , HP.attr (HH.AttrName "style") fileInfoStyle
        ]
        [ HH.span [ cls [ "file-icon" ], HP.attr (HH.AttrName "style") fileIconStyle ] [ HH.text "\x{1F3B5}" ]
        , HH.div
            [ cls [ "file-details" ]
            , HP.attr (HH.AttrName "style") fileDetailsStyle
            ]
            [ HH.span [ cls [ "file-name" ], HP.attr (HH.AttrName "style") fileNameStyle ] 
                [ HH.text state.input.audioFileName ]
            , HH.span [ cls [ "file-meta" ], HP.attr (HH.AttrName "style") fileMetaStyle ] 
                [ HH.text (state.input.audioDuration <> " \x{2022} " <> state.input.audioSampleRate) ]
            ]
        , HH.button
            [ cls [ "remove-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Remove Audio"
            , HP.attr (HH.AttrName "style") removeBtnStyle
            , HE.onClick \_ -> RemoveAudioAction
            ]
            [ HH.text "\x{00D7}" ]
        ]
    ]

renderVolumeControl :: forall m. State -> H.ComponentHTML Action Slots m
renderVolumeControl state =
  HH.div
    [ cls [ "control-section" ]
    , HP.attr (HH.AttrName "style") controlSectionStyle
    ]
    [ HH.div
        [ cls [ "control-row" ]
        , HP.attr (HH.AttrName "style") controlRowStyle
        ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Master Vol" ]
        , HH.input
            [ HP.type_ HP.InputRange
            , HP.value (show state.input.volume)
            , HP.attr (HH.AttrName "min") "0"
            , HP.attr (HH.AttrName "max") "100"
            , HP.attr (HH.AttrName "style") volumeSliderStyle
            , HE.onValueInput SetVolumeAction
            ]
        , HH.span [ HP.attr (HH.AttrName "style") volumeValueStyle ] 
            [ HH.text (show state.input.volume <> "%") ]
        , HH.button
            [ cls [ "mute-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Mute"
            , HP.attr (HH.AttrName "style") (muteBtnStyle state.input.isMuted)
            , HP.attr (HH.AttrName "data-state") (if state.input.isMuted then "muted" else "unmuted")
            , HE.onClick \_ -> ToggleMuteAction
            ]
            [ HH.text (if state.input.isMuted then "\x{1F507}" else "\x{1F50A}") ]
        ]
    ]

renderWaveformSection :: forall m. H.ComponentHTML Action Slots m
renderWaveformSection =
  HH.div
    [ cls [ "waveform-section" ]
    , HP.attr (HH.AttrName "style") waveformSectionStyle
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ]
        [ HH.span [ cls [ "section-title" ] ] [ HH.text "Waveform" ] ]
    , HH.div
        [ cls [ "waveform-display" ]
        , HP.attr (HH.AttrName "style") waveformDisplayStyle
        , HP.id "audio-waveform-canvas"
        ]
        []
    ]

-- =============================================================================
--                                                           // stem section
-- =============================================================================

renderStemSection :: forall m. State -> H.ComponentHTML Action Slots m
renderStemSection state =
  HH.div
    [ cls [ "stem-section" ]
    , HP.attr (HH.AttrName "style") collapsibleSectionStyle
    ]
    [ renderCollapsibleHeader "Stem Separation" state.stemSectionExpanded ToggleStemSection
        (if Array.null state.separatedStems then Nothing else Just (show (Array.length state.separatedStems) <> " stems"))
    , if state.stemSectionExpanded
        then renderStemContent state
        else HH.text ""
    ]

renderStemContent :: forall m. State -> H.ComponentHTML Action Slots m
renderStemContent state =
  HH.div
    [ cls [ "section-content" ]
    , HP.attr (HH.AttrName "style") sectionContentStyle
    ]
    [ HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Model" ]
        , HH.select
            [ HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetModelAction
            ]
            [ HH.option [ HP.value "htdemucs", HP.selected (state.selectedModel == "htdemucs") ] 
                [ HH.text "HT-Demucs (Recommended)" ]
            , HH.option [ HP.value "mdx", HP.selected (state.selectedModel == "mdx") ] 
                [ HH.text "MDX-Net" ]
            ]
        ]
    , HH.div
        [ cls [ "preset-buttons" ]
        , HP.attr (HH.AttrName "style") presetButtonsStyle
        ]
        [ stemPresetBtn "\x{1F3A4} Vocals" (SeparateStemAction StemVocals) state.isSeparating
        , stemPresetBtn "\x{1F941} Drums" (SeparateStemAction StemDrums) state.isSeparating
        , stemPresetBtn "\x{1F3B8} Bass" (SeparateStemAction StemBass) state.isSeparating
        , stemPresetBtn "\x{1F3B6} Karaoke" MakeKaraokeAction state.isSeparating
        , stemPresetBtn "\x{2728} All Stems" SeparateAllAction state.isSeparating
        ]
    , if state.isSeparating
        then renderStemProgress state
        else HH.text ""
    , if not (Array.null state.separatedStems)
        then renderStemsList state
        else HH.text ""
    , case state.separationError of
        Just err -> renderErrorMessage err
        Nothing -> HH.text ""
    ]

stemPresetBtn :: forall m. String -> Action -> Boolean -> H.ComponentHTML Action Slots m
stemPresetBtn label action disabled =
  HH.button
    [ cls [ "preset-btn" ]
    , HP.type_ HP.ButtonButton
    , HP.disabled disabled
    , HP.attr (HH.AttrName "style") presetBtnStyle
    , HE.onClick \_ -> action
    ]
    [ HH.text label ]

renderStemProgress :: forall m. State -> H.ComponentHTML Action Slots m
renderStemProgress state =
  HH.div
    [ cls [ "progress-row" ]
    , HP.attr (HH.AttrName "style") progressRowStyle
    ]
    [ HH.div [ cls [ "progress-bar" ], HP.attr (HH.AttrName "style") progressBarStyle ]
        [ HH.div 
            [ cls [ "progress-fill" ]
            , HP.attr (HH.AttrName "style") (progressFillStyle state.separationProgress)
            ] 
            [] 
        ]
    , HH.span [ cls [ "progress-text" ], HP.attr (HH.AttrName "style") progressTextStyle ] 
        [ HH.text state.separationMessage ]
    ]

renderStemsList :: forall m. State -> H.ComponentHTML Action Slots m
renderStemsList state =
  HH.div
    [ cls [ "stems-list" ]
    , HP.attr (HH.AttrName "style") stemsListStyle
    ]
    ([ HH.div [ cls [ "stems-header" ], HP.attr (HH.AttrName "style") stemsHeaderStyle ]
        [ HH.text "Separated Stems"
        , case state.input.activeStemName of
            Just name -> HH.span [ cls [ "active-stem-badge" ], HP.attr (HH.AttrName "style") activeStemBadgeStyle ] 
                          [ HH.text ("Active: " <> name) ]
            Nothing -> HH.text ""
        ]
    , renderMainAudioItem state
    ] <> map (renderStemItem state) state.separatedStems)

renderMainAudioItem :: forall m. State -> H.ComponentHTML Action Slots m
renderMainAudioItem state =
  let
    isActive = case state.input.activeStemName of
      Nothing -> true
      Just _ -> false
  in
  HH.div
    [ cls [ "stem-item" ]
    , HP.attr (HH.AttrName "style") (stemItemStyle isActive)
    ]
    [ HH.span [ cls [ "stem-icon" ] ] [ HH.text "\x{1F3B5}" ]
    , HH.span [ cls [ "stem-name" ] ] [ HH.text "Main Audio" ]
    , HH.button
        [ cls [ "stem-btn", "use" ]
        , HP.type_ HP.ButtonButton
        , HP.disabled isActive
        , HP.title "Use Main Audio for Reactivity"
        , HP.attr (HH.AttrName "style") stemUseBtnStyle
        , HE.onClick \_ -> UseMainAudioAction
        ]
        [ HH.text (if isActive then "\x{2713}" else "\x{1F517}") ]
    ]

renderStemItem :: forall m. State -> StemInfo -> H.ComponentHTML Action Slots m
renderStemItem state stem =
  let
    isActive = state.input.activeStemName == Just stem.name
  in
  HH.div
    [ cls [ "stem-item" ]
    , HP.attr (HH.AttrName "style") (stemItemStyle isActive)
    ]
    [ HH.span [ cls [ "stem-icon" ] ] [ HH.text (getStemIcon stem.name) ]
    , HH.span [ cls [ "stem-name" ] ] [ HH.text stem.name ]
    , HH.button
        [ cls [ "stem-btn", "play" ]
        , HP.type_ HP.ButtonButton
        , HP.title "Play"
        , HP.attr (HH.AttrName "style") stemBtnStyle
        , HE.onClick \_ -> PlayStemAction stem.name
        ]
        [ HH.text "\x{25B6}" ]
    , HH.button
        [ cls [ "stem-btn", "download" ]
        , HP.type_ HP.ButtonButton
        , HP.title "Download"
        , HP.attr (HH.AttrName "style") stemBtnStyle
        , HE.onClick \_ -> DownloadStemAction stem.name
        ]
        [ HH.text "\x{2B07}" ]
    , HH.button
        [ cls [ "stem-btn", "use" ]
        , HP.type_ HP.ButtonButton
        , HP.title "Use for Audio Reactivity"
        , HP.attr (HH.AttrName "style") stemUseBtnStyle
        , HE.onClick \_ -> UseStemAction stem.name
        ]
        [ HH.text (if isActive then "\x{2713}" else "\x{1F517}") ]
    ]

getStemIcon :: String -> String
getStemIcon = case _ of
  "vocals" -> "\x{1F3A4}"
  "drums" -> "\x{1F941}"
  "bass" -> "\x{1F3B8}"
  "other" -> "\x{1F3B9}"
  "karaoke" -> "\x{1F3B6}"
  _ -> "\x{1F3B5}"

-- =============================================================================
--                                                           // beat section
-- =============================================================================

renderBeatSection :: forall m. State -> H.ComponentHTML Action Slots m
renderBeatSection state =
  HH.div
    [ cls [ "beat-section" ]
    , HP.attr (HH.AttrName "style") collapsibleSectionStyle
    ]
    [ renderCollapsibleHeader "Beat Detection" state.beatSectionExpanded ToggleBeatSection
        (map (\bg -> show (floor bg.bpm) <> " BPM") state.beatGrid)
    , if state.beatSectionExpanded
        then renderBeatContent state
        else HH.text ""
    ]

renderBeatContent :: forall m. State -> H.ComponentHTML Action Slots m
renderBeatContent state =
  HH.div
    [ cls [ "section-content" ]
    , HP.attr (HH.AttrName "style") sectionContentStyle
    ]
    [ HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Genre Preset" ]
        , HH.select
            [ HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetBeatPresetAction
            ]
            [ HH.option [ HP.value "", HP.selected (state.beatPreset == PresetCustom) ] [ HH.text "Custom" ]
            , HH.option [ HP.value "electronic", HP.selected (state.beatPreset == PresetElectronic) ] [ HH.text "Electronic/EDM" ]
            , HH.option [ HP.value "rock", HP.selected (state.beatPreset == PresetRock) ] [ HH.text "Rock/Pop" ]
            , HH.option [ HP.value "hiphop", HP.selected (state.beatPreset == PresetHipHop) ] [ HH.text "Hip-Hop" ]
            , HH.option [ HP.value "jazz", HP.selected (state.beatPreset == PresetJazz) ] [ HH.text "Jazz" ]
            , HH.option [ HP.value "classical", HP.selected (state.beatPreset == PresetClassical) ] [ HH.text "Classical" ]
            , HH.option [ HP.value "waltz", HP.selected (state.beatPreset == PresetWaltz) ] [ HH.text "Waltz (3/4)" ]
            ]
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Time Signature" ]
        , HH.select
            [ HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetTimeSignatureAction
            ]
            [ HH.option [ HP.value "4", HP.selected (state.timeSignature == 4) ] [ HH.text "4/4" ]
            , HH.option [ HP.value "3", HP.selected (state.timeSignature == 3) ] [ HH.text "3/4" ]
            , HH.option [ HP.value "6", HP.selected (state.timeSignature == 6) ] [ HH.text "6/8" ]
            , HH.option [ HP.value "2", HP.selected (state.timeSignature == 2) ] [ HH.text "2/4" ]
            ]
        ]
    , HH.div [ cls [ "checkbox-row" ], HP.attr (HH.AttrName "style") checkboxRowStyle ]
        [ HH.label_
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.fillGaps
                , HE.onChecked SetFillGapsAction
                ]
            , HH.text " Fill Missing Beats"
            ]
        ]
    , HH.div [ cls [ "checkbox-row" ], HP.attr (HH.AttrName "style") checkboxRowStyle ]
        [ HH.label_
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.snapToGrid
                , HE.onChecked SetSnapToGridAction
                ]
            , HH.text " Snap to Grid"
            ]
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Tolerance" ]
        , HH.input
            [ HP.type_ HP.InputRange
            , HP.value (show state.tolerance)
            , HP.attr (HH.AttrName "min") "1"
            , HP.attr (HH.AttrName "max") "10"
            , HP.attr (HH.AttrName "style") sliderStyle
            , HE.onValueInput SetToleranceAction
            ]
        , HH.span [ HP.attr (HH.AttrName "style") valueStyle ] [ HH.text (show state.tolerance <> "f") ]
        ]
    , HH.button
        [ cls [ "analyze-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.disabled state.isAnalyzingBeats
        , HP.attr (HH.AttrName "style") analyzeBtnStyle
        , HE.onClick \_ -> AnalyzeBeatsAction
        ]
        [ HH.text (if state.isAnalyzingBeats then "Analyzing..." else "\x{1F3B5} Analyze Beats") ]
    , case state.beatGrid of
        Just bg -> renderBeatResults bg state
        Nothing -> HH.text ""
    ]

renderBeatResults :: forall m. BeatGridInfo -> State -> H.ComponentHTML Action Slots m
renderBeatResults bg _state =
  HH.div
    [ cls [ "beat-results" ]
    , HP.attr (HH.AttrName "style") beatResultsStyle
    ]
    [ HH.div [ cls [ "result-row" ], HP.attr (HH.AttrName "style") resultRowStyle ]
        [ HH.span [ cls [ "result-label" ] ] [ HH.text "Detected BPM:" ]
        , HH.span [ cls [ "result-value" ] ] [ HH.text (show (floor bg.bpm)) ]
        , HH.span [ cls [ "confidence" ], HP.attr (HH.AttrName "style") (confidenceStyle bg.bpmConfidence) ] 
            [ HH.text (show (floor (bg.bpmConfidence * 100.0)) <> "% confidence") ]
        ]
    , HH.div [ cls [ "result-row" ], HP.attr (HH.AttrName "style") resultRowStyle ]
        [ HH.span [ cls [ "result-label" ] ] [ HH.text "Beats Found:" ]
        , HH.span [ cls [ "result-value" ] ] [ HH.text (show bg.beatCount) ]
        ]
    , HH.div [ cls [ "result-row" ], HP.attr (HH.AttrName "style") resultRowStyle ]
        [ HH.span [ cls [ "result-label" ] ] [ HH.text "Downbeats:" ]
        , HH.span [ cls [ "result-value" ] ] [ HH.text (show bg.downbeatCount) ]
        ]
    , HH.div [ cls [ "beat-actions" ], HP.attr (HH.AttrName "style") beatActionsStyle ]
        [ HH.button
            [ cls [ "beat-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Snap keyframes to beats"
            , HP.attr (HH.AttrName "style") beatBtnStyle
            , HE.onClick \_ -> SnapToBeatsAction
            ]
            [ HH.text "\x{23F1} Snap to Beats" ]
        , HH.button
            [ cls [ "beat-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Add markers at beats"
            , HP.attr (HH.AttrName "style") beatBtnStyle
            , HE.onClick \_ -> AddBeatMarkersAction
            ]
            [ HH.text "\x{1F4CD} Add Markers" ]
        ]
    ]

-- =============================================================================
--                                                        // convert section
-- =============================================================================

renderConvertSection :: forall m. State -> H.ComponentHTML Action Slots m
renderConvertSection state =
  HH.div
    [ cls [ "convert-section" ]
    , HP.attr (HH.AttrName "style") collapsibleSectionStyle
    ]
    [ renderCollapsibleHeader "Convert to Keyframes" state.convertSectionExpanded ToggleConvertSection Nothing
    , if state.convertSectionExpanded
        then renderConvertContent state
        else HH.text ""
    ]

renderConvertContent :: forall m. State -> H.ComponentHTML Action Slots m
renderConvertContent state =
  HH.div
    [ cls [ "section-content" ]
    , HP.attr (HH.AttrName "style") sectionContentStyle
    ]
    [ HH.p [ cls [ "section-description" ], HP.attr (HH.AttrName "style") sectionDescStyle ]
        [ HH.text "Creates a null layer with amplitude keyframes for expression linking." ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Layer Name" ]
        , HH.input
            [ HP.type_ HP.InputText
            , HP.value state.convertLayerName
            , HP.placeholder "Audio Amplitude"
            , HP.attr (HH.AttrName "style") textInputStyle
            , HE.onValueInput SetConvertLayerNameAction
            ]
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Amplitude Scale" ]
        , HH.input
            [ HP.type_ HP.InputRange
            , HP.value (show state.convertAmplitudeScale)
            , HP.attr (HH.AttrName "min") "10"
            , HP.attr (HH.AttrName "max") "200"
            , HP.attr (HH.AttrName "style") sliderStyle
            , HE.onValueInput SetConvertAmplitudeScaleAction
            ]
        , HH.span [ HP.attr (HH.AttrName "style") valueStyle ] [ HH.text (show state.convertAmplitudeScale <> "%") ]
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Smoothing" ]
        , HH.input
            [ HP.type_ HP.InputRange
            , HP.value (show state.convertSmoothing)
            , HP.attr (HH.AttrName "min") "0"
            , HP.attr (HH.AttrName "max") "20"
            , HP.attr (HH.AttrName "style") sliderStyle
            , HE.onValueInput SetConvertSmoothingAction
            ]
        , HH.span [ HP.attr (HH.AttrName "style") valueStyle ] [ HH.text (show state.convertSmoothing <> " frames") ]
        ]
    , HH.button
        [ cls [ "convert-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.disabled state.isConverting
        , HP.attr (HH.AttrName "style") convertBtnStyle
        , HE.onClick \_ -> ConvertAudioAction
        ]
        [ HH.text (if state.isConverting then "Converting..." else "\x{1F3B9} Convert Audio to Keyframes") ]
    , case state.convertResult of
        Just result -> renderConvertResult result
        Nothing -> HH.text ""
    , case state.convertError of
        Just err -> renderErrorMessage err
        Nothing -> HH.text ""
    ]

renderConvertResult :: forall m. { layerName :: String, keyframeCount :: Int } -> H.ComponentHTML Action Slots m
renderConvertResult result =
  HH.div
    [ cls [ "convert-result" ]
    , HP.attr (HH.AttrName "style") convertResultStyle
    ]
    [ HH.span [ cls [ "result-icon" ] ] [ HH.text "\x{2705}" ]
    , HH.span_ [ HH.text ("Created \"" <> result.layerName <> "\" with " <> show result.keyframeCount <> " keyframes") ]
    ]

-- =============================================================================
--                                                         // MIDI section
-- =============================================================================

renderMIDISection :: forall m. State -> H.ComponentHTML Action Slots m
renderMIDISection state =
  HH.div
    [ cls [ "midi-section" ]
    , HP.attr (HH.AttrName "style") collapsibleSectionStyle
    ]
    [ renderCollapsibleHeader "MIDI Input" state.midiSectionExpanded ToggleMIDISection
        (if Array.null state.midiDevices 
          then if state.midiAvailable then Nothing else Just "Unavailable"
          else Just (show (Array.length state.midiDevices) <> " device" <> (if Array.length state.midiDevices /= 1 then "s" else "")))
    , if state.midiSectionExpanded
        then renderMIDIContent state
        else HH.text ""
    ]

renderMIDIContent :: forall m. State -> H.ComponentHTML Action Slots m
renderMIDIContent state =
  HH.div
    [ cls [ "section-content" ]
    , HP.attr (HH.AttrName "style") sectionContentStyle
    ]
    [ if not state.midiAvailable
        then HH.div [ cls [ "midi-unavailable" ], HP.attr (HH.AttrName "style") midiUnavailableStyle ]
              [ HH.p_ [ HH.text "Web MIDI API is not available in this browser." ]
              , HH.p [ cls [ "hint" ], HP.attr (HH.AttrName "style") hintStyle ] [ HH.text "Try Chrome or Edge for MIDI support." ]
              ]
        else HH.div_
              [ HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
                  [ HH.button
                      [ cls [ "refresh-btn" ]
                      , HP.type_ HP.ButtonButton
                      , HP.disabled state.isRefreshingMIDI
                      , HP.attr (HH.AttrName "style") refreshBtnStyle
                      , HE.onClick \_ -> RefreshMIDIAction
                      ]
                      [ HH.text (if state.isRefreshingMIDI then "Scanning..." else "\x{1F504} Scan Devices") ]
                  ]
              , if Array.null state.midiDevices
                  then HH.div [ cls [ "no-devices" ], HP.attr (HH.AttrName "style") noDevicesStyle ]
                        [ HH.p_ [ HH.text "No MIDI devices found." ]
                        , HH.p [ cls [ "hint" ], HP.attr (HH.AttrName "style") hintStyle ] 
                            [ HH.text "Connect a MIDI controller and click \"Scan Devices\"." ]
                        ]
                  else HH.div_
                        [ HH.div [ cls [ "device-list" ], HP.attr (HH.AttrName "style") deviceListStyle ]
                            (map renderMIDIDevice state.midiDevices)
                        , renderMIDIMonitor state
                        ]
              ]
    ]

renderMIDIDevice :: forall m. MIDIDeviceInfo -> H.ComponentHTML Action Slots m
renderMIDIDevice device =
  HH.div
    [ cls [ "device-item" ]
    , HP.attr (HH.AttrName "style") deviceItemStyle
    ]
    [ HH.span [ cls [ "device-icon" ] ] [ HH.text "\x{1F3B9}" ]
    , HH.div
        [ cls [ "device-info" ]
        , HP.attr (HH.AttrName "style") deviceInfoStyle
        ]
        [ HH.span [ cls [ "device-name" ], HP.attr (HH.AttrName "style") deviceNameStyle ] [ HH.text device.name ]
        , HH.span [ cls [ "device-meta" ], HP.attr (HH.AttrName "style") deviceMetaStyle ] 
            [ HH.text (device.manufacturer <> " \x{2022} " <> device.deviceType) ]
        ]
    , HH.span [ cls [ "device-status" ], HP.attr (HH.AttrName "style") (deviceStatusStyle device.state) ] 
        [ HH.text device.state ]
    ]

renderMIDIMonitor :: forall m. State -> H.ComponentHTML Action Slots m
renderMIDIMonitor state =
  HH.div
    [ cls [ "midi-monitor" ]
    , HP.attr (HH.AttrName "style") midiMonitorStyle
    ]
    [ HH.div [ cls [ "monitor-header" ], HP.attr (HH.AttrName "style") monitorHeaderStyle ]
        [ HH.span_ [ HH.text "MIDI Monitor" ]
        , HH.label [ cls [ "monitor-toggle" ], HP.attr (HH.AttrName "style") monitorToggleStyle ]
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.midiMonitorEnabled
                , HE.onChecked SetMIDIMonitorAction
                ]
            , HH.span_ [ HH.text (if state.midiMonitorEnabled then "On" else "Off") ]
            ]
        ]
    , if state.midiMonitorEnabled
        then HH.div [ cls [ "monitor-messages" ], HP.attr (HH.AttrName "style") monitorMessagesStyle ]
              (if Array.null state.recentMIDIMessages
                then [ HH.div [ cls [ "no-messages" ], HP.attr (HH.AttrName "style") noMessagesStyle ]
                        [ HH.text "No MIDI messages yet. Move a fader or press a key." ] ]
                else map renderMIDIMessage state.recentMIDIMessages)
        else HH.text ""
    ]

renderMIDIMessage :: forall m. MIDIMessage -> H.ComponentHTML Action Slots m
renderMIDIMessage msg =
  HH.div
    [ cls [ "midi-message" ]
    , HP.attr (HH.AttrName "style") midiMessageStyle
    ]
    [ HH.span [ cls [ "msg-type" ] ] [ HH.text msg.messageType ]
    , HH.span [ cls [ "msg-channel" ] ] [ HH.text ("Ch" <> show msg.channel) ]
    , case msg.note of
        Just n -> HH.span [ cls [ "msg-note" ] ] [ HH.text (midiNoteToName n) ]
        Nothing -> HH.text ""
    , case msg.value of
        Just v -> HH.span [ cls [ "msg-value" ] ] [ HH.text (show v) ]
        Nothing -> HH.text ""
    , case msg.velocity of
        Just vel -> HH.span [ cls [ "msg-velocity" ] ] [ HH.text ("vel " <> show vel) ]
        Nothing -> HH.text ""
    ]

midiNoteToName :: Int -> String
midiNoteToName = Utils.midiNoteToName

-- =============================================================================
--                                                      // MIDI file section
-- =============================================================================

renderMIDIFileSection :: forall m. State -> H.ComponentHTML Action Slots m
renderMIDIFileSection state =
  HH.div
    [ cls [ "midi-file-section" ]
    , HP.attr (HH.AttrName "style") collapsibleSectionStyle
    ]
    [ renderCollapsibleHeader "MIDI File to Keyframes" state.midiFileSectionExpanded ToggleMIDIFileSection
        (map (\f -> show f.totalNotes <> " notes") state.loadedMIDIFile)
    , if state.midiFileSectionExpanded
        then renderMIDIFileContent state
        else HH.text ""
    ]

renderMIDIFileContent :: forall m. State -> H.ComponentHTML Action Slots m
renderMIDIFileContent state =
  HH.div
    [ cls [ "section-content" ]
    , HP.attr (HH.AttrName "style") sectionContentStyle
    ]
    [ case state.loadedMIDIFile of
        Nothing ->
          HH.div [ cls [ "midi-load-area" ] ]
            [ HH.button
                [ cls [ "load-midi-btn" ]
                , HP.type_ HP.ButtonButton
                , HP.disabled state.isLoadingMIDI
                , HP.attr (HH.AttrName "style") loadMidiBtnStyle
                , HE.onClick \_ -> LoadMIDIFileAction
                ]
                [ HH.text (if state.isLoadingMIDI then "Loading..." else "\x{1F3B9} Load MIDI File (.mid)") ]
            ]
        Just midiFile -> renderMIDIFileInfo midiFile state
    ]

renderMIDIFileInfo :: forall m. MIDIFileInfo -> State -> H.ComponentHTML Action Slots m
renderMIDIFileInfo midiFile state =
  HH.div [ cls [ "midi-file-info" ] ]
    [ HH.div [ cls [ "file-row" ], HP.attr (HH.AttrName "style") fileRowStyle ]
        [ HH.span [ cls [ "file-icon" ] ] [ HH.text "\x{1F3B9}" ]
        , HH.div [ cls [ "file-details" ], HP.attr (HH.AttrName "style") fileDetailsStyle ]
            [ HH.span [ cls [ "file-name" ], HP.attr (HH.AttrName "style") fileNameStyle ] [ HH.text midiFile.fileName ]
            , HH.span [ cls [ "file-meta" ], HP.attr (HH.AttrName "style") fileMetaStyle ] 
                [ HH.text (show midiFile.trackCount <> " tracks \x{2022} " <> show midiFile.totalNotes <> " notes \x{2022} " <> midiFile.bpm <> " BPM") ]
            ]
        , HH.button
            [ cls [ "remove-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Remove"
            , HP.attr (HH.AttrName "style") removeBtnStyle
            , HE.onClick \_ -> RemoveMIDIFileAction
            ]
            [ HH.text "\x{00D7}" ]
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Track" ]
        , HH.select
            [ HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetMIDITrackAction
            ]
            ([ HH.option [ HP.value "", HP.selected (state.midiTrackIndex == Nothing) ] [ HH.text "All Tracks" ] ]
              <> map (\t -> HH.option 
                  [ HP.value (show t.index), HP.selected (state.midiTrackIndex == Just t.index) ] 
                  [ HH.text (t.name <> " (" <> show t.noteCount <> " notes)") ]) midiFile.tracks)
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Channel" ]
        , HH.select
            [ HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetMIDIChannelAction
            ]
            ([ HH.option [ HP.value "", HP.selected (state.midiChannel == Nothing) ] [ HH.text "All Channels" ] ]
              <> map (\ch -> HH.option 
                  [ HP.value (show ch), HP.selected (state.midiChannel == Just ch) ] 
                  [ HH.text ("Channel " <> show (ch + 1)) ]) (Array.range 0 15))
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Map" ]
        , HH.select
            [ HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetMIDIMappingAction
            ]
            [ HH.option [ HP.value "noteOnOff", HP.selected (state.midiMappingType == "noteOnOff") ] [ HH.text "Note On/Off" ]
            , HH.option [ HP.value "noteVelocity", HP.selected (state.midiMappingType == "noteVelocity") ] [ HH.text "Note Velocity" ]
            , HH.option [ HP.value "notePitch", HP.selected (state.midiMappingType == "notePitch") ] [ HH.text "Note Pitch" ]
            , HH.option [ HP.value "controlChange", HP.selected (state.midiMappingType == "controlChange") ] [ HH.text "Control Change (CC)" ]
            ]
        ]
    , if state.midiMappingType == "controlChange"
        then HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
              [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "CC #" ]
              , HH.select
                  [ HP.attr (HH.AttrName "style") selectStyle
                  , HE.onValueChange SetMIDICCNumberAction
                  ]
                  [ HH.option [ HP.value "1", HP.selected (state.midiCCNumber == 1) ] [ HH.text "1 - Modulation" ]
                  , HH.option [ HP.value "7", HP.selected (state.midiCCNumber == 7) ] [ HH.text "7 - Volume" ]
                  , HH.option [ HP.value "10", HP.selected (state.midiCCNumber == 10) ] [ HH.text "10 - Pan" ]
                  , HH.option [ HP.value "11", HP.selected (state.midiCCNumber == 11) ] [ HH.text "11 - Expression" ]
                  , HH.option [ HP.value "64", HP.selected (state.midiCCNumber == 64) ] [ HH.text "64 - Sustain" ]
                  , HH.option [ HP.value "74", HP.selected (state.midiCCNumber == 74) ] [ HH.text "74 - Cutoff" ]
                  ]
              ]
        else HH.text ""
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Min" ]
        , HH.input
            [ HP.type_ HP.InputNumber
            , HP.value (show state.midiValueMin)
            , HP.attr (HH.AttrName "style") smallInputStyle
            , HE.onValueInput SetMIDIValueMinAction
            ]
        , HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Max" ]
        , HH.input
            [ HP.type_ HP.InputNumber
            , HP.value (show state.midiValueMax)
            , HP.attr (HH.AttrName "style") smallInputStyle
            , HE.onValueInput SetMIDIValueMaxAction
            ]
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Easing" ]
        , HH.select
            [ HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetMIDIInterpolationAction
            ]
            [ HH.option [ HP.value "hold", HP.selected (state.midiInterpolation == "hold") ] [ HH.text "Hold (Step)" ]
            , HH.option [ HP.value "linear", HP.selected (state.midiInterpolation == "linear") ] [ HH.text "Linear" ]
            , HH.option [ HP.value "bezier", HP.selected (state.midiInterpolation == "bezier") ] [ HH.text "Bezier" ]
            ]
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Layer" ]
        , HH.input
            [ HP.type_ HP.InputText
            , HP.value state.midiLayerName
            , HP.placeholder "MIDI Animation"
            , HP.attr (HH.AttrName "style") textInputStyle
            , HE.onValueInput SetMIDILayerNameAction
            ]
        ]
    , HH.button
        [ cls [ "convert-midi-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.disabled state.isConvertingMIDI
        , HP.attr (HH.AttrName "style") convertMidiBtnStyle
        , HE.onClick \_ -> ConvertMIDIAction
        ]
        [ HH.text (if state.isConvertingMIDI then "Converting..." else "\x{2728} Create Keyframes") ]
    , case state.midiConvertResult of
        Just result -> renderConvertResult result
        Nothing -> HH.text ""
    , case state.midiConvertError of
        Just err -> renderErrorMessage err
        Nothing -> HH.text ""
    ]

-- =============================================================================
--                                                    // path anim section
-- =============================================================================

renderPathAnimSection :: forall m. State -> H.ComponentHTML Action Slots m
renderPathAnimSection state =
  HH.div
    [ cls [ "path-anim-section" ]
    , HP.attr (HH.AttrName "style") collapsibleSectionStyle
    ]
    [ renderCollapsibleHeader "Audio Path Animation" state.pathAnimSectionExpanded TogglePathAnimSection Nothing
    , if state.pathAnimSectionExpanded
        then renderPathAnimContent state
        else HH.text ""
    ]

renderPathAnimContent :: forall m. State -> H.ComponentHTML Action Slots m
renderPathAnimContent state =
  HH.div
    [ cls [ "section-content" ]
    , HP.attr (HH.AttrName "style") sectionContentStyle
    ]
    [ HH.p [ cls [ "section-description" ], HP.attr (HH.AttrName "style") sectionDescStyle ]
        [ HH.text "Animate objects along a spline path driven by audio features." ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Path Layer" ]
        , HH.select
            [ HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetPathSplineAction
            ]
            ([ HH.option [ HP.value "", HP.selected (state.pathAnimSplineId == "") ] [ HH.text "Select a spline/path layer..." ] ]
              <> map (\l -> HH.option [ HP.value l.id, HP.selected (state.pathAnimSplineId == l.id) ] [ HH.text l.name ]) state.input.splineLayers)
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Target" ]
        , HH.select
            [ HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetPathTargetAction
            ]
            ([ HH.option [ HP.value "", HP.selected (state.pathAnimTargetId == "") ] [ HH.text "Select target layer..." ] ]
              <> map (\l -> HH.option [ HP.value l.id, HP.selected (state.pathAnimTargetId == l.id) ] [ HH.text l.name ]) state.input.animatableLayers)
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Mode" ]
        , HH.select
            [ HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetPathModeAction
            ]
            [ HH.option [ HP.value "amplitude", HP.selected (state.pathAnimMode == "amplitude") ] 
                [ HH.text "Amplitude (position maps to volume)" ]
            , HH.option [ HP.value "accumulate", HP.selected (state.pathAnimMode == "accumulate") ] 
                [ HH.text "Accumulate (travels on sound)" ]
            ]
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Sensitivity" ]
        , HH.input
            [ HP.type_ HP.InputRange
            , HP.value (formatNumber state.pathAnimSensitivity)
            , HP.attr (HH.AttrName "min") "0.1"
            , HP.attr (HH.AttrName "max") "3"
            , HP.attr (HH.AttrName "step") "0.1"
            , HP.attr (HH.AttrName "style") sliderStyle
            , HE.onValueInput SetPathSensitivityAction
            ]
        , HH.span [ HP.attr (HH.AttrName "style") valueStyle ] [ HH.text (formatNumber state.pathAnimSensitivity <> "x") ]
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Smoothing" ]
        , HH.input
            [ HP.type_ HP.InputRange
            , HP.value (formatNumber state.pathAnimSmoothing)
            , HP.attr (HH.AttrName "min") "0"
            , HP.attr (HH.AttrName "max") "0.9"
            , HP.attr (HH.AttrName "step") "0.05"
            , HP.attr (HH.AttrName "style") sliderStyle
            , HE.onValueInput SetPathSmoothingAction
            ]
        , HH.span [ HP.attr (HH.AttrName "style") valueStyle ] [ HH.text (show (floor (state.pathAnimSmoothing * 100.0)) <> "%") ]
        ]
    , HH.div [ cls [ "control-row" ], HP.attr (HH.AttrName "style") controlRowStyle ]
        [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text "Audio Source" ]
        , HH.select
            [ HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetPathFeatureAction
            ]
            [ HH.option [ HP.value "amplitude", HP.selected (state.pathAnimFeature == FeatureAmplitude) ] [ HH.text "Overall Amplitude" ]
            , HH.option [ HP.value "bass", HP.selected (state.pathAnimFeature == FeatureBass) ] [ HH.text "Bass (20-250 Hz)" ]
            , HH.option [ HP.value "mid", HP.selected (state.pathAnimFeature == FeatureMid) ] [ HH.text "Mid (500-2000 Hz)" ]
            , HH.option [ HP.value "high", HP.selected (state.pathAnimFeature == FeatureHigh) ] [ HH.text "High (4000+ Hz)" ]
            ]
        ]
    , HH.button
        [ cls [ "create-path-anim-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.disabled (state.pathAnimSplineId == "" || state.pathAnimTargetId == "" || state.isCreatingPathAnim)
        , HP.attr (HH.AttrName "style") createPathAnimBtnStyle
        , HE.onClick \_ -> CreatePathAnimatorAction
        ]
        [ HH.text (if state.isCreatingPathAnim then "Creating..." else "\x{1F3B5} Create Path Animator") ]
    , case state.pathAnimResult of
        Just result -> HH.div [ cls [ "convert-result" ], HP.attr (HH.AttrName "style") convertResultStyle ]
            [ HH.span [ cls [ "result-icon" ] ] [ HH.text "\x{2705}" ]
            , HH.span_ [ HH.text result ]
            ]
        Nothing -> HH.text ""
    , case state.pathAnimError of
        Just err -> renderErrorMessage err
        Nothing -> HH.text ""
    ]

-- =============================================================================
--                                                           // shared renders
-- =============================================================================

renderCollapsibleHeader :: forall m. String -> Boolean -> Action -> Maybe String -> H.ComponentHTML Action Slots m
renderCollapsibleHeader title isExpanded toggleAction maybeBadge =
  HH.div
    [ cls [ "section-header", "clickable" ]
    , HP.attr (HH.AttrName "style") clickableSectionHeaderStyle
    , HP.attr (HH.AttrName "role") "button"
    , ARIA.expanded (show isExpanded)
    , HP.tabIndex 0
    , HE.onClick \_ -> toggleAction
    ]
    [ HH.span [ cls [ "expand-icon" ] ] [ HH.text (if isExpanded then "\x{25BC}" else "\x{25B6}") ]
    , HH.span [ cls [ "section-title" ] ] [ HH.text title ]
    , case maybeBadge of
        Just badge -> HH.span [ cls [ "badge" ], HP.attr (HH.AttrName "style") badgeStyle ] [ HH.text badge ]
        Nothing -> HH.text ""
    ]

renderErrorMessage :: forall m. String -> H.ComponentHTML Action Slots m
renderErrorMessage err =
  HH.div
    [ cls [ "error-message" ]
    , HP.attr (HH.AttrName "style") errorMessageStyle
    ]
    [ HH.text err ]

-- =============================================================================
--                                                                    // helpers
-- =============================================================================

formatNumber :: Number -> String
formatNumber = Utils.formatFixed 1

floor :: Number -> Int
floor = Utils.floor

parseIntSafe :: String -> Int -> Int
parseIntSafe str defaultVal = Utils.parseIntOr defaultVal str

parseFloatSafe :: String -> Number -> Number
parseFloatSafe str defaultVal = Utils.parseFloatOr defaultVal str

-- =============================================================================
--                                                                     // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: #1e1e1e; color: #ccc; font-size: 13px;"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 8px; background: #252525; border-bottom: 1px solid #111; font-weight: 600;"

titleStyle :: String
titleStyle =
  "font-weight: 600;"

headerActionsStyle :: String
headerActionsStyle =
  "display: flex; gap: 4px;"

actionBtnStyle :: String
actionBtnStyle =
  "background: none; border: none; cursor: pointer; color: #aaa; " <>
  "padding: 4px; border-radius: 3px;"

contentStyle :: String
contentStyle =
  "flex: 1; overflow-y: auto;"

emptyStateStyle :: String
emptyStateStyle =
  "display: flex; flex-direction: column; align-items: center; " <>
  "justify-content: center; height: 100%; padding: 20px; text-align: center;"

emptyIconStyle :: String
emptyIconStyle =
  "font-size: 48px; margin-bottom: 16px; opacity: 0.5;"

loadBtnStyle :: String
loadBtnStyle =
  "padding: 10px 20px; background: #4a90d9; border: none; " <>
  "border-radius: 6px; color: white; font-size: 14px; cursor: pointer; margin: 12px 0;"

hintStyle :: String
hintStyle =
  "font-size: 12px; color: #666; margin: 0;"

audioInfoStyle :: String
audioInfoStyle =
  "padding: 10px; background: #222; border-bottom: 1px solid #333;"

fileInfoStyle :: String
fileInfoStyle =
  "display: flex; align-items: center; gap: 8px;"

fileIconStyle :: String
fileIconStyle =
  "font-size: 20px;"

fileDetailsStyle :: String
fileDetailsStyle =
  "flex: 1; display: flex; flex-direction: column;"

fileNameStyle :: String
fileNameStyle =
  "font-weight: 500; color: #eee;"

fileMetaStyle :: String
fileMetaStyle =
  "color: #888; font-size: 12px;"

removeBtnStyle :: String
removeBtnStyle =
  "background: none; border: none; color: #666; cursor: pointer; " <>
  "font-size: 16px; padding: 4px;"

controlSectionStyle :: String
controlSectionStyle =
  "padding: 10px; border-bottom: 1px solid #333;"

controlRowStyle :: String
controlRowStyle =
  "display: flex; align-items: center; gap: 8px;"

labelStyle :: String
labelStyle =
  "width: 70px; color: #888; flex-shrink: 0;"

volumeSliderStyle :: String
volumeSliderStyle =
  "flex: 1;"

volumeValueStyle :: String
volumeValueStyle =
  "min-width: 40px; text-align: right; font-size: 12px;"

muteBtnStyle :: Boolean -> String
muteBtnStyle isMuted =
  "width: 28px; height: 28px; padding: 0; border: none; " <>
  "background: transparent; border-radius: 3px; cursor: pointer; " <>
  "font-size: 14px; flex-shrink: 0; " <>
  "color: " <> (if isMuted then "#ff6b6b" else "#888") <> ";"

waveformSectionStyle :: String
waveformSectionStyle =
  "padding: 10px; border-bottom: 1px solid #333; background: #1a1a1a;"

sectionHeaderStyle :: String
sectionHeaderStyle =
  "display: flex; align-items: center; margin-bottom: 8px;"

waveformDisplayStyle :: String
waveformDisplayStyle =
  "height: 60px; background: #1a1a1a; border-radius: 4px; overflow: hidden;"

collapsibleSectionStyle :: String
collapsibleSectionStyle =
  "border-top: 1px solid #333;"

clickableSectionHeaderStyle :: String
clickableSectionHeaderStyle =
  "display: flex; align-items: center; gap: 8px; padding: 8px 10px; " <>
  "cursor: pointer; background: #2a2a2a;"

badgeStyle :: String
badgeStyle =
  "margin-left: auto; background: #4a90d9; color: white; " <>
  "padding: 2px 8px; border-radius: 10px; font-size: 11px;"

sectionContentStyle :: String
sectionContentStyle =
  "padding: 10px; background: #222;"

sectionDescStyle :: String
sectionDescStyle =
  "font-size: 12px; color: #888; margin: 0 0 12px 0;"

presetButtonsStyle :: String
presetButtonsStyle =
  "display: flex; flex-wrap: wrap; gap: 6px; margin: 8px 0;"

presetBtnStyle :: String
presetBtnStyle =
  "padding: 6px 12px; background: #333; border: 1px solid #444; " <>
  "border-radius: 4px; color: #ccc; font-size: 12px; cursor: pointer;"

progressRowStyle :: String
progressRowStyle =
  "display: flex; align-items: center; gap: 8px; margin: 8px 0;"

progressBarStyle :: String
progressBarStyle =
  "flex: 1; height: 6px; background: #333; border-radius: 3px; overflow: hidden;"

progressFillStyle :: Int -> String
progressFillStyle pct =
  "height: 100%; background: #4a90d9; width: " <> show pct <> "%;"

progressTextStyle :: String
progressTextStyle =
  "font-size: 11px; color: #888; min-width: 80px;"

stemsListStyle :: String
stemsListStyle =
  "margin-top: 12px;"

stemsHeaderStyle :: String
stemsHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "margin-bottom: 8px; font-weight: 500;"

activeStemBadgeStyle :: String
activeStemBadgeStyle =
  "background: #22c55e; color: white; padding: 2px 8px; " <>
  "border-radius: 10px; font-size: 11px;"

stemItemStyle :: Boolean -> String
stemItemStyle isActive =
  "display: flex; align-items: center; gap: 8px; padding: 8px; " <>
  "background: " <> (if isActive then "rgba(74, 144, 217, 0.2)" else "#2a2a2a") <> "; " <>
  "border-radius: 4px; margin-bottom: 4px;"

stemBtnStyle :: String
stemBtnStyle =
  "padding: 4px 8px; background: #333; border: 1px solid #444; " <>
  "border-radius: 3px; color: #ccc; font-size: 12px; cursor: pointer;"

stemUseBtnStyle :: String
stemUseBtnStyle =
  "padding: 4px 8px; background: #4a90d9; border: none; " <>
  "border-radius: 3px; color: white; font-size: 12px; cursor: pointer;"

selectStyle :: String
selectStyle =
  "flex: 1; padding: 6px 8px; background: #333; border: 1px solid #444; " <>
  "border-radius: 4px; color: #ccc; font-size: 12px;"

checkboxRowStyle :: String
checkboxRowStyle =
  "display: flex; align-items: center; gap: 8px; margin: 4px 0;"

sliderStyle :: String
sliderStyle =
  "flex: 1;"

valueStyle :: String
valueStyle =
  "min-width: 30px; text-align: right; font-size: 12px; color: #888;"

analyzeBtnStyle :: String
analyzeBtnStyle =
  "width: 100%; padding: 10px; background: #4a90d9; border: none; " <>
  "border-radius: 6px; color: white; font-size: 13px; cursor: pointer; margin-top: 8px;"

beatResultsStyle :: String
beatResultsStyle =
  "margin-top: 12px; padding: 10px; background: #2a2a2a; border-radius: 6px;"

resultRowStyle :: String
resultRowStyle =
  "display: flex; align-items: center; gap: 8px; margin-bottom: 4px;"

confidenceStyle :: Number -> String
confidenceStyle conf =
  let
    color = if conf >= 0.8 then "#22c55e" 
            else if conf >= 0.5 then "#eab308" 
            else "#ef4444"
  in
    "font-size: 11px; color: " <> color <> ";"

beatActionsStyle :: String
beatActionsStyle =
  "display: flex; gap: 8px; margin-top: 8px;"

beatBtnStyle :: String
beatBtnStyle =
  "flex: 1; padding: 8px; background: #333; border: 1px solid #444; " <>
  "border-radius: 4px; color: #ccc; font-size: 12px; cursor: pointer;"

textInputStyle :: String
textInputStyle =
  "flex: 1; padding: 6px 8px; background: #333; border: 1px solid #444; " <>
  "border-radius: 4px; color: #ccc; font-size: 12px;"

convertBtnStyle :: String
convertBtnStyle =
  "width: 100%; padding: 10px; background: #8B5CF6; border: none; " <>
  "border-radius: 6px; color: white; font-size: 13px; cursor: pointer; margin-top: 8px;"

convertResultStyle :: String
convertResultStyle =
  "display: flex; align-items: center; gap: 8px; padding: 10px; " <>
  "background: rgba(34, 197, 94, 0.1); border: 1px solid rgba(34, 197, 94, 0.3); " <>
  "border-radius: 6px; margin-top: 8px; color: #22c55e;"

errorMessageStyle :: String
errorMessageStyle =
  "padding: 10px; background: rgba(239, 68, 68, 0.1); " <>
  "border: 1px solid rgba(239, 68, 68, 0.3); border-radius: 6px; " <>
  "margin-top: 8px; color: #ef4444; font-size: 12px;"

midiUnavailableStyle :: String
midiUnavailableStyle =
  "text-align: center; padding: 16px;"

refreshBtnStyle :: String
refreshBtnStyle =
  "padding: 8px 16px; background: #333; border: 1px solid #444; " <>
  "border-radius: 4px; color: #ccc; font-size: 12px; cursor: pointer;"

noDevicesStyle :: String
noDevicesStyle =
  "text-align: center; padding: 16px; color: #888;"

deviceListStyle :: String
deviceListStyle =
  "margin: 8px 0;"

deviceItemStyle :: String
deviceItemStyle =
  "display: flex; align-items: center; gap: 8px; padding: 8px; " <>
  "background: #2a2a2a; border-radius: 4px; margin-bottom: 4px;"

deviceInfoStyle :: String
deviceInfoStyle =
  "flex: 1; display: flex; flex-direction: column;"

deviceNameStyle :: String
deviceNameStyle =
  "font-weight: 500; color: #eee;"

deviceMetaStyle :: String
deviceMetaStyle =
  "font-size: 11px; color: #888;"

deviceStatusStyle :: String -> String
deviceStatusStyle state =
  let color = if state == "connected" then "#22c55e" else "#888"
  in "font-size: 11px; color: " <> color <> ";"

midiMonitorStyle :: String
midiMonitorStyle =
  "margin-top: 12px; background: #1a1a1a; border-radius: 6px; overflow: hidden;"

monitorHeaderStyle :: String
monitorHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 8px 10px; background: #252525;"

monitorToggleStyle :: String
monitorToggleStyle =
  "display: flex; align-items: center; gap: 6px; cursor: pointer; font-size: 12px;"

monitorMessagesStyle :: String
monitorMessagesStyle =
  "max-height: 150px; overflow-y: auto; padding: 8px;"

noMessagesStyle :: String
noMessagesStyle =
  "text-align: center; color: #666; padding: 16px; font-size: 12px;"

midiMessageStyle :: String
midiMessageStyle =
  "display: flex; gap: 8px; padding: 4px 8px; background: #252525; " <>
  "border-radius: 3px; margin-bottom: 4px; font-size: 11px; font-family: monospace;"

fileRowStyle :: String
fileRowStyle =
  "display: flex; align-items: center; gap: 8px; margin-bottom: 12px;"

smallInputStyle :: String
smallInputStyle =
  "width: 60px; padding: 6px 8px; background: #333; border: 1px solid #444; " <>
  "border-radius: 4px; color: #ccc; font-size: 12px;"

loadMidiBtnStyle :: String
loadMidiBtnStyle =
  "width: 100%; padding: 12px; background: #333; border: 1px solid #444; " <>
  "border-radius: 6px; color: #ccc; font-size: 13px; cursor: pointer;"

convertMidiBtnStyle :: String
convertMidiBtnStyle =
  "width: 100%; padding: 10px; background: #8B5CF6; border: none; " <>
  "border-radius: 6px; color: white; font-size: 13px; cursor: pointer; margin-top: 8px;"

createPathAnimBtnStyle :: String
createPathAnimBtnStyle =
  "width: 100%; padding: 10px; background: #4a90d9; border: none; " <>
  "border-radius: 6px; color: white; font-size: 13px; cursor: pointer; margin-top: 8px;"

-- =============================================================================
--                                                                    // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  Receive input -> H.modify_ _ { input = input }

  LoadAudioAction -> H.raise LoadAudioFile
  RemoveAudioAction -> H.raise RemoveAudio
  SetVolumeAction val -> H.raise (SetVolume (parseIntSafe val 100))
  ToggleMuteAction -> H.raise ToggleMute

  -- Stem actions
  ToggleStemSection -> H.modify_ \s -> s { stemSectionExpanded = not s.stemSectionExpanded }
  SetModelAction val -> H.modify_ _ { selectedModel = val }
  SeparateStemAction stemType -> H.raise (SeparateStem stemType)
  SeparateAllAction -> H.raise SeparateAllStems
  MakeKaraokeAction -> H.raise MakeKaraoke
  PlayStemAction name -> H.raise (PlayStem name)
  DownloadStemAction name -> H.raise (DownloadStem name)
  UseStemAction name -> H.raise (UseStemForReactivity name)
  UseMainAudioAction -> H.raise UseMainAudio

  -- Beat actions
  ToggleBeatSection -> H.modify_ \s -> s { beatSectionExpanded = not s.beatSectionExpanded }
  SetBeatPresetAction val -> do
    let preset = parsePreset val
    H.modify_ _ { beatPreset = preset }
    H.raise (SetBeatPreset preset)
  SetTimeSignatureAction val -> do
    let ts = parseIntSafe val 4
    H.modify_ _ { timeSignature = ts }
    H.raise (SetTimeSignature ts)
  SetFillGapsAction checked -> do
    H.modify_ _ { fillGaps = checked }
    H.raise (SetFillGaps checked)
  SetSnapToGridAction checked -> do
    H.modify_ _ { snapToGrid = checked }
    H.raise (SetSnapToGrid checked)
  SetToleranceAction val -> do
    let tol = parseIntSafe val 5
    H.modify_ _ { tolerance = tol }
    H.raise (SetTolerance tol)
  AnalyzeBeatsAction -> do
    H.modify_ _ { isAnalyzingBeats = true }
    H.raise AnalyzeBeats
  SnapToBeatsAction -> H.raise SnapToBeats
  AddBeatMarkersAction -> H.raise AddBeatMarkers

  -- Convert actions
  ToggleConvertSection -> H.modify_ \s -> s { convertSectionExpanded = not s.convertSectionExpanded }
  SetConvertLayerNameAction val -> H.modify_ _ { convertLayerName = val }
  SetConvertAmplitudeScaleAction val -> H.modify_ _ { convertAmplitudeScale = parseIntSafe val 100 }
  SetConvertSmoothingAction val -> H.modify_ _ { convertSmoothing = parseIntSafe val 3 }
  ConvertAudioAction -> do
    state <- H.get
    H.modify_ _ { isConverting = true, convertError = Nothing, convertResult = Nothing }
    H.raise $ ConvertAudioToKeyframes
      { layerName: state.convertLayerName
      , amplitudeScale: state.convertAmplitudeScale
      , smoothing: state.convertSmoothing
      }

  -- MIDI actions
  ToggleMIDISection -> H.modify_ \s -> s { midiSectionExpanded = not s.midiSectionExpanded }
  RefreshMIDIAction -> do
    H.modify_ _ { isRefreshingMIDI = true }
    H.raise RefreshMIDIDevices
  SetMIDIMonitorAction checked -> do
    H.modify_ _ { midiMonitorEnabled = checked }
    H.raise (SetMIDIMonitor checked)

  -- MIDI file actions
  ToggleMIDIFileSection -> H.modify_ \s -> s { midiFileSectionExpanded = not s.midiFileSectionExpanded }
  LoadMIDIFileAction -> do
    H.modify_ _ { isLoadingMIDI = true }
    H.raise LoadMIDIFile
  RemoveMIDIFileAction -> do
    H.modify_ _ { loadedMIDIFile = Nothing, midiConvertResult = Nothing, midiConvertError = Nothing }
    H.raise RemoveMIDIFile
  SetMIDITrackAction val -> H.modify_ _ { midiTrackIndex = if val == "" then Nothing else Just (parseIntSafe val 0) }
  SetMIDIChannelAction val -> H.modify_ _ { midiChannel = if val == "" then Nothing else Just (parseIntSafe val 0) }
  SetMIDIMappingAction val -> H.modify_ _ { midiMappingType = val }
  SetMIDICCNumberAction val -> H.modify_ _ { midiCCNumber = parseIntSafe val 1 }
  SetMIDIValueMinAction val -> H.modify_ _ { midiValueMin = parseIntSafe val 0 }
  SetMIDIValueMaxAction val -> H.modify_ _ { midiValueMax = parseIntSafe val 100 }
  SetMIDIInterpolationAction val -> H.modify_ _ { midiInterpolation = val }
  SetMIDILayerNameAction val -> H.modify_ _ { midiLayerName = val }
  ConvertMIDIAction -> do
    state <- H.get
    H.modify_ _ { isConvertingMIDI = true, midiConvertError = Nothing, midiConvertResult = Nothing }
    H.raise $ ConvertMIDIToKeyframes
      { trackIndex: state.midiTrackIndex
      , channel: state.midiChannel
      , mappingType: state.midiMappingType
      , ccNumber: state.midiCCNumber
      , valueMin: state.midiValueMin
      , valueMax: state.midiValueMax
      , interpolation: state.midiInterpolation
      , layerName: state.midiLayerName
      }

  -- Path animation actions
  TogglePathAnimSection -> H.modify_ \s -> s { pathAnimSectionExpanded = not s.pathAnimSectionExpanded }
  SetPathSplineAction val -> H.modify_ _ { pathAnimSplineId = val }
  SetPathTargetAction val -> H.modify_ _ { pathAnimTargetId = val }
  SetPathModeAction val -> H.modify_ _ { pathAnimMode = val }
  SetPathSensitivityAction val -> H.modify_ _ { pathAnimSensitivity = parseFloatSafe val 1.0 }
  SetPathSmoothingAction val -> H.modify_ _ { pathAnimSmoothing = parseFloatSafe val 0.3 }
  SetPathFeatureAction val -> H.modify_ _ { pathAnimFeature = parseFeature val }
  CreatePathAnimatorAction -> do
    state <- H.get
    H.modify_ _ { isCreatingPathAnim = true, pathAnimError = Nothing, pathAnimResult = Nothing }
    H.raise $ CreatePathAnimator
      { splineId: state.pathAnimSplineId
      , targetId: state.pathAnimTargetId
      , mode: state.pathAnimMode
      , sensitivity: state.pathAnimSensitivity
      , smoothing: state.pathAnimSmoothing
      , feature: state.pathAnimFeature
      }

parsePreset :: String -> BeatPreset
parsePreset = case _ of
  "electronic" -> PresetElectronic
  "rock" -> PresetRock
  "hiphop" -> PresetHipHop
  "jazz" -> PresetJazz
  "classical" -> PresetClassical
  "waltz" -> PresetWaltz
  _ -> PresetCustom

parseFeature :: String -> AudioFeature
parseFeature = case _ of
  "bass" -> FeatureBass
  "mid" -> FeatureMid
  "high" -> FeatureHigh
  _ -> FeatureAmplitude

-- =============================================================================
--                                                                    // queries
-- =============================================================================

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  SetStemSeparationProgress progress message next -> do
    H.modify_ _ { separationProgress = progress, separationMessage = message }
    pure (Just next)

  SetSeparatedStems stems next -> do
    H.modify_ _ { separatedStems = stems, isSeparating = false, separationError = Nothing }
    pure (Just next)

  SetStemError err next -> do
    H.modify_ _ { separationError = Just err, isSeparating = false }
    pure (Just next)

  SetBeatGrid beatGrid next -> do
    H.modify_ _ { beatGrid = Just beatGrid, isAnalyzingBeats = false }
    pure (Just next)

  SetMIDIDevices devices next -> do
    H.modify_ _ { midiDevices = devices, isRefreshingMIDI = false }
    pure (Just next)

  AddMIDIMessage msg next -> do
    H.modify_ \s -> s { recentMIDIMessages = Array.take 10 ([msg] <> s.recentMIDIMessages) }
    pure (Just next)

  SetMIDIFile midiFile next -> do
    H.modify_ _ { loadedMIDIFile = Just midiFile, isLoadingMIDI = false }
    pure (Just next)
