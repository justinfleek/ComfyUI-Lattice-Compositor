-- | Generative Flow Panel Component
-- |
-- | Data-driven trajectory generation for Wan-Move animation.
-- | Features:
-- | - Flow pattern presets (neural flow, cosmic dust, etc.)
-- | - Custom pattern types (spiral, wave, explosion, vortex, etc.)
-- | - Configurable trajectory count, duration, resolution
-- | - Seed control with randomization
-- | - Data-driven trajectory modification
-- | - Preview canvas rendering
-- | - JSON and Wan-Move export
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/GenerativeFlowPanel.vue
module Lattice.UI.Components.GenerativeFlowPanel
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , FlowConfig
  , PatternType(..)
  , DataMapping(..)
  ) where

import Prelude

import Control.Monad (when)
import Data.Array (length)
import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(..), isJust)
import Data.String (Pattern(..), split)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls, RemoteData(..))
import Lattice.UI.Utils (formatFixed)

-- =============================================================================
--                                                                      // types
-- =============================================================================

type Input =
  { dataAssets :: Array DataAsset
  }

data Output
  = GeneratePreview FlowConfig
  | ExportJSON FlowConfig
  | ExportWanMove FlowConfig

data Query a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                         // domain // types
-- =============================================================================

type DataAsset =
  { name :: String
  }

type FlowConfig =
  { preset :: String
  , patternType :: PatternType
  , numPoints :: Int
  , numFrames :: Int
  , width :: Int
  , height :: Int
  , seed :: Int
  , useDataDriven :: Boolean
  , dataAssetName :: Maybe String
  , dataMapping :: DataMapping
  }

data PatternType
  = Spiral
  | Wave
  | Explosion
  | Vortex
  | DataRiver
  | Morph
  | Swarm

derive instance eqPatternType :: Eq PatternType

instance showPatternType :: Show PatternType where
  show = case _ of
    Spiral -> "spiral"
    Wave -> "wave"
    Explosion -> "explosion"
    Vortex -> "vortex"
    DataRiver -> "data-river"
    Morph -> "morph"
    Swarm -> "swarm"

data DataMapping
  = MappingSpeed
  | MappingAmplitude
  | MappingPhase
  | MappingDirection

derive instance eqDataMapping :: Eq DataMapping

instance showDataMapping :: Show DataMapping where
  show = case _ of
    MappingSpeed -> "speed"
    MappingAmplitude -> "amplitude"
    MappingPhase -> "phase"
    MappingDirection -> "direction"

type GenerationResult =
  { numPoints :: Int
  , numFrames :: Int
  }

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { dataAssets :: Array DataAsset
  , selectedPreset :: String
  , patternType :: PatternType
  , numPoints :: Int
  , numFrames :: Int
  , width :: Int
  , height :: Int
  , seed :: Int
  , useDataDriven :: Boolean
  , selectedDataAsset :: String
  , dataMapping :: DataMapping
  , generationState :: RemoteData String GenerationResult
  , statusMessage :: Maybe StatusMessage
  , baseId :: String
  }

type StatusMessage =
  { text :: String
  , messageType :: StatusType
  }

data StatusType
  = StatusSuccess
  | StatusError
  | StatusInfo

derive instance eqStatusType :: Eq StatusType

data Action
  = Initialize
  | Receive Input
  | SetPreset String
  | SetPatternType PatternType
  | SetNumPoints Int
  | SetNumFrames Int
  | SetWidth Int
  | SetHeight Int
  | SetResolution Int Int
  | SetSeed Int
  | RandomizeSeed
  | ToggleDataDriven
  | SetSelectedDataAsset String
  | SetDataMapping DataMapping
  | TriggerPreview
  | TriggerExportJSON
  | TriggerExportWanMove

type Slots = ()

-- =============================================================================
--                                                               // component
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
  { dataAssets: input.dataAssets
  , selectedPreset: "neural-flow"
  , patternType: Spiral
  , numPoints: 200
  , numFrames: 81      -- 5 seconds @ 16fps
  , width: 832
  , height: 480
  , seed: 42
  , useDataDriven: false
  , selectedDataAsset: case Array.head input.dataAssets of
      Just asset -> asset.name
      Nothing -> ""
  , dataMapping: MappingSpeed
  , generationState: NotAsked
  , statusMessage: Nothing
  , baseId: "lattice-generative-flow"
  }

-- =============================================================================
--                                                                    // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-generative-flow-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , HP.attr (HH.AttrName "aria-label") "Generative Flow"
    ]
    [ renderHeader
    , renderPresetSection state
    , renderPatternSection state
    , renderTrajectorySection state
    , renderDurationSection state
    , renderResolutionSection state
    , renderSeedSection state
    , renderDataDrivenSection state
    , renderPreviewSection state
    , renderActionsSection state
    , renderStatusSection state
    ]

renderHeader :: forall m. H.ComponentHTML Action Slots m
renderHeader =
  HH.div
    [ cls [ "panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.h3 [ HP.attr (HH.AttrName "style") headerTitleStyle ] 
        [ HH.text "Generative Flow" ]
    , HH.span [ cls [ "subtitle" ], HP.attr (HH.AttrName "style") subtitleStyle ]
        [ HH.text "Data-driven trajectory generation for Wan-Move" ]
    ]

-- =============================================================================
--                                                             // form sections
-- =============================================================================

renderPresetSection :: forall m. State -> H.ComponentHTML Action Slots m
renderPresetSection state =
  HH.div
    [ cls [ "section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.label [ cls [ "section-label" ], HP.attr (HH.AttrName "style") sectionLabelStyle ]
        [ HH.text "Flow Pattern" ]
    , HH.select
        [ cls [ "preset-select" ]
        , HP.attr (HH.AttrName "style") selectStyle
        , HP.value state.selectedPreset
        , HE.onValueInput SetPreset
        , HP.attr (HH.AttrName "aria-label") "Flow pattern preset"
        ]
        [ HH.option [ HP.value "custom" ] [ HH.text "Custom Pattern" ]
        , HH.optgroup [ HP.attr (HH.AttrName "label") "Presets" ]
            (map renderPresetOption flowPresets)
        ]
    ]

renderPresetOption :: forall m. String -> H.ComponentHTML Action Slots m
renderPresetOption preset =
  HH.option [ HP.value preset ] [ HH.text (formatPresetName preset) ]

renderPatternSection :: forall m. State -> H.ComponentHTML Action Slots m
renderPatternSection state =
  if state.selectedPreset == "custom"
    then HH.div
           [ cls [ "section" ]
           , HP.attr (HH.AttrName "style") sectionStyle
           ]
           [ HH.label [ cls [ "section-label" ], HP.attr (HH.AttrName "style") sectionLabelStyle ]
               [ HH.text "Pattern Type" ]
           , HH.select
               [ cls [ "pattern-select" ]
               , HP.attr (HH.AttrName "style") selectStyle
               , HP.value (show state.patternType)
               , HE.onValueInput \v -> SetPatternType (parsePatternType v)
               , HP.attr (HH.AttrName "aria-label") "Pattern type"
               ]
               [ HH.option [ HP.value "spiral", HP.selected (state.patternType == Spiral) ] 
                   [ HH.text "Spiral" ]
               , HH.option [ HP.value "wave", HP.selected (state.patternType == Wave) ] 
                   [ HH.text "Wave" ]
               , HH.option [ HP.value "explosion", HP.selected (state.patternType == Explosion) ] 
                   [ HH.text "Explosion" ]
               , HH.option [ HP.value "vortex", HP.selected (state.patternType == Vortex) ] 
                   [ HH.text "Vortex" ]
               , HH.option [ HP.value "data-river", HP.selected (state.patternType == DataRiver) ] 
                   [ HH.text "Data River" ]
               , HH.option [ HP.value "morph", HP.selected (state.patternType == Morph) ] 
                   [ HH.text "Morph" ]
               , HH.option [ HP.value "swarm", HP.selected (state.patternType == Swarm) ] 
                   [ HH.text "Swarm" ]
               ]
           ]
    else HH.text ""

renderTrajectorySection :: forall m. State -> H.ComponentHTML Action Slots m
renderTrajectorySection state =
  HH.div
    [ cls [ "section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.label [ cls [ "section-label" ], HP.attr (HH.AttrName "style") sectionLabelStyle ]
        [ HH.text "Trajectory Count" ]
    , HH.div
        [ cls [ "input-row" ]
        , HP.attr (HH.AttrName "style") inputRowStyle
        ]
        [ HH.input
            [ HP.type_ HP.InputNumber
            , cls [ "num-input" ]
            , HP.attr (HH.AttrName "style") numInputStyle
            , HP.min 10.0
            , HP.max 1000.0
            , HP.step (HP.Step 10.0)
            , HP.value (show state.numPoints)
            , HE.onValueInput \v -> SetNumPoints (parseIntOr 200 v)
            , HP.attr (HH.AttrName "aria-label") "Trajectory count"
            ]
        , HH.span [ cls [ "input-hint" ], HP.attr (HH.AttrName "style") inputHintStyle ]
            [ HH.text "10-1000 trajectories" ]
        ]
    ]

renderDurationSection :: forall m. State -> H.ComponentHTML Action Slots m
renderDurationSection state =
  let
    durationSeconds = toNumber state.numFrames / 16.0
  in
    HH.div
      [ cls [ "section" ]
      , HP.attr (HH.AttrName "style") sectionStyle
      ]
      [ HH.label [ cls [ "section-label" ], HP.attr (HH.AttrName "style") sectionLabelStyle ]
          [ HH.text "Duration" ]
      , HH.div
          [ cls [ "input-row" ]
          , HP.attr (HH.AttrName "style") inputRowStyle
          ]
          [ HH.input
              [ HP.type_ HP.InputNumber
              , cls [ "num-input" ]
              , HP.attr (HH.AttrName "style") numInputStyle
              , HP.min 17.0
              , HP.max 241.0
              , HP.step (HP.Step 16.0)
              , HP.value (show state.numFrames)
              , HE.onValueInput \v -> SetNumFrames (parseIntOr 81 v)
              , HP.attr (HH.AttrName "aria-label") "Number of frames"
              ]
          , HH.span [ cls [ "input-hint" ], HP.attr (HH.AttrName "style") inputHintStyle ]
              [ HH.text (formatFixed 1 durationSeconds <> "s @ 16fps") ]
          ]
      ]

renderResolutionSection :: forall m. State -> H.ComponentHTML Action Slots m
renderResolutionSection state =
  HH.div
    [ cls [ "section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.label [ cls [ "section-label" ], HP.attr (HH.AttrName "style") sectionLabelStyle ]
        [ HH.text "Resolution" ]
    , HH.div
        [ cls [ "resolution-row" ]
        , HP.attr (HH.AttrName "style") resolutionRowStyle
        ]
        [ HH.input
            [ HP.type_ HP.InputNumber
            , cls [ "res-input" ]
            , HP.attr (HH.AttrName "style") resInputStyle
            , HP.min 256.0
            , HP.max 1920.0
            , HP.step (HP.Step 8.0)
            , HP.value (show state.width)
            , HE.onValueInput \v -> SetWidth (parseIntOr 832 v)
            , HP.attr (HH.AttrName "aria-label") "Width"
            ]
        , HH.span [ cls [ "res-x" ], HP.attr (HH.AttrName "style") resXStyle ] 
            [ HH.text "×" ]
        , HH.input
            [ HP.type_ HP.InputNumber
            , cls [ "res-input" ]
            , HP.attr (HH.AttrName "style") resInputStyle
            , HP.min 256.0
            , HP.max 1080.0
            , HP.step (HP.Step 8.0)
            , HP.value (show state.height)
            , HE.onValueInput \v -> SetHeight (parseIntOr 480 v)
            , HP.attr (HH.AttrName "aria-label") "Height"
            ]
        , HH.button
            [ cls [ "preset-btn" ]
            , HP.attr (HH.AttrName "style") presetBtnStyle
            , HP.attr (HH.AttrName "title") "Wan-Move default"
            , HE.onClick \_ -> SetResolution 832 480
            ]
            [ HH.text "480p" ]
        , HH.button
            [ cls [ "preset-btn" ]
            , HP.attr (HH.AttrName "style") presetBtnStyle
            , HE.onClick \_ -> SetResolution 1280 720
            ]
            [ HH.text "720p" ]
        ]
    ]

renderSeedSection :: forall m. State -> H.ComponentHTML Action Slots m
renderSeedSection state =
  HH.div
    [ cls [ "section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.label [ cls [ "section-label" ], HP.attr (HH.AttrName "style") sectionLabelStyle ]
        [ HH.text "Seed" ]
    , HH.div
        [ cls [ "input-row" ]
        , HP.attr (HH.AttrName "style") inputRowStyle
        ]
        [ HH.input
            [ HP.type_ HP.InputNumber
            , cls [ "num-input" ]
            , HP.attr (HH.AttrName "style") numInputStyle
            , HP.min 0.0
            , HP.value (show state.seed)
            , HE.onValueInput \v -> SetSeed (parseIntOr 42 v)
            , HP.attr (HH.AttrName "aria-label") "Random seed"
            ]
        , HH.button
            [ cls [ "randomize-btn" ]
            , HP.attr (HH.AttrName "style") randomizeBtnStyle
            , HP.attr (HH.AttrName "title") "Randomize seed"
            , HP.attr (HH.AttrName "aria-label") "Randomize seed"
            , HE.onClick \_ -> RandomizeSeed
            ]
            [ HH.text "🎲" ]
        ]
    ]

renderDataDrivenSection :: forall m. State -> H.ComponentHTML Action Slots m
renderDataDrivenSection state =
  if length state.dataAssets > 0
    then HH.div
           [ cls [ "section" ]
           , HP.attr (HH.AttrName "style") sectionStyle
           ]
           [ HH.label
               [ cls [ "section-label" ]
               , HP.attr (HH.AttrName "style") (sectionLabelStyle <> " cursor: pointer;")
               ]
               [ HH.input
                   [ HP.type_ HP.InputCheckbox
                   , HP.checked state.useDataDriven
                   , HE.onChecked \_ -> ToggleDataDriven
                   , HP.attr (HH.AttrName "aria-label") "Use data source"
                   ]
               , HH.text " Use Data Source"
               ]
           , if state.useDataDriven
               then HH.div
                      [ cls [ "data-options" ]
                      , HP.attr (HH.AttrName "style") dataOptionsStyle
                      ]
                      [ HH.select
                          [ cls [ "data-select" ]
                          , HP.attr (HH.AttrName "style") selectStyle
                          , HP.value state.selectedDataAsset
                          , HE.onValueInput SetSelectedDataAsset
                          , HP.attr (HH.AttrName "aria-label") "Data asset"
                          ]
                          (map renderDataAssetOption state.dataAssets)
                      , HH.select
                          [ cls [ "data-select" ]
                          , HP.attr (HH.AttrName "style") selectStyle
                          , HP.value (show state.dataMapping)
                          , HE.onValueInput \v -> SetDataMapping (parseDataMapping v)
                          , HP.attr (HH.AttrName "aria-label") "Data mapping"
                          ]
                          [ HH.option [ HP.value "speed", HP.selected (state.dataMapping == MappingSpeed) ] 
                              [ HH.text "Speed" ]
                          , HH.option [ HP.value "amplitude", HP.selected (state.dataMapping == MappingAmplitude) ] 
                              [ HH.text "Amplitude" ]
                          , HH.option [ HP.value "phase", HP.selected (state.dataMapping == MappingPhase) ] 
                              [ HH.text "Phase" ]
                          , HH.option [ HP.value "direction", HP.selected (state.dataMapping == MappingDirection) ] 
                              [ HH.text "Direction" ]
                          ]
                      ]
               else HH.text ""
           ]
    else HH.text ""

renderDataAssetOption :: forall m. DataAsset -> H.ComponentHTML Action Slots m
renderDataAssetOption asset =
  HH.option [ HP.value asset.name ] [ HH.text asset.name ]

-- =============================================================================
--                                                       // preview // section
-- =============================================================================

renderPreviewSection :: forall m. State -> H.ComponentHTML Action Slots m
renderPreviewSection state =
  let
    isGenerating = case state.generationState of
      Loading _ -> true
      _ -> false
  in
    HH.div
      [ cls [ "preview-section" ]
      , HP.attr (HH.AttrName "style") previewSectionStyle
      ]
      [ HH.canvas
          [ cls [ "preview-canvas" ]
          , HP.attr (HH.AttrName "style") previewCanvasStyle
          , HP.attr (HH.AttrName "width") "280"
          , HP.attr (HH.AttrName "height") "160"
          , HP.attr (HH.AttrName "aria-label") "Trajectory preview"
          ]
      , HH.button
          [ cls [ "preview-btn" ]
          , HP.attr (HH.AttrName "style") previewBtnStyle
          , HP.disabled isGenerating
          , HE.onClick \_ -> TriggerPreview
          , HP.attr (HH.AttrName "aria-label") "Generate preview"
          ]
          [ HH.text (if isGenerating then "Generating..." else "Preview") ]
      ]

-- =============================================================================
--                                                       // actions // section
-- =============================================================================

renderActionsSection :: forall m. State -> H.ComponentHTML Action Slots m
renderActionsSection state =
  let
    hasResult = case state.generationState of
      Success _ -> true
      _ -> false
  in
    HH.div
      [ cls [ "actions" ]
      , HP.attr (HH.AttrName "style") actionsStyle
      ]
      [ HH.button
          [ cls [ "action-btn", "secondary" ]
          , HP.attr (HH.AttrName "style") actionBtnSecondaryStyle
          , HP.disabled (not hasResult)
          , HE.onClick \_ -> TriggerExportJSON
          , HP.attr (HH.AttrName "aria-label") "Export as JSON"
          ]
          [ HH.text "Export JSON" ]
      , HH.button
          [ cls [ "action-btn", "primary" ]
          , HP.attr (HH.AttrName "style") actionBtnPrimaryStyle
          , HP.disabled (not hasResult)
          , HE.onClick \_ -> TriggerExportWanMove
          , HP.attr (HH.AttrName "aria-label") "Export for Wan-Move"
          ]
          [ HH.text "Export for Wan-Move" ]
      ]

-- =============================================================================
--                                                        // status // section
-- =============================================================================

renderStatusSection :: forall m. State -> H.ComponentHTML Action Slots m
renderStatusSection state =
  case state.statusMessage of
    Just msg ->
      HH.div
        [ cls [ "status" ]
        , HP.attr (HH.AttrName "style") (statusStyle msg.messageType)
        , HP.attr (HH.AttrName "role") (if msg.messageType == StatusError then "alert" else "status")
        ]
        [ HH.text msg.text ]
    Nothing -> HH.text ""

-- =============================================================================
--                                                       // helper // functions
-- =============================================================================

flowPresets :: Array String
flowPresets =
  [ "neural-flow"
  , "cosmic-dust"
  , "particle-stream"
  , "data-cascade"
  , "organic-growth"
  , "geometric-pulse"
  ]

formatPresetName :: String -> String
formatPresetName name =
  let
    words = split (Pattern "-") name
    capitalize w = case String.uncons w of
      Just { head, tail } -> String.singleton (String.toUpper (String.singleton head)) <> tail
      Nothing -> w
  in
    String.joinWith " " (map capitalize words)

parsePatternType :: String -> PatternType
parsePatternType = case _ of
  "spiral" -> Spiral
  "wave" -> Wave
  "explosion" -> Explosion
  "vortex" -> Vortex
  "data-river" -> DataRiver
  "morph" -> Morph
  "swarm" -> Swarm
  _ -> Spiral

parseDataMapping :: String -> DataMapping
parseDataMapping = case _ of
  "speed" -> MappingSpeed
  "amplitude" -> MappingAmplitude
  "phase" -> MappingPhase
  "direction" -> MappingDirection
  _ -> MappingSpeed

parseIntOr :: Int -> String -> Int
parseIntOr default s = case Int.fromString s of
  Just n -> n
  Nothing -> default

toNumber :: Int -> Number
toNumber = Int.toNumber

buildConfig :: State -> FlowConfig
buildConfig state =
  { preset: state.selectedPreset
  , patternType: state.patternType
  , numPoints: state.numPoints
  , numFrames: state.numFrames
  , width: state.width
  , height: state.height
  , seed: state.seed
  , useDataDriven: state.useDataDriven
  , dataAssetName: if state.useDataDriven && state.selectedDataAsset /= ""
                     then Just state.selectedDataAsset
                     else Nothing
  , dataMapping: state.dataMapping
  }

-- =============================================================================
--                                                                    // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "padding: 12px; display: flex; flex-direction: column; gap: 12px; " <>
  "font-size: 12px; color: var(--lattice-text-primary);"

headerStyle :: String
headerStyle =
  "display: flex; flex-direction: column; gap: 2px;"

headerTitleStyle :: String
headerTitleStyle =
  "margin: 0; font-size: 14px; font-weight: 600;"

subtitleStyle :: String
subtitleStyle =
  "font-size: 11px; color: var(--lattice-text-muted);"

sectionStyle :: String
sectionStyle =
  "display: flex; flex-direction: column; gap: 4px;"

sectionLabelStyle :: String
sectionLabelStyle =
  "font-size: 11px; color: var(--lattice-text-muted); display: flex; align-items: center; gap: 6px;"

selectStyle :: String
selectStyle =
  "background: var(--lattice-surface-2); border: 1px solid var(--lattice-border-subtle); " <>
  "border-radius: 4px; padding: 6px 8px; color: var(--lattice-text-primary); font-size: 12px;"

inputRowStyle :: String
inputRowStyle =
  "display: flex; align-items: center; gap: 8px;"

numInputStyle :: String
numInputStyle =
  "background: var(--lattice-surface-2); border: 1px solid var(--lattice-border-subtle); " <>
  "border-radius: 4px; padding: 6px 8px; color: var(--lattice-text-primary); " <>
  "font-size: 12px; width: 80px;"

inputHintStyle :: String
inputHintStyle =
  "font-size: 11px; color: var(--lattice-text-muted);"

resolutionRowStyle :: String
resolutionRowStyle =
  "display: flex; align-items: center; gap: 6px;"

resInputStyle :: String
resInputStyle =
  "background: var(--lattice-surface-2); border: 1px solid var(--lattice-border-subtle); " <>
  "border-radius: 4px; padding: 6px 8px; color: var(--lattice-text-primary); " <>
  "font-size: 12px; width: 60px;"

resXStyle :: String
resXStyle =
  "color: var(--lattice-text-muted);"

presetBtnStyle :: String
presetBtnStyle =
  "background: var(--lattice-surface-3); border: 1px solid var(--lattice-border-subtle); " <>
  "border-radius: 4px; padding: 4px 8px; color: var(--lattice-text-muted); " <>
  "font-size: 11px; cursor: pointer;"

randomizeBtnStyle :: String
randomizeBtnStyle =
  "background: var(--lattice-surface-3); border: 1px solid var(--lattice-border-subtle); " <>
  "border-radius: 4px; padding: 4px 8px; cursor: pointer; font-size: 14px;"

dataOptionsStyle :: String
dataOptionsStyle =
  "display: flex; flex-direction: column; gap: 6px; padding-left: 20px; margin-top: 4px;"

previewSectionStyle :: String
previewSectionStyle =
  "display: flex; flex-direction: column; gap: 8px;"

previewCanvasStyle :: String
previewCanvasStyle =
  "background: #0a0a0a; border: 1px solid var(--lattice-border-subtle); " <>
  "border-radius: 4px; width: 100%; aspect-ratio: 832 / 480;"

previewBtnStyle :: String
previewBtnStyle =
  "background: var(--lattice-surface-3); border: 1px solid var(--lattice-border-subtle); " <>
  "border-radius: 4px; padding: 8px; color: var(--lattice-text-primary); " <>
  "font-size: 12px; cursor: pointer;"

actionsStyle :: String
actionsStyle =
  "display: flex; gap: 8px;"

actionBtnSecondaryStyle :: String
actionBtnSecondaryStyle =
  "flex: 1; padding: 8px 12px; border-radius: 4px; font-size: 12px; cursor: pointer; " <>
  "background: var(--lattice-surface-3); color: var(--lattice-text-primary); " <>
  "border: 1px solid var(--lattice-border-subtle);"

actionBtnPrimaryStyle :: String
actionBtnPrimaryStyle =
  "flex: 1; padding: 8px 12px; border-radius: 4px; font-size: 12px; cursor: pointer; " <>
  "background: var(--lattice-accent); color: white; border: none;"

statusStyle :: StatusType -> String
statusStyle statusType =
  let
    baseStyle = "padding: 8px; border-radius: 4px; font-size: 11px; "
    colorStyle = case statusType of
      StatusSuccess -> "background: rgba(16, 185, 129, 0.2); color: #10b981;"
      StatusError -> "background: rgba(239, 68, 68, 0.2); color: #ef4444;"
      StatusInfo -> "background: rgba(139, 92, 246, 0.2); color: #8b5cf6;"
  in
    baseStyle <> colorStyle

-- =============================================================================
--                                                                   // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input -> do
    H.modify_ _ { dataAssets = input.dataAssets }

  SetPreset preset -> do
    H.modify_ _ { selectedPreset = preset }
    -- Update pattern type based on preset
    when (preset /= "custom") do
      H.modify_ _ { patternType = presetToPattern preset }

  SetPatternType pattern -> do
    H.modify_ _ { patternType = pattern }

  SetNumPoints n -> do
    H.modify_ _ { numPoints = clamp 10 1000 n }

  SetNumFrames n -> do
    H.modify_ _ { numFrames = clamp 17 241 n }

  SetWidth w -> do
    H.modify_ _ { width = clamp 256 1920 w }

  SetHeight h -> do
    H.modify_ _ { height = clamp 256 1080 h }

  SetResolution w h -> do
    H.modify_ _ { width = w, height = h }

  SetSeed s -> do
    H.modify_ _ { seed = max 0 s }

  RandomizeSeed -> do
    -- In a real implementation, this would use Effect.Random
    -- For now, just increment by a pseudo-random amount
    state <- H.get
    let newSeed = (state.seed * 1103515245 + 12345) `mod` 1000000
    H.modify_ _ { seed = newSeed }

  ToggleDataDriven -> do
    H.modify_ \s -> s { useDataDriven = not s.useDataDriven }

  SetSelectedDataAsset name -> do
    H.modify_ _ { selectedDataAsset = name }

  SetDataMapping mapping -> do
    H.modify_ _ { dataMapping = mapping }

  TriggerPreview -> do
    state <- H.get
    H.modify_ _ { generationState = Loading 0.0 }
    H.raise $ GeneratePreview (buildConfig state)

  TriggerExportJSON -> do
    state <- H.get
    H.raise $ ExportJSON (buildConfig state)

  TriggerExportWanMove -> do
    state <- H.get
    H.raise $ ExportWanMove (buildConfig state)

presetToPattern :: String -> PatternType
presetToPattern = case _ of
  "neural-flow" -> DataRiver
  "cosmic-dust" -> Swarm
  "particle-stream" -> Wave
  "data-cascade" -> Vortex
  "organic-growth" -> Morph
  "geometric-pulse" -> Spiral
  _ -> Spiral

clamp :: Int -> Int -> Int -> Int
clamp minVal maxVal val = max minVal (min maxVal val)
