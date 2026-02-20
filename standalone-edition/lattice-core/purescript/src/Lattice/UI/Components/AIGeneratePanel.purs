-- | AI Generate Panel Component
-- |
-- | AI-powered generation tools for depth maps, normal maps, and segmentation.
-- | Integrates with ComfyUI backend models for processing.
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/AIGeneratePanel.vue
module Lattice.UI.Components.AIGeneratePanel
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  ) where

import Prelude

import Data.Array (filter)
import Data.Maybe (Maybe(..), isJust)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls, textMuted)
import Lattice.UI.Utils as Utils

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { selectedLayerName :: Maybe String
  }

data Output
  = GenerateDepth DepthOptions
  | GenerateNormal NormalOptions
  | GenerateSegment SegmentOptions
  | RefreshModels

data Query a

type Slot id = H.Slot Query Output id

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // model // types
-- ════════════════════════════════════════════════════════════════════════════

data SourceType
  = SourceLayer
  | SourceCanvas
  | SourceFile

derive instance eqSourceType :: Eq SourceType

data GenerationType
  = GenDepth
  | GenNormal
  | GenSegment

derive instance eqGenerationType :: Eq GenerationType

data AIModelType
  = DepthAnything
  | DepthAnythingV2
  | NormalCrafter
  | SegmentAnything
  | SegmentAnything2

derive instance eqAIModelType :: Eq AIModelType

instance showAIModelType :: Show AIModelType where
  show = case _ of
    DepthAnything -> "depth-anything"
    DepthAnythingV2 -> "depth-anything-v2"
    NormalCrafter -> "normal-crafter"
    SegmentAnything -> "segment-anything"
    SegmentAnything2 -> "segment-anything-2"

modelName :: AIModelType -> String
modelName = case _ of
  DepthAnything -> "Depth Anything"
  DepthAnythingV2 -> "Depth Anything V2"
  NormalCrafter -> "Normal Crafter"
  SegmentAnything -> "Segment Anything"
  SegmentAnything2 -> "SAM 2"

type ModelInfo =
  { modelType :: AIModelType
  , memoryRequired :: Int  -- MB
  , status :: ModelStatus
  }

data ModelStatus
  = StatusReady
  | StatusNotLoaded
  | StatusLoading
  | StatusError

derive instance eqModelStatus :: Eq ModelStatus

instance showModelStatus :: Show ModelStatus where
  show = case _ of
    StatusReady -> "ready"
    StatusNotLoaded -> "not-loaded"
    StatusLoading -> "loading"
    StatusError -> "error"

data OutputTarget
  = OutputLayer
  | OutputMask
  | OutputDownload

derive instance eqOutputTarget :: Eq OutputTarget

data ColorMap
  = CMGrayscale
  | CMViridis
  | CMPlasma
  | CMMagma

derive instance eqColorMap :: Eq ColorMap

instance showColorMap :: Show ColorMap where
  show = case _ of
    CMGrayscale -> "grayscale"
    CMViridis -> "viridis"
    CMPlasma -> "plasma"
    CMMagma -> "magma"

type DepthOptions =
  { model :: AIModelType
  , colorMap :: ColorMap
  , normalize :: Boolean
  }

type NormalOptions =
  { model :: AIModelType
  , strength :: Number
  , smoothing :: Number
  }

type SegmentOptions =
  { model :: AIModelType
  , autoMask :: Boolean
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // state
-- ════════════════════════════════════════════════════════════════════════════

type State =
  { selectedLayerName :: Maybe String
  , sourceType :: SourceType
  , generationType :: GenerationType
  , selectedModel :: AIModelType
  , models :: Array ModelInfo
  , depthOptions :: DepthOptions
  , normalOptions :: NormalOptions
  , segmentOptions :: SegmentOptions
  , outputTarget :: OutputTarget
  , isGenerating :: Boolean
  , statusMessage :: Maybe StatusMessage
  , previewUrl :: Maybe String
  , uploadedFileName :: Maybe String
  }

type StatusMessage =
  { text :: String
  , msgType :: StatusType
  }

data StatusType
  = StatusInfo
  | StatusSuccess
  | StatusErr

derive instance eqStatusType :: Eq StatusType

data Action
  = Initialize
  | Receive Input
  | SetSourceType SourceType
  | SetGenerationType GenerationType
  | SetModel AIModelType
  | SetColorMap ColorMap
  | SetNormalize Boolean
  | SetNormalStrength Number
  | SetNormalSmoothing Number
  | SetAutoMask Boolean
  | SetOutputTarget OutputTarget
  | RefreshModelStatus
  | StartGeneration
  | ClearStatus

type Slots = ()

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

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
  { selectedLayerName: input.selectedLayerName
  , sourceType: SourceLayer
  , generationType: GenDepth
  , selectedModel: DepthAnything
  , models: defaultModels
  , depthOptions:
      { model: DepthAnything
      , colorMap: CMGrayscale
      , normalize: true
      }
  , normalOptions:
      { model: NormalCrafter
      , strength: 100.0
      , smoothing: 0.0
      }
  , segmentOptions:
      { model: SegmentAnything
      , autoMask: true
      }
  , outputTarget: OutputLayer
  , isGenerating: false
  , statusMessage: Nothing
  , previewUrl: Nothing
  , uploadedFileName: Nothing
  }

defaultModels :: Array ModelInfo
defaultModels =
  [ { modelType: DepthAnything, memoryRequired: 1200, status: StatusNotLoaded }
  , { modelType: DepthAnythingV2, memoryRequired: 1400, status: StatusNotLoaded }
  , { modelType: NormalCrafter, memoryRequired: 800, status: StatusNotLoaded }
  , { modelType: SegmentAnything, memoryRequired: 2500, status: StatusNotLoaded }
  , { modelType: SegmentAnything2, memoryRequired: 3200, status: StatusNotLoaded }
  ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-ai-generate-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , HP.attr (HH.AttrName "aria-label") "AI Generation Tools"
    ]
    [ renderHeader
    , renderContent state
    ]

renderHeader :: forall m. H.ComponentHTML Action Slots m
renderHeader =
  HH.div
    [ cls [ "lattice-panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.span [ cls [ "lattice-panel-title" ] ] 
        [ HH.text "AI Generate" ]
    , HH.button
        [ cls [ "refresh-btn" ]
        , HP.attr (HH.AttrName "style") refreshBtnStyle
        , HP.attr (HH.AttrName "title") "Refresh model status"
        , HE.onClick \_ -> RefreshModelStatus
        ]
        [ HH.text "↻" ]
    ]

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "lattice-panel-content" ]
    , HP.attr (HH.AttrName "style") contentStyle
    ]
    [ renderSourceSection state
    , renderGenerationTypeSection state
    , renderModelSection state
    , renderOptionsSection state
    , renderOutputSection state
    , renderGenerateButton state
    , renderStatusMessage state
    , renderPreview state
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // source // section
-- ════════════════════════════════════════════════════════════════════════════

renderSourceSection :: forall m. State -> H.ComponentHTML Action Slots m
renderSourceSection state =
  HH.div
    [ cls [ "section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div 
        [ cls [ "section-header" ]
        , HP.attr (HH.AttrName "style") sectionHeaderStyle
        , HP.id "source-label"
        ] 
        [ HH.text "Source" ]
    , HH.div 
        [ cls [ "source-options" ]
        , HP.attr (HH.AttrName "style") buttonGroupStyle
        , HP.attr (HH.AttrName "role") "group"
        , ARIA.labelledBy "source-label"
        ]
        [ sourceButton "Selected Layer" SourceLayer state.sourceType
        , sourceButton "Canvas Frame" SourceCanvas state.sourceType
        , sourceButton "Upload File" SourceFile state.sourceType
        ]
    , renderSourceInfo state
    ]

sourceButton :: forall m. String -> SourceType -> SourceType -> H.ComponentHTML Action Slots m
sourceButton labelText sourceType activeSource =
  let isSelected = sourceType == activeSource
  in
  HH.button
    [ cls [ "source-btn" ]
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "style") (optionButtonStyle isSelected)
    , ARIA.pressed (show isSelected)
    , HP.attr (HH.AttrName "data-state") (if isSelected then "active" else "inactive")
    , HE.onClick \_ -> SetSourceType sourceType
    ]
    [ HH.text labelText ]

renderSourceInfo :: forall m. State -> H.ComponentHTML Action Slots m
renderSourceInfo state =
  case state.sourceType of
    SourceLayer ->
      HH.div [ cls [ "layer-info" ], HP.attr (HH.AttrName "style") infoBoxStyle ]
        [ case state.selectedLayerName of
            Just name -> HH.text name
            Nothing -> HH.span [ cls [ "no-selection" ] ] [ textMuted "No layer selected" ]
        ]
    SourceFile ->
      HH.div [ cls [ "file-upload" ], HP.attr (HH.AttrName "style") infoBoxStyle ]
        [ HH.button [ cls [ "upload-btn" ], HP.attr (HH.AttrName "style") uploadBtnStyle ]
            [ HH.text "Select Image..." ]
        , case state.uploadedFileName of
            Just name -> HH.span [ cls [ "file-name" ] ] [ HH.text name ]
            Nothing -> HH.text ""
        ]
    SourceCanvas ->
      HH.div [ cls [ "canvas-info" ], HP.attr (HH.AttrName "style") infoBoxStyle ]
        [ textMuted "Will capture current canvas frame" ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                 // generation // type // section
-- ════════════════════════════════════════════════════════════════════════════

renderGenerationTypeSection :: forall m. State -> H.ComponentHTML Action Slots m
renderGenerationTypeSection state =
  HH.div
    [ cls [ "section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div 
        [ cls [ "section-header" ]
        , HP.attr (HH.AttrName "style") sectionHeaderStyle
        , HP.id "gen-type-label"
        ] 
        [ HH.text "Generation Type" ]
    , HH.div 
        [ cls [ "generation-types" ]
        , HP.attr (HH.AttrName "style") buttonGroupStyle
        , HP.attr (HH.AttrName "role") "group"
        , ARIA.labelledBy "gen-type-label"
        ]
        [ genTypeButton "⬛" "Depth" "Estimate depth from image" GenDepth state.generationType
        , genTypeButton "🔮" "Normal" "Generate normal map" GenNormal state.generationType
        , genTypeButton "✂" "Segment" "Segment objects" GenSegment state.generationType
        ]
    ]

genTypeButton :: forall m. String -> String -> String -> GenerationType -> GenerationType -> H.ComponentHTML Action Slots m
genTypeButton iconText labelText description genType activeType =
  let isSelected = genType == activeType
  in
  HH.button
    [ cls [ "gen-type-btn" ]
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "style") (genTypeButtonStyle isSelected)
    , HP.attr (HH.AttrName "title") description
    , ARIA.pressed (show isSelected)
    , HP.attr (HH.AttrName "data-state") (if isSelected then "active" else "inactive")
    , HE.onClick \_ -> SetGenerationType genType
    ]
    [ HH.span [ cls [ "type-icon" ], HP.attr (HH.AttrName "style") typeIconStyle, HP.attr (HH.AttrName "aria-hidden") "true" ] 
        [ HH.text iconText ]
    , HH.span [ cls [ "type-label" ], HP.attr (HH.AttrName "style") typeLabelStyle ] 
        [ HH.text labelText ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // model // section
-- ════════════════════════════════════════════════════════════════════════════

renderModelSection :: forall m. State -> H.ComponentHTML Action Slots m
renderModelSection state =
  HH.div
    [ cls [ "section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ] 
        [ HH.text "Model" ]
    , HH.select
        [ cls [ "model-select" ]
        , HP.attr (HH.AttrName "style") selectStyle
        ]
        (map renderModelOption (availableModels state))
    , renderModelInfo state
    ]

availableModels :: State -> Array ModelInfo
availableModels state =
  filter (\m -> isModelForType m.modelType state.generationType) state.models

isModelForType :: AIModelType -> GenerationType -> Boolean
isModelForType model genType =
  case genType of
    GenDepth -> model == DepthAnything || model == DepthAnythingV2
    GenNormal -> model == NormalCrafter
    GenSegment -> model == SegmentAnything || model == SegmentAnything2

renderModelOption :: forall m. ModelInfo -> H.ComponentHTML Action Slots m
renderModelOption info =
  HH.option
    [ HP.value (show info.modelType) ]
    [ HH.text (modelName info.modelType) ]

renderModelInfo :: forall m. State -> H.ComponentHTML Action Slots m
renderModelInfo state =
  let
    mInfo = findModel state.selectedModel state.models
  in
    case mInfo of
      Just info ->
        HH.div [ cls [ "model-info" ], HP.attr (HH.AttrName "style") modelInfoStyle ]
          [ HH.span [ cls [ "memory-badge" ], HP.attr (HH.AttrName "style") memoryBadgeStyle ] 
              [ HH.text (show info.memoryRequired <> "MB") ]
          , HH.span 
              [ cls [ "status-badge" ]
              , HP.attr (HH.AttrName "style") (statusBadgeStyle info.status)
              ] 
              [ HH.text (show info.status) ]
          ]
      Nothing -> HH.text ""

findModel :: AIModelType -> Array ModelInfo -> Maybe ModelInfo
findModel target models =
  case filter (\m -> m.modelType == target) models of
    [ m ] -> Just m
    _ -> Nothing

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // options // section
-- ════════════════════════════════════════════════════════════════════════════

renderOptionsSection :: forall m. State -> H.ComponentHTML Action Slots m
renderOptionsSection state =
  HH.div
    [ cls [ "section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ] 
        [ HH.text "Options" ]
    , case state.generationType of
        GenDepth -> renderDepthOptions state
        GenNormal -> renderNormalOptions state
        GenSegment -> renderSegmentOptions state
    ]

renderDepthOptions :: forall m. State -> H.ComponentHTML Action Slots m
renderDepthOptions state =
  HH.div [ cls [ "options-group" ], HP.attr (HH.AttrName "style") optionsGroupStyle ]
    [ HH.label [ cls [ "option-row" ], HP.attr (HH.AttrName "style") optionRowStyle ]
        [ HH.span_ [ HH.text "Color Map" ]
        , HH.select
            [ cls [ "option-select" ]
            , HP.attr (HH.AttrName "style") optionSelectStyle
            ]
            [ HH.option [ HP.value "grayscale" ] [ HH.text "Grayscale" ]
            , HH.option [ HP.value "viridis" ] [ HH.text "Viridis" ]
            , HH.option [ HP.value "plasma" ] [ HH.text "Plasma" ]
            , HH.option [ HP.value "magma" ] [ HH.text "Magma" ]
            ]
        ]
    , HH.label [ cls [ "option-row" ], HP.attr (HH.AttrName "style") optionRowStyle ]
        [ HH.input
            [ HP.type_ HP.InputCheckbox
            , HP.checked state.depthOptions.normalize
            , HE.onChecked SetNormalize
            ]
        , HH.span_ [ HH.text "Normalize output" ]
        ]
    ]

renderNormalOptions :: forall m. State -> H.ComponentHTML Action Slots m
renderNormalOptions state =
  HH.div [ cls [ "options-group" ], HP.attr (HH.AttrName "style") optionsGroupStyle ]
    [ HH.label [ cls [ "option-row" ], HP.attr (HH.AttrName "style") optionRowStyle ]
        [ HH.span_ [ HH.text "Strength" ]
        , HH.input
            [ HP.type_ HP.InputRange
            , HP.attr (HH.AttrName "min") "0"
            , HP.attr (HH.AttrName "max") "100"
            , HP.value (show (round state.normalOptions.strength))
            ]
        , HH.span [ cls [ "value" ], HP.attr (HH.AttrName "style") valueStyle ] 
            [ HH.text (show (round state.normalOptions.strength) <> "%") ]
        ]
    , HH.label [ cls [ "option-row" ], HP.attr (HH.AttrName "style") optionRowStyle ]
        [ HH.span_ [ HH.text "Smoothing" ]
        , HH.input
            [ HP.type_ HP.InputRange
            , HP.attr (HH.AttrName "min") "0"
            , HP.attr (HH.AttrName "max") "100"
            , HP.value (show (round state.normalOptions.smoothing))
            ]
        , HH.span [ cls [ "value" ], HP.attr (HH.AttrName "style") valueStyle ] 
            [ HH.text (show (round state.normalOptions.smoothing) <> "%") ]
        ]
    ]

renderSegmentOptions :: forall m. State -> H.ComponentHTML Action Slots m
renderSegmentOptions state =
  HH.div [ cls [ "options-group" ], HP.attr (HH.AttrName "style") optionsGroupStyle ]
    [ HH.div [ cls [ "option-row" ], HP.attr (HH.AttrName "style") optionRowStyle ]
        [ HH.span_ [ textMuted "Click on canvas to set point" ] ]
    , HH.label [ cls [ "option-row" ], HP.attr (HH.AttrName "style") optionRowStyle ]
        [ HH.input
            [ HP.type_ HP.InputCheckbox
            , HP.checked state.segmentOptions.autoMask
            , HE.onChecked SetAutoMask
            ]
        , HH.span_ [ HH.text "Auto-mask to layer" ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // output // section
-- ════════════════════════════════════════════════════════════════════════════

renderOutputSection :: forall m. State -> H.ComponentHTML Action Slots m
renderOutputSection state =
  HH.div
    [ cls [ "section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ] 
        [ HH.text "Output" ]
    , HH.div [ cls [ "output-options" ], HP.attr (HH.AttrName "style") outputOptionsStyle ]
        [ outputOption "Create new layer" OutputLayer state.outputTarget
        , outputOption "Apply as layer mask" OutputMask state.outputTarget
        , outputOption "Download file" OutputDownload state.outputTarget
        ]
    ]

outputOption :: forall m. String -> OutputTarget -> OutputTarget -> H.ComponentHTML Action Slots m
outputOption labelText target activeTarget =
  HH.label [ cls [ "option-row" ], HP.attr (HH.AttrName "style") optionRowStyle ]
    [ HH.input
        [ HP.type_ HP.InputRadio
        , HP.name "output-target"
        , HP.checked (target == activeTarget)
        , HE.onClick \_ -> SetOutputTarget target
        ]
    , HH.span_ [ HH.text labelText ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // generate // button
-- ════════════════════════════════════════════════════════════════════════════

renderGenerateButton :: forall m. State -> H.ComponentHTML Action Slots m
renderGenerateButton state =
  let
    canGenerate = case state.sourceType of
      SourceLayer -> isJust state.selectedLayerName
      SourceFile -> isJust state.uploadedFileName
      SourceCanvas -> true
    
    buttonText = if state.isGenerating
      then "Generating..."
      else case state.generationType of
        GenDepth -> "Generate Depth Map"
        GenNormal -> "Generate Normal Map"
        GenSegment -> "Segment Image"
  in
    HH.div
      [ cls [ "section" ]
      , HP.attr (HH.AttrName "style") sectionStyle
      ]
      [ HH.button
          [ cls [ "generate-btn" ]
          , HP.attr (HH.AttrName "style") generateBtnStyle
          , HP.disabled (not canGenerate || state.isGenerating)
          , HE.onClick \_ -> StartGeneration
          ]
          [ if state.isGenerating
              then HH.span [ cls [ "spinner" ], HP.attr (HH.AttrName "style") spinnerStyle ] []
              else HH.text buttonText
          ]
      ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // status // and // preview
-- ════════════════════════════════════════════════════════════════════════════

renderStatusMessage :: forall m. State -> H.ComponentHTML Action Slots m
renderStatusMessage state =
  case state.statusMessage of
    Just msg ->
      HH.div
        [ cls [ "status-message" ]
        , HP.attr (HH.AttrName "style") (statusMsgStyle msg.msgType)
        ]
        [ HH.text msg.text ]
    Nothing -> HH.text ""

renderPreview :: forall m. State -> H.ComponentHTML Action Slots m
renderPreview state =
  case state.previewUrl of
    Just url ->
      HH.div [ cls [ "preview-section" ], HP.attr (HH.AttrName "style") previewSectionStyle ]
        [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ] 
            [ HH.text "Preview" ]
        , HH.img
            [ HP.src url
            , cls [ "preview-image" ]
            , HP.attr (HH.AttrName "style") previewImageStyle
            , HP.attr (HH.AttrName "alt") "Generation preview"
            ]
        ]
    Nothing -> HH.text ""

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // styles
-- ════════════════════════════════════════════════════════════════════════════

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary); " <>
  "font-size: 13px;"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 10px 12px; background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

refreshBtnStyle :: String
refreshBtnStyle =
  "width: 24px; height: 24px; padding: 0; border: none; " <>
  "background: transparent; color: var(--lattice-text-secondary); " <>
  "cursor: pointer; border-radius: 4px; font-size: 16px;"

contentStyle :: String
contentStyle =
  "flex: 1; overflow-y: auto; padding: 12px;"

sectionStyle :: String
sectionStyle =
  "margin-bottom: 16px;"

sectionHeaderStyle :: String
sectionHeaderStyle =
  "font-size: 11px; font-weight: 600; color: var(--lattice-text-secondary); " <>
  "text-transform: uppercase; margin-bottom: 8px;"

buttonGroupStyle :: String
buttonGroupStyle =
  "display: flex; gap: 6px;"

optionButtonStyle :: Boolean -> String
optionButtonStyle active =
  "flex: 1; padding: 6px 8px; " <>
  "border: 1px solid " <> (if active then "var(--lattice-accent)" else "var(--lattice-border-default)") <> "; " <>
  "background: " <> (if active then "var(--lattice-accent-muted)" else "var(--lattice-surface-2)") <> "; " <>
  "color: " <> (if active then "var(--lattice-accent)" else "var(--lattice-text-secondary)") <> "; " <>
  "border-radius: 4px; cursor: pointer; font-size: 12px;"

genTypeButtonStyle :: Boolean -> String
genTypeButtonStyle active =
  "flex: 1; padding: 8px; display: flex; flex-direction: column; align-items: center; gap: 4px; " <>
  "border: 1px solid " <> (if active then "var(--lattice-accent)" else "var(--lattice-border-default)") <> "; " <>
  "background: " <> (if active then "var(--lattice-accent-muted)" else "var(--lattice-surface-2)") <> "; " <>
  "color: " <> (if active then "var(--lattice-accent)" else "var(--lattice-text-secondary)") <> "; " <>
  "border-radius: 4px; cursor: pointer;"

typeIconStyle :: String
typeIconStyle =
  "font-size: 18px;"

typeLabelStyle :: String
typeLabelStyle =
  "font-size: 11px;"

infoBoxStyle :: String
infoBoxStyle =
  "margin-top: 8px; padding: 8px; background: var(--lattice-surface-0); border-radius: 4px;"

uploadBtnStyle :: String
uploadBtnStyle =
  "padding: 6px 12px; border: 1px dashed var(--lattice-border-default); " <>
  "background: transparent; color: var(--lattice-text-secondary); " <>
  "border-radius: 4px; cursor: pointer;"

selectStyle :: String
selectStyle =
  "width: 100%; padding: 8px; " <>
  "border: 1px solid var(--lattice-border-default); " <>
  "background: var(--lattice-surface-2); " <>
  "color: var(--lattice-text-primary); " <>
  "border-radius: 4px; font-size: 13px;"

modelInfoStyle :: String
modelInfoStyle =
  "display: flex; gap: 8px; margin-top: 6px;"

memoryBadgeStyle :: String
memoryBadgeStyle =
  "padding: 2px 8px; border-radius: 10px; font-size: 11px; " <>
  "background: var(--lattice-surface-3); color: var(--lattice-text-secondary);"

statusBadgeStyle :: ModelStatus -> String
statusBadgeStyle status =
  let
    (bg, fg) = case status of
      StatusReady -> ("rgba(16, 185, 129, 0.2)", "#10b981")
      StatusNotLoaded -> ("var(--lattice-surface-3)", "var(--lattice-text-muted)")
      StatusLoading -> ("rgba(245, 158, 11, 0.2)", "#f59e0b")
      StatusError -> ("rgba(239, 68, 68, 0.2)", "#ef4444")
  in
    "padding: 2px 8px; border-radius: 10px; font-size: 11px; " <>
    "background: " <> bg <> "; color: " <> fg <> ";"

optionsGroupStyle :: String
optionsGroupStyle =
  "display: flex; flex-direction: column; gap: 8px;"

optionRowStyle :: String
optionRowStyle =
  "display: flex; align-items: center; gap: 8px;"

optionSelectStyle :: String
optionSelectStyle =
  "flex: 1; padding: 4px 8px; " <>
  "border: 1px solid var(--lattice-border-default); " <>
  "background: var(--lattice-surface-2); " <>
  "color: var(--lattice-text-primary); border-radius: 4px;"

valueStyle :: String
valueStyle =
  "min-width: 40px; text-align: right; color: var(--lattice-text-secondary); font-size: 12px;"

outputOptionsStyle :: String
outputOptionsStyle =
  "display: flex; flex-direction: column; gap: 6px;"

generateBtnStyle :: String
generateBtnStyle =
  "width: 100%; padding: 12px; border: none; " <>
  "background: linear-gradient(135deg, var(--lattice-accent), var(--lattice-accent-secondary)); " <>
  "color: white; font-size: 14px; font-weight: 600; " <>
  "border-radius: 6px; cursor: pointer;"

spinnerStyle :: String
spinnerStyle =
  "display: inline-block; width: 16px; height: 16px; " <>
  "border: 2px solid rgba(255,255,255,0.3); " <>
  "border-top-color: white; border-radius: 50%; " <>
  "animation: spin 0.8s linear infinite;"

statusMsgStyle :: StatusType -> String
statusMsgStyle msgType =
  let
    (bg, fg, border) = case msgType of
      StatusInfo -> ("rgba(59, 130, 246, 0.1)", "#3b82f6", "rgba(59, 130, 246, 0.3)")
      StatusSuccess -> ("rgba(16, 185, 129, 0.1)", "#10b981", "rgba(16, 185, 129, 0.3)")
      StatusErr -> ("rgba(239, 68, 68, 0.1)", "#ef4444", "rgba(239, 68, 68, 0.3)")
  in
    "margin-top: 12px; padding: 10px; border-radius: 4px; font-size: 12px; " <>
    "background: " <> bg <> "; color: " <> fg <> "; border: 1px solid " <> border <> ";"

previewSectionStyle :: String
previewSectionStyle =
  "margin-top: 16px;"

previewImageStyle :: String
previewImageStyle =
  "width: 100%; border-radius: 4px; background: var(--lattice-surface-0);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> do
    H.raise RefreshModels
  
  Receive input -> do
    H.modify_ _ { selectedLayerName = input.selectedLayerName }
  
  SetSourceType st -> do
    H.modify_ _ { sourceType = st }
  
  SetGenerationType gt -> do
    let defaultModel = case gt of
          GenDepth -> DepthAnything
          GenNormal -> NormalCrafter
          GenSegment -> SegmentAnything
    H.modify_ _ { generationType = gt, selectedModel = defaultModel }
  
  SetModel model -> do
    H.modify_ _ { selectedModel = model }
  
  SetColorMap cm -> do
    H.modify_ \s -> s { depthOptions = s.depthOptions { colorMap = cm } }
  
  SetNormalize normalize -> do
    H.modify_ \s -> s { depthOptions = s.depthOptions { normalize = normalize } }
  
  SetNormalStrength strength -> do
    H.modify_ \s -> s { normalOptions = s.normalOptions { strength = strength } }
  
  SetNormalSmoothing smoothing -> do
    H.modify_ \s -> s { normalOptions = s.normalOptions { smoothing = smoothing } }
  
  SetAutoMask autoMask -> do
    H.modify_ \s -> s { segmentOptions = s.segmentOptions { autoMask = autoMask } }
  
  SetOutputTarget target -> do
    H.modify_ _ { outputTarget = target }
  
  RefreshModelStatus -> do
    H.raise RefreshModels
  
  StartGeneration -> do
    state <- H.get
    H.modify_ _ { isGenerating = true, statusMessage = Just { text: "Starting generation...", msgType: StatusInfo } }
    case state.generationType of
      GenDepth -> H.raise (GenerateDepth state.depthOptions)
      GenNormal -> H.raise (GenerateNormal state.normalOptions)
      GenSegment -> H.raise (GenerateSegment state.segmentOptions)
  
  ClearStatus -> do
    H.modify_ _ { statusMessage = Nothing }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Round a number to the nearest integer
-- | Uses Data.Int.round from standard library
round :: Number -> Int
round = Utils.round

-- | Floor a number to an integer (toward negative infinity)
-- | Uses Data.Int.floor from standard library
floorNum :: Number -> Int
floorNum = Utils.floor

-- | Convert Int to Number
-- | Uses Data.Int.toNumber from standard library
toNumber :: Int -> Number
toNumber = Utils.toNumber
