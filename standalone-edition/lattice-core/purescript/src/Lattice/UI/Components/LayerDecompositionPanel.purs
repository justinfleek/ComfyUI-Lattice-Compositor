-- | Layer Decomposition Panel Component
-- |
-- | AI-powered image layer decomposition using Qwen-Image-Layered model.
-- | Decomposes a single image into multiple RGBA layers with automatic
-- | depth-based z-space placement.
-- |
-- | Features:
-- | - Model download with progress tracking and hash verification
-- | - Configurable layer count (3-10)
-- | - LLM-based depth estimation (GPT-4o / Claude)
-- | - Automatic z-space positioning
-- | - Progress visualization
-- | - Layer preview grid
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/LayerDecompositionPanel.vue
module Lattice.UI.Components.LayerDecompositionPanel
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , ModelStatus(..)
  , DecompositionOptions
  , DecompositionResult
  , DepthProvider(..)
  ) where

import Prelude

import Data.Array (length)
import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(..), isJust, isNothing)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls, loadingState, errorState, RemoteData(..))
import Lattice.UI.Utils (formatFixed)

-- =============================================================================
--                                                                      // types
-- =============================================================================

type Input =
  { modelStatus :: ModelStatus
  }

data Output
  = StartDownload
  | StartDecomposition DecompositionOptions
  | SelectLayer String
  | ClearImage

data Query a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                         // domain // types
-- =============================================================================

type ModelStatus =
  { downloaded :: Boolean
  , loaded :: Boolean
  , loading :: Boolean
  , verification :: Maybe VerificationInfo
  }

type VerificationInfo =
  { verified :: Boolean
  , message :: String
  }

data DepthProvider
  = ProviderOpenAI
  | ProviderAnthropic

derive instance eqDepthProvider :: Eq DepthProvider

type DecompositionOptions =
  { imageDataUrl :: String
  , numLayers :: Int
  , autoDepthEstimation :: Boolean
  , depthProvider :: DepthProvider
  , zSpaceScale :: Int
  , autoUnload :: Boolean
  }

type DecompositionResult =
  { success :: Boolean
  , layers :: Array LayerResult
  , depthEstimation :: Maybe DepthEstimationInfo
  , error :: Maybe String
  }

type LayerResult =
  { id :: String
  , name :: String
  , zPosition :: Number
  }

type DepthEstimationInfo =
  { sceneDescription :: String
  , depthRange :: { near :: Number, far :: Number }
  }

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { modelStatus :: ModelStatus
  , imageDataUrl :: Maybe String
  , numLayers :: Int
  , autoDepth :: Boolean
  , depthProvider :: DepthProvider
  , zScale :: Int
  , autoUnload :: Boolean
  , downloadState :: RemoteData String Number  -- Progress 0-100
  , decomposeState :: RemoteData String DecompositionResult
  , progressMessage :: String
  , baseId :: String
  }

data Action
  = Initialize
  | Receive Input
  | TriggerDownload
  | SetNumLayers Int
  | ToggleAutoDepth
  | SetDepthProvider DepthProvider
  | SetZScale Int
  | ToggleAutoUnload
  | SetImageDataUrl String
  | TriggerClearImage
  | TriggerDecompose
  | LayerClicked String

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
  { modelStatus: input.modelStatus
  , imageDataUrl: Nothing
  , numLayers: 5
  , autoDepth: true
  , depthProvider: ProviderOpenAI
  , zScale: 500
  , autoUnload: true
  , downloadState: NotAsked
  , decomposeState: NotAsked
  , progressMessage: ""
  , baseId: "lattice-layer-decomposition"
  }

-- =============================================================================
--                                                                    // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-layer-decomposition-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , HP.attr (HH.AttrName "aria-label") "AI Layer Decomposition"
    ]
    [ renderHeader state
    , renderContent state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.span [ cls [ "panel-title" ], HP.attr (HH.AttrName "style") panelTitleStyle ]
        [ HH.text "Layer Decomposition" ]
    , HH.span
        [ cls [ "badge" ]
        , HP.attr (HH.AttrName "style") (badgeStyle state.modelStatus)
        ]
        [ HH.text (modelStatusText state.modelStatus) ]
    ]

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "panel-content" ]
    , HP.attr (HH.AttrName "style") contentStyle
    ]
    [ renderModelStatusSection state
    , renderUploadSection state
    , renderOptionsSection state
    , renderActionSection state
    , renderProgressSection state
    , renderResultsSection state
    , renderErrorSection state
    ]

-- =============================================================================
--                                                    // model status // section
-- =============================================================================

renderModelStatusSection :: forall m. State -> H.ComponentHTML Action Slots m
renderModelStatusSection state =
  HH.div
    [ cls [ "section", "model-status-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ]
        [ HH.text "Model Status" ]
    , if state.modelStatus.downloaded
        then renderModelReady state
        else renderModelNotDownloaded state
    ]

renderModelNotDownloaded :: forall m. State -> H.ComponentHTML Action Slots m
renderModelNotDownloaded state =
  HH.div
    [ cls [ "model-not-downloaded" ]
    , HP.attr (HH.AttrName "style") modelNotDownloadedStyle
    ]
    [ HH.p [ cls [ "warning-text" ], HP.attr (HH.AttrName "style") warningTextStyle ]
        [ HH.span [ HP.attr (HH.AttrName "style") "margin-right: 8px;" ] [ HH.text "⚠" ]
        , HH.text "Qwen-Image-Layered model not downloaded"
        ]
    , HH.p [ cls [ "size-info" ], HP.attr (HH.AttrName "style") sizeInfoStyle ]
        [ HH.text "Download size: "
        , HH.strong_ [ HH.text "28.8 GB" ]
        ]
    , HH.button
        [ cls [ "download-btn" ]
        , HP.attr (HH.AttrName "style") downloadBtnStyle
        , HP.disabled (isDownloading state)
        , HE.onClick \_ -> TriggerDownload
        , HP.attr (HH.AttrName "aria-label") "Download model"
        ]
        [ HH.span [ cls [ "icon" ] ]
            [ HH.text (if isDownloading state then "⟳" else "↓") ]
        , HH.text (if isDownloading state then " Downloading..." else " Download Model")
        ]
    , case state.downloadState of
        Loading progress ->
          renderProgressBar progress state.progressMessage
        _ -> HH.text ""
    ]

renderModelReady :: forall m. State -> H.ComponentHTML Action Slots m
renderModelReady state =
  HH.div
    [ cls [ "model-ready" ]
    ]
    [ HH.div
        [ cls [ "status-row" ]
        , HP.attr (HH.AttrName "style") statusRowStyle
        ]
        [ HH.span [ cls [ "ready-icon" ], HP.attr (HH.AttrName "style") readyIconStyle ]
            [ HH.text "✓" ]
        , HH.span_ [ HH.text "Model Ready" ]
        , if state.modelStatus.loaded
            then HH.span
                   [ cls [ "loaded-badge" ]
                   , HP.attr (HH.AttrName "style") loadedBadgeStyle
                   ]
                   [ HH.text "Loaded" ]
            else HH.text ""
        ]
    , case state.modelStatus.verification of
        Just v ->
          HH.div
            [ cls [ "verification-info" ]
            , HP.attr (HH.AttrName "style") verificationInfoStyle
            ]
            [ HH.span
                [ HP.attr (HH.AttrName "style") (if v.verified then "color: #10B981;" else "color: #F59E0B;") ]
                [ HH.text v.message ]
            ]
        Nothing -> HH.text ""
    ]

-- =============================================================================
--                                                        // upload // section
-- =============================================================================

renderUploadSection :: forall m. State -> H.ComponentHTML Action Slots m
renderUploadSection state =
  HH.div
    [ cls [ "section", "upload-section" ]
    , HP.attr (HH.AttrName "style") (sectionStyle <> if not state.modelStatus.downloaded then " opacity: 0.5; pointer-events: none;" else "")
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ]
        [ HH.text "Source Image" ]
    , HH.div
        [ cls [ "upload-area" ]
        , HP.attr (HH.AttrName "style") uploadAreaStyle
        , HP.attr (HH.AttrName "role") "button"
        , HP.attr (HH.AttrName "tabindex") "0"
        , HP.attr (HH.AttrName "aria-label") "Click or drop image to upload"
        ]
        [ case state.imageDataUrl of
            Nothing ->
              HH.div
                [ cls [ "upload-placeholder" ]
                , HP.attr (HH.AttrName "style") uploadPlaceholderStyle
                ]
                [ HH.span [ HP.attr (HH.AttrName "style") "font-size: 2rem; margin-bottom: 8px;" ] [ HH.text "🖼" ]
                , HH.span_ [ HH.text "Click or drop image" ]
                ]
            Just url ->
              HH.img
                [ cls [ "preview-image" ]
                , HP.src url
                , HP.alt "Source image"
                , HP.attr (HH.AttrName "style") previewImageStyle
                ]
        ]
    , case state.imageDataUrl of
        Just _ ->
          HH.div
            [ cls [ "image-actions" ]
            , HP.attr (HH.AttrName "style") imageActionsStyle
            ]
            [ HH.button
                [ cls [ "clear-btn" ]
                , HP.attr (HH.AttrName "style") clearBtnStyle
                , HE.onClick \_ -> TriggerClearImage
                , HP.attr (HH.AttrName "aria-label") "Clear image"
                ]
                [ HH.text "× Clear" ]
            ]
        Nothing -> HH.text ""
    ]

-- =============================================================================
--                                                       // options // section
-- =============================================================================

renderOptionsSection :: forall m. State -> H.ComponentHTML Action Slots m
renderOptionsSection state =
  HH.div
    [ cls [ "section", "options-section" ]
    , HP.attr (HH.AttrName "style") (sectionStyle <> if isNothing state.imageDataUrl then " opacity: 0.5; pointer-events: none;" else "")
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ]
        [ HH.text "Options" ]
    
    -- Number of Layers
    , renderOptionRow "Number of Layers"
        [ HH.input
            [ HP.type_ HP.InputRange
            , HP.attr (HH.AttrName "style") rangeInputStyle
            , HP.min 3.0
            , HP.max 10.0
            , HP.step (HP.Step 1.0)
            , HP.value (show state.numLayers)
            , HE.onValueInput \v -> SetNumLayers (parseIntOr 5 v)
            , HP.attr (HH.AttrName "aria-label") "Number of layers"
            ]
        , HH.span [ cls [ "value" ], HP.attr (HH.AttrName "style") valueStyle ]
            [ HH.text (show state.numLayers) ]
        ]
    
    -- AI Depth Estimation
    , renderCheckboxOption "AI Depth Estimation" state.autoDepth ToggleAutoDepth
    
    -- Depth Provider (conditional)
    , if state.autoDepth
        then renderOptionRow "AI Provider"
               [ HH.select
                   [ cls [ "lattice-select" ]
                   , HP.attr (HH.AttrName "style") selectStyle
                   , HE.onValueInput \v -> SetDepthProvider (parseProvider v)
                   , HP.attr (HH.AttrName "aria-label") "AI provider"
                   ]
                   [ HH.option [ HP.value "openai", HP.selected (state.depthProvider == ProviderOpenAI) ]
                       [ HH.text "GPT-4o" ]
                   , HH.option [ HP.value "anthropic", HP.selected (state.depthProvider == ProviderAnthropic) ]
                       [ HH.text "Claude" ]
                   ]
               ]
        else HH.text ""
    
    -- Z-Space Scale
    , renderOptionRow "Z-Space Scale"
        [ HH.input
            [ HP.type_ HP.InputNumber
            , cls [ "lattice-input" ]
            , HP.attr (HH.AttrName "style") numberInputStyle
            , HP.min 100.0
            , HP.max 2000.0
            , HP.step (HP.Step 100.0)
            , HP.value (show state.zScale)
            , HE.onValueInput \v -> SetZScale (parseIntOr 500 v)
            , HP.attr (HH.AttrName "aria-label") "Z-space scale"
            ]
        , HH.span [ cls [ "unit" ], HP.attr (HH.AttrName "style") unitStyle ]
            [ HH.text "units" ]
        ]
    
    -- Auto-unload
    , renderCheckboxOption "Auto-unload model after" state.autoUnload ToggleAutoUnload
    ]

renderOptionRow :: forall m. String -> Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
renderOptionRow labelText children =
  HH.div
    [ cls [ "option-row" ]
    , HP.attr (HH.AttrName "style") optionRowStyle
    ]
    ([ HH.label [ HP.attr (HH.AttrName "style") optionLabelStyle ] [ HH.text labelText ] ] <> children)

renderCheckboxOption :: forall m. String -> Boolean -> Action -> H.ComponentHTML Action Slots m
renderCheckboxOption labelText checked action =
  HH.div
    [ cls [ "option-row", "checkbox" ]
    , HP.attr (HH.AttrName "style") optionRowCheckboxStyle
    ]
    [ HH.input
        [ HP.type_ HP.InputCheckbox
        , HP.checked checked
        , HE.onChecked \_ -> action
        , HP.attr (HH.AttrName "aria-label") labelText
        ]
    , HH.label [ HP.attr (HH.AttrName "style") "margin-left: 8px; cursor: pointer;" ]
        [ HH.text labelText ]
    ]

-- =============================================================================
--                                                        // action // section
-- =============================================================================

renderActionSection :: forall m. State -> H.ComponentHTML Action Slots m
renderActionSection state =
  HH.div
    [ cls [ "action-section" ]
    , HP.attr (HH.AttrName "style") actionSectionStyle
    ]
    [ HH.button
        [ cls [ "decompose-btn" ]
        , HP.attr (HH.AttrName "style") decomposeBtnStyle
        , HP.disabled (not (canDecompose state))
        , HE.onClick \_ -> TriggerDecompose
        , HP.attr (HH.AttrName "aria-label") "Decompose image"
        ]
        [ HH.span [ cls [ "icon" ] ]
            [ HH.text (if isDecomposing state then "⟳" else "⚡") ]
        , HH.text (if isDecomposing state then " Decomposing..." else " Decompose Image")
        ]
    ]

-- =============================================================================
--                                                      // progress // section
-- =============================================================================

renderProgressSection :: forall m. State -> H.ComponentHTML Action Slots m
renderProgressSection state =
  case state.decomposeState of
    Loading progress ->
      HH.div
        [ cls [ "progress-section" ]
        , HP.attr (HH.AttrName "style") progressSectionStyle
        ]
        [ renderProgressBar progress state.progressMessage ]
    _ -> HH.text ""

renderProgressBar :: forall m. Number -> String -> H.ComponentHTML Action Slots m
renderProgressBar progress message =
  HH.div
    [ cls [ "download-progress" ]
    , HP.attr (HH.AttrName "style") "margin-top: 12px;"
    ]
    [ HH.div
        [ cls [ "progress-bar" ]
        , HP.attr (HH.AttrName "style") progressBarStyle
        , HP.attr (HH.AttrName "role") "progressbar"
        , HP.attr (HH.AttrName "aria-valuenow") (show progress)
        , HP.attr (HH.AttrName "aria-valuemin") "0"
        , HP.attr (HH.AttrName "aria-valuemax") "100"
        ]
        [ HH.div
            [ cls [ "progress-fill" ]
            , HP.attr (HH.AttrName "style") (progressFillStyle progress)
            ]
            []
        ]
    , HH.div
        [ cls [ "progress-info" ]
        , HP.attr (HH.AttrName "style") progressInfoStyle
        ]
        [ HH.span_ [ HH.text message ]
        , HH.span_ [ HH.text (formatFixed 1 progress <> "%") ]
        ]
    ]

-- =============================================================================
--                                                       // results // section
-- =============================================================================

renderResultsSection :: forall m. State -> H.ComponentHTML Action Slots m
renderResultsSection state =
  case state.decomposeState of
    Success result ->
      if result.success
        then HH.div
               [ cls [ "results-section" ]
               , HP.attr (HH.AttrName "style") resultsSectionStyle
               ]
               [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ]
                   [ HH.text ("Created " <> show (length result.layers) <> " Layers") ]
               , HH.div
                   [ cls [ "layer-grid" ]
                   , HP.attr (HH.AttrName "style") layerGridStyle
                   ]
                   (map renderLayerCard result.layers)
               , case result.depthEstimation of
                   Just depth ->
                     HH.div
                       [ cls [ "depth-info" ]
                       , HP.attr (HH.AttrName "style") depthInfoStyle
                       ]
                       [ HH.p_ [ HH.text depth.sceneDescription ]
                       , HH.p [ cls [ "depth-range" ], HP.attr (HH.AttrName "style") depthRangeStyle ]
                           [ HH.text ("Depth range: " <> formatFixed 0 depth.depthRange.near <>
                                      " - " <> formatFixed 0 depth.depthRange.far) ]
                       ]
                   Nothing -> HH.text ""
               ]
        else HH.text ""
    _ -> HH.text ""

renderLayerCard :: forall m. LayerResult -> H.ComponentHTML Action Slots m
renderLayerCard layer =
  HH.div
    [ cls [ "layer-card" ]
    , HP.attr (HH.AttrName "style") layerCardStyle
    , HP.attr (HH.AttrName "role") "button"
    , HP.attr (HH.AttrName "tabindex") "0"
    , HE.onClick \_ -> LayerClicked layer.id
    , HP.attr (HH.AttrName "aria-label") ("Select layer: " <> layer.name)
    ]
    [ HH.div [ cls [ "layer-name" ], HP.attr (HH.AttrName "style") layerNameStyle ]
        [ HH.text layer.name ]
    , HH.div [ cls [ "layer-depth" ], HP.attr (HH.AttrName "style") layerDepthStyle ]
        [ HH.text ("Z: " <> formatFixed 0 layer.zPosition) ]
    ]

-- =============================================================================
--                                                         // error // section
-- =============================================================================

renderErrorSection :: forall m. State -> H.ComponentHTML Action Slots m
renderErrorSection state =
  case state.decomposeState of
    Failure err ->
      HH.div
        [ cls [ "error-section" ]
        , HP.attr (HH.AttrName "style") errorSectionStyle
        , HP.attr (HH.AttrName "role") "alert"
        ]
        [ HH.span [ HP.attr (HH.AttrName "style") "margin-right: 8px;" ] [ HH.text "⚠" ]
        , HH.span_ [ HH.text err ]
        ]
    Success result ->
      case result.error of
        Just err ->
          HH.div
            [ cls [ "error-section" ]
            , HP.attr (HH.AttrName "style") errorSectionStyle
            , HP.attr (HH.AttrName "role") "alert"
            ]
            [ HH.span [ HP.attr (HH.AttrName "style") "margin-right: 8px;" ] [ HH.text "⚠" ]
            , HH.span_ [ HH.text err ]
            ]
        Nothing -> HH.text ""
    _ -> HH.text ""

-- =============================================================================
--                                                       // helper // functions
-- =============================================================================

isDownloading :: State -> Boolean
isDownloading state = case state.downloadState of
  Loading _ -> true
  _ -> false

isDecomposing :: State -> Boolean
isDecomposing state = case state.decomposeState of
  Loading _ -> true
  _ -> false

canDecompose :: State -> Boolean
canDecompose state =
  state.modelStatus.downloaded &&
  isJust state.imageDataUrl &&
  not (isDecomposing state)

modelStatusText :: ModelStatus -> String
modelStatusText status
  | status.loaded = "Loaded"
  | status.downloaded = "Ready"
  | otherwise = "Not Downloaded"

parseIntOr :: Int -> String -> Int
parseIntOr default s = case Int.fromString s of
  Just n -> n
  Nothing -> default

parseProvider :: String -> DepthProvider
parseProvider = case _ of
  "anthropic" -> ProviderAnthropic
  _ -> ProviderOpenAI

-- =============================================================================
--                                                                    // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary); font-size: 14px;"

headerStyle :: String
headerStyle =
  "display: flex; align-items: center; justify-content: space-between; " <>
  "padding: 8px 12px; border-bottom: 1px solid var(--lattice-border-subtle); " <>
  "background: var(--lattice-surface-2);"

panelTitleStyle :: String
panelTitleStyle =
  "font-weight: 600;"

badgeStyle :: ModelStatus -> String
badgeStyle status =
  let
    baseStyle = "padding: 2px 8px; border-radius: 9999px; font-size: 12px; font-weight: 500; "
    colorStyle
      | status.loaded = "background: rgba(16, 185, 129, 0.2); color: #10B981;"
      | status.downloaded = "background: rgba(139, 92, 246, 0.2); color: var(--lattice-accent);"
      | otherwise = "background: rgba(239, 68, 68, 0.2); color: #EF4444;"
  in
    baseStyle <> colorStyle

contentStyle :: String
contentStyle =
  "flex: 1; overflow-y: auto; padding: 12px; display: flex; flex-direction: column; gap: 16px;"

sectionStyle :: String
sectionStyle =
  "background: var(--lattice-surface-2); border-radius: 8px; padding: 12px;"

sectionHeaderStyle :: String
sectionHeaderStyle =
  "font-weight: 600; margin-bottom: 8px; color: var(--lattice-text-muted); " <>
  "font-size: 12px; text-transform: uppercase; letter-spacing: 0.05em;"

modelNotDownloadedStyle :: String
modelNotDownloadedStyle =
  "text-align: center;"

warningTextStyle :: String
warningTextStyle =
  "color: #F59E0B; display: flex; align-items: center; justify-content: center; gap: 8px; margin-bottom: 8px;"

sizeInfoStyle :: String
sizeInfoStyle =
  "color: var(--lattice-text-muted); margin-bottom: 12px;"

downloadBtnStyle :: String
downloadBtnStyle =
  "width: 100%; padding: 10px 16px; background: var(--lattice-accent); color: white; " <>
  "border: none; border-radius: 8px; font-weight: 500; cursor: pointer; " <>
  "display: flex; align-items: center; justify-content: center; gap: 8px;"

statusRowStyle :: String
statusRowStyle =
  "display: flex; align-items: center; gap: 8px;"

readyIconStyle :: String
readyIconStyle =
  "color: #10B981; font-size: 16px;"

loadedBadgeStyle :: String
loadedBadgeStyle =
  "font-size: 11px; padding: 2px 6px; background: rgba(16, 185, 129, 0.2); " <>
  "color: #10B981; border-radius: 9999px;"

verificationInfoStyle :: String
verificationInfoStyle =
  "margin-top: 4px; font-size: 12px;"

uploadAreaStyle :: String
uploadAreaStyle =
  "border: 2px dashed var(--lattice-border); border-radius: 8px; " <>
  "padding: 24px; text-align: center; cursor: pointer; min-height: 150px; " <>
  "display: flex; align-items: center; justify-content: center;"

uploadPlaceholderStyle :: String
uploadPlaceholderStyle =
  "display: flex; flex-direction: column; align-items: center; gap: 8px; " <>
  "color: var(--lattice-text-muted);"

previewImageStyle :: String
previewImageStyle =
  "max-width: 100%; max-height: 200px; object-fit: contain; border-radius: 4px;"

imageActionsStyle :: String
imageActionsStyle =
  "margin-top: 8px; text-align: center;"

clearBtnStyle :: String
clearBtnStyle =
  "padding: 4px 12px; background: transparent; border: 1px solid var(--lattice-border); " <>
  "border-radius: 4px; color: var(--lattice-text-muted); cursor: pointer; font-size: 12px;"

optionRowStyle :: String
optionRowStyle =
  "display: flex; align-items: center; gap: 8px; margin-bottom: 8px;"

optionRowCheckboxStyle :: String
optionRowCheckboxStyle =
  "display: flex; align-items: center; margin-bottom: 8px;"

optionLabelStyle :: String
optionLabelStyle =
  "flex: 1; color: var(--lattice-text-muted);"

rangeInputStyle :: String
rangeInputStyle =
  "flex: 1; max-width: 120px;"

numberInputStyle :: String
numberInputStyle =
  "width: 80px; padding: 4px 8px; background: var(--lattice-surface-3); " <>
  "border: 1px solid var(--lattice-border); border-radius: 4px; " <>
  "color: var(--lattice-text-primary);"

selectStyle :: String
selectStyle =
  "flex: 1; max-width: 150px; padding: 4px 8px; background: var(--lattice-surface-3); " <>
  "border: 1px solid var(--lattice-border); border-radius: 4px; " <>
  "color: var(--lattice-text-primary);"

valueStyle :: String
valueStyle =
  "font-size: 12px; color: var(--lattice-text-muted); min-width: 40px;"

unitStyle :: String
unitStyle =
  "font-size: 12px; color: var(--lattice-text-muted); min-width: 40px;"

actionSectionStyle :: String
actionSectionStyle =
  "padding: 0 12px;"

decomposeBtnStyle :: String
decomposeBtnStyle =
  "width: 100%; padding: 12px 16px; " <>
  "background: linear-gradient(135deg, var(--lattice-accent), var(--lattice-accent-hover)); " <>
  "color: white; border: none; border-radius: 8px; font-weight: 600; cursor: pointer; " <>
  "display: flex; align-items: center; justify-content: center; gap: 8px;"

progressSectionStyle :: String
progressSectionStyle =
  "background: var(--lattice-surface-2); border-radius: 8px; padding: 12px;"

progressBarStyle :: String
progressBarStyle =
  "height: 6px; background: var(--lattice-surface-3); border-radius: 3px; overflow: hidden;"

progressFillStyle :: Number -> String
progressFillStyle percent =
  "height: 100%; background: linear-gradient(90deg, var(--lattice-accent), var(--lattice-accent-hover)); " <>
  "width: " <> show percent <> "%;"

progressInfoStyle :: String
progressInfoStyle =
  "display: flex; justify-content: space-between; font-size: 12px; " <>
  "color: var(--lattice-text-muted); margin-top: 4px;"

resultsSectionStyle :: String
resultsSectionStyle =
  "background: var(--lattice-surface-2); border-radius: 8px; padding: 12px;"

layerGridStyle :: String
layerGridStyle =
  "display: grid; grid-template-columns: repeat(auto-fill, minmax(100px, 1fr)); gap: 8px; margin-top: 8px;"

layerCardStyle :: String
layerCardStyle =
  "background: var(--lattice-surface-3); border-radius: 4px; padding: 8px; cursor: pointer;"

layerNameStyle :: String
layerNameStyle =
  "font-weight: 500; font-size: 13px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap;"

layerDepthStyle :: String
layerDepthStyle =
  "font-size: 11px; color: var(--lattice-text-muted);"

depthInfoStyle :: String
depthInfoStyle =
  "margin-top: 12px; padding-top: 8px; border-top: 1px solid var(--lattice-border-subtle); " <>
  "font-size: 12px; color: var(--lattice-text-muted);"

depthRangeStyle :: String
depthRangeStyle =
  "color: var(--lattice-text-muted);"

errorSectionStyle :: String
errorSectionStyle =
  "background: rgba(239, 68, 68, 0.1); border: 1px solid rgba(239, 68, 68, 0.3); " <>
  "border-radius: 8px; padding: 12px; color: #EF4444; display: flex; align-items: center; gap: 8px;"

-- =============================================================================
--                                                                   // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input -> do
    H.modify_ _ { modelStatus = input.modelStatus }

  TriggerDownload -> do
    H.modify_ _ { downloadState = Loading 0.0 }
    H.raise StartDownload

  SetNumLayers n -> do
    H.modify_ _ { numLayers = clamp 3 10 n }

  ToggleAutoDepth -> do
    H.modify_ \s -> s { autoDepth = not s.autoDepth }

  SetDepthProvider provider -> do
    H.modify_ _ { depthProvider = provider }

  SetZScale scale -> do
    H.modify_ _ { zScale = clamp 100 2000 scale }

  ToggleAutoUnload -> do
    H.modify_ \s -> s { autoUnload = not s.autoUnload }

  SetImageDataUrl url -> do
    H.modify_ _ { imageDataUrl = Just url, decomposeState = NotAsked }

  TriggerClearImage -> do
    H.modify_ _ { imageDataUrl = Nothing, decomposeState = NotAsked }
    H.raise ClearImage

  TriggerDecompose -> do
    state <- H.get
    case state.imageDataUrl of
      Just url -> do
        H.modify_ _ { decomposeState = Loading 0.0 }
        H.raise $ StartDecomposition
          { imageDataUrl: url
          , numLayers: state.numLayers
          , autoDepthEstimation: state.autoDepth
          , depthProvider: state.depthProvider
          , zSpaceScale: state.zScale
          , autoUnload: state.autoUnload
          }
      Nothing -> pure unit

  LayerClicked layerId -> do
    H.raise $ SelectLayer layerId

clamp :: Int -> Int -> Int -> Int
clamp minVal maxVal val = max minVal (min maxVal val)
