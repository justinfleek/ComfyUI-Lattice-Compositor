-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Workspace Layout AI Generation Render Functions
-- |
-- | Render functions for the AI generation panel in the right sidebar.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Layout.WorkspaceLayout.RenderAI
  ( renderRightSidebar
  ) where

import Prelude

import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.UI.Components.PropertiesPanel as PropertiesPanel
import Lattice.Project (LayerBase)

import Lattice.UI.Layout.WorkspaceLayout.Types
  ( State
  , Action(..)
  , Slots
  , LeftTab(..)
  , GenerationMode(..)
  , _properties
  )
import Lattice.UI.Layout.WorkspaceLayout.Styles as S

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // right sidebar
-- ════════════════════════════════════════════════════════════════════════════

renderRightSidebar :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderRightSidebar state =
  HH.div [ cls [ "lattice-sidebar-content" ] ]
    [ -- properties panel
      HH.slot _properties unit PropertiesPanel.component
        { selectedLayer: getSelectedLayer state }
        HandleProperties
    
      -- ai section
    , HH.div [ cls [ "lattice-ai-section" ] ]
        [ HH.div [ cls [ "lattice-sidebar-tabs" ] ]
            [ tabButton "Generate" true
            , tabButton "Chat" false
            , tabButton "Flow" false
            ]
        , HH.div [ cls [ "lattice-ai-content" ] ]
            [ renderAIGenerateContent state ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // ai generate content
-- ════════════════════════════════════════════════════════════════════════════

renderAIGenerateContent :: forall m. State -> H.ComponentHTML Action Slots m
renderAIGenerateContent state =
  HH.div_
    [ -- generation mode toggle buttons
      HH.div [ cls [ "lattice-mode-toggle" ] ]
        [ modeButton state TextToImage "T2I" "Text to Image"
        , modeButton state ImageEdit "Edit" "Image Edit (Inpaint/Outpaint)"
        , modeButton state ImageToVideo "I2V" "Image to Video"
        , modeButton state TextToVideo "T2V" "Text to Video"
        , modeButton state TextTo3D "3D" "Text/Image to 3D Model"
        ]
    
      -- model selector (changes based on mode)
    , HH.div [ cls [ "lattice-model-selector" ] ]
        [ HH.label [ HP.for "lattice-model-select" ] [ HH.text "Model" ]
        , HH.select 
            [ cls [ "lattice-select" ]
            , HP.id "lattice-model-select"
            , HP.value state.selectedModel
            , HE.onValueChange SetModel
            ]
            (modelsForMode state.generationMode)
        ]
    
      -- source image selector (for i2v, edit, and 3d modes)
    , case state.generationMode of
        ImageToVideo -> renderSourceImageSelector state
        ImageEdit -> renderSourceImageSelector state
        TextTo3D -> renderSourceImageSelector state  -- optional reference image
        _ -> HH.text ""
    
      -- mask controls (only for imageedit mode)
    , case state.generationMode of
        ImageEdit ->
          HH.div [ cls [ "lattice-mask-controls" ] ]
            [ HH.label_ [ HH.text "Mask" ]
            , HH.div [ cls [ "lattice-mask-options" ] ]
                [ HH.button 
                    [ cls [ "lattice-btn lattice-btn-ghost" ]
                    , HP.title "Draw mask in Draw tab"
                    , HE.onClick \_ -> SetLeftTab TabDraw
                    ]
                    [ HH.text "Draw Mask" ]
                , HH.button 
                    [ cls [ "lattice-btn lattice-btn-ghost" ]
                    , HP.title "Auto-generate mask from selection"
                    ]
                    [ HH.text "Auto Mask" ]
                ]
            , HH.div [ cls [ "lattice-mask-info lattice-text-muted" ] ]
                [ HH.text "White = edit, Black = keep" ]
            ]
        _ -> HH.text ""
    
      -- prompt input
    , HH.div [ cls [ "lattice-prompt-container" ] ]
        [ HH.label [ HP.for "lattice-prompt" ] [ HH.text "Prompt" ]
        , HH.textarea
            [ cls [ "lattice-prompt-input" ]
            , HP.id "lattice-prompt"
            , HP.placeholder "Describe what you want to generate..."
            , HP.attr (HH.AttrName "rows") "3"
            , HP.value state.promptText
            , HE.onValueInput SetPromptText
            ]
        ]
    
      -- negative prompt (collapsible)
    , HH.div [ cls [ "lattice-prompt-container" ] ]
        [ HH.label [ HP.for "lattice-negative-prompt" ] [ HH.text "Negative Prompt" ]
        , HH.textarea
            [ cls [ "lattice-prompt-input lattice-prompt-negative" ]
            , HP.id "lattice-negative-prompt"
            , HP.placeholder "What to avoid..."
            , HP.attr (HH.AttrName "rows") "2"
            , HP.value state.negativePrompt
            , HE.onValueInput SetNegativePrompt
            ]
        ]
    
      -- generation parameters
    , renderGenerationParams state
    
      -- error display
    , case state.renderError of
        Just err -> 
          HH.div [ cls [ "lattice-error" ] ] 
            [ HH.text err ]
        Nothing -> HH.text ""
    
      -- progress bar (shown during generation)
    , if state.isRendering
        then renderProgressBar state
        else HH.text ""
    
      -- generate button
    , HH.div [ cls [ "lattice-generate-actions" ] ]
        [ HH.button 
            [ cls [ "lattice-btn lattice-btn-primary lattice-btn-lg" ]
            , HP.disabled (state.isRendering || state.promptText == "")
            , HE.onClick \_ -> GenerateFromPrompt
            ]
            [ HH.text (if state.isRendering then "Generating..." else "Generate") ]
        ]
    
      -- connection status
    , case state.bridgeClient of
        Nothing -> 
          HH.div [ cls [ "lattice-connection-status lattice-disconnected" ] ]
            [ HH.text "Backend disconnected" ]
        Just _ ->
          HH.div [ cls [ "lattice-connection-status lattice-connected" ] ]
            [ HH.text "Connected" ]
    ]

renderGenerationParams :: forall m. State -> H.ComponentHTML Action Slots m
renderGenerationParams state =
  HH.div [ cls [ "lattice-gen-params" ] ]
    [ -- frames (only for video modes)
      case state.generationMode of
        TextToImage -> HH.text ""
        _ -> 
          HH.div [ cls [ "lattice-param" ] ]
            [ HH.label [ HP.for "lattice-frames" ] [ HH.text "Frames" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.id "lattice-frames"
                , HP.value (show state.numFrames)
                , HP.attr (HH.AttrName "min") "1"
                , HP.attr (HH.AttrName "max") "300"
                ]
            ]
    , HH.div [ cls [ "lattice-param" ] ]
        [ HH.label [ HP.for "lattice-cfg-scale" ] [ HH.text "CFG Scale" ]
        , HH.input
            [ HP.type_ HP.InputNumber
            , HP.id "lattice-cfg-scale"
            , HP.value (show state.cfgScale)
            , HP.attr (HH.AttrName "min") "1"
            , HP.attr (HH.AttrName "max") "20"
            , HP.attr (HH.AttrName "step") "0.5"
            ]
        ]
    , HH.div [ cls [ "lattice-param" ] ]
        [ HH.label [ HP.for "lattice-steps" ] [ HH.text "Steps" ]
        , HH.input
            [ HP.type_ HP.InputNumber
            , HP.id "lattice-steps"
            , HP.value (show state.steps)
            , HP.attr (HH.AttrName "min") "1"
            , HP.attr (HH.AttrName "max") "100"
            ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // progress
-- ════════════════════════════════════════════════════════════════════════════

-- | progress bar for generation
renderProgressBar :: forall m. State -> H.ComponentHTML Action Slots m
renderProgressBar state =
  HH.div [ cls [ "lattice-progress-container" ] ]
    [ -- stage label
      HH.div [ cls [ "lattice-progress-header" ] ]
        [ HH.span [ cls [ "lattice-progress-stage" ] ]
            [ HH.text (stageLabel state.generationStage) ]
        , HH.span [ cls [ "lattice-progress-percentage" ] ]
            [ HH.text (show (floor state.generationProgress) <> "%") ]
        ]
    
      -- progress bar track
    , HH.div 
        [ cls [ "lattice-progress-track" ]
        , HP.attr (HH.AttrName "style") S.progressTrackStyle
        ]
        [ -- progress bar fill
          HH.div 
            [ cls [ "lattice-progress-fill" ]
            , HP.attr (HH.AttrName "style") (S.progressFillStyle state.generationProgress)
            ]
            []
        ]
    
      -- eta display
    , case state.generationEta of
        Just eta -> 
          HH.div [ cls [ "lattice-progress-eta lattice-text-muted" ] ]
            [ HH.text ("~" <> formatEta eta <> " remaining") ]
        Nothing -> HH.text ""
    ]

stageLabel :: String -> String
stageLabel = case _ of
  "encoding" -> "Encoding prompt..."
  "sampling" -> "Sampling..."
  "decoding" -> "Decoding frames..."
  "idle" -> "Preparing..."
  other -> other

formatEta :: Number -> String
formatEta seconds =
  if seconds < 60.0
    then show (floor seconds) <> "s"
    else 
      let mins = floor (seconds / 60.0)
          secs = floor (seconds - (toNumber mins * 60.0))
      in show mins <> "m " <> show secs <> "s"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | mode toggle button helper
modeButton :: forall m. State -> GenerationMode -> String -> String -> H.ComponentHTML Action Slots m
modeButton state mode label title =
  HH.button
    [ cls [ "lattice-mode-btn" ]
    , HP.attr (HH.AttrName "data-state") (if state.generationMode == mode then "active" else "inactive")
    , HE.onClick \_ -> SetGenerationMode mode
    , HP.title title
    ]
    [ HH.text label ]

-- | source image selector for i2v, edit, and 3d modes
renderSourceImageSelector :: forall m. State -> H.ComponentHTML Action Slots m
renderSourceImageSelector state =
  HH.div [ cls [ "lattice-source-image" ] ]
    [ HH.label_ [ HH.text "Source Image" ]
    , case state.sourceImageUrl of
        Nothing ->
          HH.div [ cls [ "lattice-source-options" ] ]
            [ HH.button 
                [ cls [ "lattice-btn lattice-btn-ghost" ]
                , HP.title "Select from imported assets"
                ]
                [ HH.text "From Assets" ]
            , HH.button 
                [ cls [ "lattice-btn lattice-btn-ghost" ]
                , HP.title "Use current render preview"
                ]
                [ HH.text "From Preview" ]
            , HH.button 
                [ cls [ "lattice-btn lattice-btn-ghost" ]
                , HP.title "Capture current scene view"
                ]
                [ HH.text "From Scene" ]
            ]
        Just url ->
          HH.div [ cls [ "lattice-source-preview" ] ]
            [ HH.img 
                [ HP.src url
                , HP.alt "Source"
                , HP.attr (HH.AttrName "style") "max-width: 100%; max-height: 80px; object-fit: contain;"
                ]
            , HH.button 
                [ cls [ "lattice-btn-icon" ]
                , HP.title "Clear source image"
                , HE.onClick \_ -> SetSourceImage ""
                ]
                [ HH.text "x" ]
            ]
    ]

-- | get available models for a generation mode
modelsForMode :: forall m. GenerationMode -> Array (H.ComponentHTML Action Slots m)
modelsForMode = case _ of
  TextToImage ->
    [ HH.option [ HP.value "flux-1-dev" ] [ HH.text "Flux 1 Dev" ]
    , HH.option [ HP.value "flux-schnell" ] [ HH.text "Flux Schnell" ]
    , HH.option [ HP.value "flux-2-dev" ] [ HH.text "Flux 2 Dev" ]
    , HH.option [ HP.value "qwen-image" ] [ HH.text "Qwen Image" ]
    , HH.option [ HP.value "z-image" ] [ HH.text "Z-Image" ]
    ]
  ImageEdit ->
    [ HH.option [ HP.value "flux-2-dev" ] [ HH.text "Flux 2 Dev" ]
    , HH.option [ HP.value "z-image-edit" ] [ HH.text "Z-Image Edit" ]
    , HH.option [ HP.value "qwen-image-edit" ] [ HH.text "Qwen Image Edit" ]
    ]
  ImageToVideo ->
    [ HH.option [ HP.value "ati" ] [ HH.text "ATI" ]
    , HH.option [ HP.value "wan-move" ] [ HH.text "Wan Move" ]
    , HH.option [ HP.value "ltx-2" ] [ HH.text "LTX 2" ]
    , HH.option [ HP.value "hunyuan-video" ] [ HH.text "Hunyuan Video" ]
    ]
  TextToVideo ->
    [ HH.option [ HP.value "wan-2.1" ] [ HH.text "Wan 2.1" ]
    , HH.option [ HP.value "hunyuan-video" ] [ HH.text "Hunyuan Video" ]
    , HH.option [ HP.value "ltx-2" ] [ HH.text "LTX 2" ]
    , HH.option [ HP.value "mochi" ] [ HH.text "Mochi" ]
    ]
  TextTo3D ->
    [ HH.option [ HP.value "trellis-2" ] [ HH.text "Trellis 2" ]
    , HH.option [ HP.value "hunyuan-3d" ] [ HH.text "Hunyuan 3D" ]
    ]

getSelectedLayer :: State -> Maybe LayerBase
getSelectedLayer state =
  case state.selectedLayerIds of
    [layerId] -> findLayer layerId state.layers
    _ -> Nothing

findLayer :: String -> Array LayerBase -> Maybe LayerBase
findLayer _layerId _layers = Nothing  -- simplified for now

tabButton :: forall m. String -> Boolean -> H.ComponentHTML Action Slots m
tabButton label active =
  HH.button
    [ cls [ "lattice-tabs-trigger" ]
    , HP.attr (HH.AttrName "data-state") (if active then "active" else "inactive")
    ]
    [ HH.text label ]
