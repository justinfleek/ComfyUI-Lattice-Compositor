-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // lattice // ui // right-sidebar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Right Sidebar Component
-- |
-- | Split pane with collapsible property panels (top) and AI tools (bottom).
-- |
-- | Property Panels:
-- | - Properties: Layer transform, opacity, blend mode
-- | - Effects: Active effect controls
-- | - Drivers: Parameter animation drivers
-- | - Scopes: Waveform, vectorscope, histogram
-- | - Camera: 3D camera properties
-- | - Audio: Audio properties and waveform
-- | - Align: Layer alignment tools
-- | - Preview: Render preview settings
-- |
-- | AI Tools:
-- | - Chat: AI compositor agent conversation
-- | - Generate: AI generation (depth, normal, segment)
-- | - Flow: Generative flow trajectories
-- | - Decompose: AI layer decomposition
-- |
module Lattice.UI.Layout.RightSidebar
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , AITab(..)
  , ExpandedPanels
  , RightSidebarAction(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

data AITab
  = AIChat
  | AIGenerate
  | AIFlow
  | AIDecompose

derive instance eqAITab :: Eq AITab

type ExpandedPanels =
  { properties :: Boolean
  , effects :: Boolean
  , drivers :: Boolean
  , scopes :: Boolean
  , camera :: Boolean
  , audio :: Boolean
  , align :: Boolean
  , preview :: Boolean
  }

type Input =
  { aiTab :: AITab
  , expandedPanels :: ExpandedPanels
  , selectedLayerId :: Maybe String
  , hasSelection :: Boolean
  }

-- | Actions emitted from sidebar
data RightSidebarAction
  = AITabChanged AITab
  | PanelToggled String Boolean
  | CameraUpdated
  | SendChatMessage String
  | GenerateDepthMap
  | GenerateNormalMap
  | GenerateSegmentation
  | StartFlowGeneration
  | StartDecomposition

data Output = RightSidebarActionSelected RightSidebarAction

data Query a

type Slot id = H.Slot Query Output id

type State =
  { aiTab :: AITab
  , expandedPanels :: ExpandedPanels
  , selectedLayerId :: Maybe String
  , hasSelection :: Boolean
  }

data Action
  = Initialize
  | Receive Input
  | SwitchAITab AITab
  | TogglePanel String
  | EmitAction RightSidebarAction

type Slots :: Row Type
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
  { aiTab: input.aiTab
  , expandedPanels: input.expandedPanels
  , selectedLayerId: input.selectedLayerId
  , hasSelection: input.hasSelection
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-right-sidebar" ]
    , HP.attr (HH.AttrName "style") sidebarStyle
    ]
    [ -- Properties section (top)
      HH.div
        [ cls [ "lattice-properties-section" ]
        , HP.attr (HH.AttrName "style") propertiesSectionStyle
        ]
        [ HH.div
            [ cls [ "lattice-panel-scroll" ]
            , HP.attr (HH.AttrName "style") panelScrollStyle
            ]
            [ renderCollapsiblePanel state "Properties" "properties" renderPropertiesContent
            , renderCollapsiblePanel state "Effects" "effects" renderEffectsContent
            , renderCollapsiblePanel state "Drivers" "drivers" renderDriversContent
            , renderCollapsiblePanel state "Scopes" "scopes" renderScopesContent
            , renderCollapsiblePanel state "Camera" "camera" renderCameraContent
            , renderCollapsiblePanel state "Audio" "audio" renderAudioContent
            , renderCollapsiblePanel state "Align" "align" renderAlignContent
            , renderCollapsiblePanel state "Preview" "preview" renderPreviewContent
            ]
        ]
    
    , -- Resize handle
      HH.div
        [ cls [ "lattice-resize-handle" ]
        , HP.attr (HH.AttrName "style") resizeHandleStyle
        ]
        []
    
    , -- AI section (bottom)
      HH.div
        [ cls [ "lattice-ai-section" ]
        , HP.attr (HH.AttrName "style") aiSectionStyle
        ]
        [ -- AI header
          HH.div
            [ cls [ "lattice-ai-header" ]
            , HP.attr (HH.AttrName "style") aiHeaderStyle
            ]
            [ HH.span [ cls [ "lattice-ai-title" ] ] [ HH.text "AI Tools" ] ]
        
        , -- AI tabs
          HH.div
            [ cls [ "lattice-ai-tabs" ]
            , HP.attr (HH.AttrName "style") aiTabsStyle
            ]
            [ aiTabButton state AIChat "Chat" "AI Compositor Agent"
            , aiTabButton state AIGenerate "Generate" "AI Generation (Depth, Normal, Segment)"
            , aiTabButton state AIFlow "Flow" "Generative Flow Trajectories for Wan-Move"
            , aiTabButton state AIDecompose "Decompose" "AI Layer Decomposition"
            ]
        
        , -- AI content
          HH.div
            [ cls [ "lattice-ai-content" ]
            , HP.attr (HH.AttrName "style") aiContentStyle
            ]
            [ case state.aiTab of
                AIChat -> renderAIChatPanel
                AIGenerate -> renderAIGeneratePanel
                AIFlow -> renderAIFlowPanel
                AIDecompose -> renderAIDecomposePanel
            ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // collapsible panels
-- ════════════════════════════════════════════════════════════════════════════

renderCollapsiblePanel :: forall m. State -> String -> String -> (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
renderCollapsiblePanel state title key content =
  let
    isExpanded = getPanelExpanded state.expandedPanels key
  in
    HH.div
      [ cls [ "lattice-collapsible-panel" ]
      , HP.attr (HH.AttrName "style") collapsiblePanelStyle
      ]
      [ -- Panel header
        HH.div
          [ cls [ "lattice-panel-header" ]
          , HP.attr (HH.AttrName "style") collapsibleHeaderStyle
          , HE.onClick \_ -> TogglePanel key
          ]
          [ HH.span [ cls [ "lattice-expand-icon" ] ] 
              [ HH.text (if isExpanded then "▼" else "▶") ]
          , HH.span [ cls [ "lattice-panel-title" ] ] [ HH.text title ]
          ]
      
      , -- Panel content
        if isExpanded
          then HH.div
                 [ cls [ "lattice-panel-body" ]
                 , HP.attr (HH.AttrName "style") collapsibleBodyStyle
                 ]
                 [ content ]
          else HH.text ""
      ]

getPanelExpanded :: ExpandedPanels -> String -> Boolean
getPanelExpanded panels key = case key of
  "properties" -> panels.properties
  "effects" -> panels.effects
  "drivers" -> panels.drivers
  "scopes" -> panels.scopes
  "camera" -> panels.camera
  "audio" -> panels.audio
  "align" -> panels.align
  "preview" -> panels.preview
  _ -> false

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // panel contents
-- ════════════════════════════════════════════════════════════════════════════

renderPropertiesContent :: forall m. H.ComponentHTML Action Slots m
renderPropertiesContent =
  HH.div [ cls [ "lattice-properties-content" ] ]
    [ -- Transform section
      HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Position"
        , propRow
            [ propInput "X" "0"
            , propInput "Y" "0"
            , propInput "Z" "0"
            ]
        ]
    , HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Scale"
        , propRow
            [ propInput "X" "100%"
            , propInput "Y" "100%"
            , propInput "Z" "100%"
            ]
        ]
    , HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Rotation"
        , propRow
            [ propInput "X" "0°"
            , propInput "Y" "0°"
            , propInput "Z" "0°"
            ]
        ]
    , HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Opacity"
        , propSlider "100%"
        ]
    , HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Blend Mode"
        , propSelect [ "Normal", "Multiply", "Screen", "Overlay", "Add" ]
        ]
    ]

renderEffectsContent :: forall m. H.ComponentHTML Action Slots m
renderEffectsContent =
  HH.div [ cls [ "lattice-effects-content" ] ]
    [ HH.div
        [ cls [ "lattice-empty-state" ]
        , HP.attr (HH.AttrName "style") emptyStateStyle
        ]
        [ HH.text "No effects applied"
        , HH.br_
        , HH.text "Drag effects from the library"
        ]
    ]

renderDriversContent :: forall m. H.ComponentHTML Action Slots m
renderDriversContent =
  HH.div [ cls [ "lattice-drivers-content" ] ]
    [ HH.div
        [ cls [ "lattice-empty-state" ]
        , HP.attr (HH.AttrName "style") emptyStateStyle
        ]
        [ HH.text "No drivers configured"
        , HH.br_
        , HH.text "Add drivers to animate parameters"
        ]
    ]

renderScopesContent :: forall m. H.ComponentHTML Action Slots m
renderScopesContent =
  HH.div [ cls [ "lattice-scopes-content" ] ]
    [ HH.div
        [ cls [ "lattice-scope-display" ]
        , HP.attr (HH.AttrName "style") scopeDisplayStyle
        ]
        [ HH.div [ cls [ "lattice-waveform" ] ] [ HH.text "Waveform" ]
        , HH.div [ cls [ "lattice-vectorscope" ] ] [ HH.text "RGB Parade" ]
        ]
    ]

renderCameraContent :: forall m. H.ComponentHTML Action Slots m
renderCameraContent =
  HH.div [ cls [ "lattice-camera-content" ] ]
    [ HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Focal Length"
        , propSlider "50mm"
        ]
    , HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Aperture"
        , propSlider "f/2.8"
        ]
    , HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Focus Distance"
        , propSlider "10m"
        ]
    , HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Depth of Field"
        , propCheckbox "Enable" true
        ]
    ]

renderAudioContent :: forall m. H.ComponentHTML Action Slots m
renderAudioContent =
  HH.div [ cls [ "lattice-audio-content" ] ]
    [ HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Volume"
        , propSlider "100%"
        ]
    , HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Pan"
        , propSlider "Center"
        ]
    , HH.div
        [ cls [ "lattice-audio-waveform" ]
        , HP.attr (HH.AttrName "style") audioWaveformStyle
        ]
        [ HH.text "Audio Waveform" ]
    ]

renderAlignContent :: forall m. H.ComponentHTML Action Slots m
renderAlignContent =
  HH.div [ cls [ "lattice-align-content" ] ]
    [ -- Align buttons
      HH.div
        [ cls [ "lattice-align-row" ]
        , HP.attr (HH.AttrName "style") alignRowStyle
        ]
        [ alignButton "⬅" "Align Left"
        , alignButton "↔" "Center Horizontal"
        , alignButton "➡" "Align Right"
        ]
    , HH.div
        [ cls [ "lattice-align-row" ]
        , HP.attr (HH.AttrName "style") alignRowStyle
        ]
        [ alignButton "⬆" "Align Top"
        , alignButton "↕" "Center Vertical"
        , alignButton "⬇" "Align Bottom"
        ]
    , HH.div
        [ cls [ "lattice-align-row" ]
        , HP.attr (HH.AttrName "style") alignRowStyle
        ]
        [ alignButton "⊞" "Distribute Horizontal"
        , alignButton "⊟" "Distribute Vertical"
        ]
    ]

renderPreviewContent :: forall m. H.ComponentHTML Action Slots m
renderPreviewContent =
  HH.div [ cls [ "lattice-preview-content" ] ]
    [ HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Resolution"
        , propSelect [ "Full", "Half", "Quarter", "Eighth" ]
        ]
    , HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Frame Rate"
        , propSelect [ "30 fps", "24 fps", "60 fps" ]
        ]
    , HH.div [ cls [ "lattice-prop-group" ] ]
        [ propLabel "Motion Blur"
        , propCheckbox "Enable" false
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                               // AI panels
-- ════════════════════════════════════════════════════════════════════════════

aiTabButton :: forall m. State -> AITab -> String -> String -> H.ComponentHTML Action Slots m
aiTabButton state tab label tooltip =
  HH.button
    [ cls [ "lattice-ai-tab-btn" ]
    , HP.attr (HH.AttrName "style") (aiTabButtonStyle (state.aiTab == tab))
    , HP.title tooltip
    , HE.onClick \_ -> SwitchAITab tab
    ]
    [ HH.text label ]

renderAIChatPanel :: forall m. H.ComponentHTML Action Slots m
renderAIChatPanel =
  HH.div
    [ cls [ "lattice-ai-chat-panel" ]
    , HP.attr (HH.AttrName "style") aiPanelStyle
    ]
    [ -- Chat messages area
      HH.div
        [ cls [ "lattice-chat-messages" ]
        , HP.attr (HH.AttrName "style") chatMessagesStyle
        ]
        [ HH.div [ cls [ "lattice-chat-welcome" ] ]
            [ HH.text "Hi! I'm Lattice AI. I can help you:"
            , HH.ul_
                [ HH.li_ [ HH.text "Create and edit compositions" ]
                , HH.li_ [ HH.text "Apply and adjust effects" ]
                , HH.li_ [ HH.text "Generate AI content" ]
                , HH.li_ [ HH.text "Explain techniques" ]
                ]
            ]
        ]
    
    , -- Chat input
      HH.div
        [ cls [ "lattice-chat-input" ]
        , HP.attr (HH.AttrName "style") chatInputContainerStyle
        ]
        [ HH.textarea
            [ HP.placeholder "Ask anything..."
            , HP.attr (HH.AttrName "style") chatInputStyle
            ]
        , HH.button
            [ cls [ "lattice-chat-send" ]
            , HP.attr (HH.AttrName "style") chatSendStyle
            ]
            [ HH.text "→" ]
        ]
    ]

renderAIGeneratePanel :: forall m. H.ComponentHTML Action Slots m
renderAIGeneratePanel =
  HH.div
    [ cls [ "lattice-ai-generate-panel" ]
    , HP.attr (HH.AttrName "style") aiPanelStyle
    ]
    [ HH.div [ cls [ "lattice-generate-section" ] ]
        [ HH.div
            [ cls [ "lattice-section-title" ]
            , HP.attr (HH.AttrName "style") sectionTitleStyle
            ]
            [ HH.text "Generate Maps" ]
        , HH.div
            [ cls [ "lattice-generate-buttons" ]
            , HP.attr (HH.AttrName "style") generateButtonsStyle
            ]
            [ generateButton "Depth Map" "Generate depth from image" GenerateDepthMap
            , generateButton "Normal Map" "Generate surface normals" GenerateNormalMap
            , generateButton "Segmentation" "AI object segmentation" GenerateSegmentation
            ]
        ]
    
    , HH.div [ cls [ "lattice-generate-options" ] ]
        [ propLabel "Model"
        , propSelect [ "MiDaS v3.1", "Depth Anything v2", "ZoeDepth" ]
        , propLabel "Quality"
        , propSelect [ "Fast", "Balanced", "High Quality" ]
        ]
    ]

generateButton :: forall m. String -> String -> RightSidebarAction -> H.ComponentHTML Action Slots m
generateButton label tooltip action =
  HH.button
    [ cls [ "lattice-generate-btn" ]
    , HP.attr (HH.AttrName "style") generateBtnStyle
    , HP.title tooltip
    , HE.onClick \_ -> EmitAction action
    ]
    [ HH.text label ]

renderAIFlowPanel :: forall m. H.ComponentHTML Action Slots m
renderAIFlowPanel =
  HH.div
    [ cls [ "lattice-ai-flow-panel" ]
    , HP.attr (HH.AttrName "style") aiPanelStyle
    ]
    [ HH.div
        [ cls [ "lattice-section-title" ]
        , HP.attr (HH.AttrName "style") sectionTitleStyle
        ]
        [ HH.text "Generative Flow" ]
    , HH.div [ cls [ "lattice-flow-description" ] ]
        [ HH.p_ [ HH.text "Generate motion trajectories using optical flow analysis and AI prediction." ]
        ]
    , HH.div [ cls [ "lattice-flow-options" ] ]
        [ propLabel "Flow Method"
        , propSelect [ "RAFT", "PWC-Net", "FlowNet2" ]
        , propLabel "Temporal Window"
        , propSlider "5 frames"
        ]
    , HH.button
        [ cls [ "lattice-primary-btn" ]
        , HP.attr (HH.AttrName "style") primaryBtnStyle
        , HE.onClick \_ -> EmitAction StartFlowGeneration
        ]
        [ HH.text "Generate Flow" ]
    ]

renderAIDecomposePanel :: forall m. H.ComponentHTML Action Slots m
renderAIDecomposePanel =
  HH.div
    [ cls [ "lattice-ai-decompose-panel" ]
    , HP.attr (HH.AttrName "style") aiPanelStyle
    ]
    [ HH.div
        [ cls [ "lattice-section-title" ]
        , HP.attr (HH.AttrName "style") sectionTitleStyle
        ]
        [ HH.text "Layer Decomposition" ]
    , HH.div [ cls [ "lattice-decompose-description" ] ]
        [ HH.p_ [ HH.text "Automatically decompose an image into separate layers based on AI analysis." ]
        ]
    , HH.div [ cls [ "lattice-decompose-options" ] ]
        [ propLabel "Decomposition Mode"
        , propSelect [ "Foreground/Background", "Objects", "Depth Layers", "Semantic" ]
        , propLabel "Number of Layers"
        , propSlider "Auto"
        ]
    , HH.button
        [ cls [ "lattice-primary-btn" ]
        , HP.attr (HH.AttrName "style") primaryBtnStyle
        , HE.onClick \_ -> EmitAction StartDecomposition
        ]
        [ HH.text "Decompose" ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // property helpers
-- ════════════════════════════════════════════════════════════════════════════

propLabel :: forall m. String -> H.ComponentHTML Action Slots m
propLabel text =
  HH.div
    [ cls [ "lattice-prop-label" ]
    , HP.attr (HH.AttrName "style") propLabelStyle
    ]
    [ HH.text text ]

propRow :: forall m. Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
propRow children =
  HH.div
    [ cls [ "lattice-prop-row" ]
    , HP.attr (HH.AttrName "style") propRowStyle
    ]
    children

propInput :: forall m. String -> String -> H.ComponentHTML Action Slots m
propInput label value =
  HH.div [ cls [ "lattice-prop-input" ] ]
    [ HH.span
        [ cls [ "lattice-input-label" ]
        , HP.attr (HH.AttrName "style") inputLabelStyle
        ]
        [ HH.text label ]
    , HH.input
        [ HP.type_ HP.InputText
        , HP.value value
        , HP.attr (HH.AttrName "style") inputFieldStyle
        ]
    ]

propSlider :: forall m. String -> H.ComponentHTML Action Slots m
propSlider value =
  HH.div
    [ cls [ "lattice-prop-slider" ]
    , HP.attr (HH.AttrName "style") propSliderStyle
    ]
    [ HH.input
        [ HP.type_ HP.InputRange
        , HP.attr (HH.AttrName "style") sliderStyle
        ]
    , HH.span
        [ cls [ "lattice-slider-value" ]
        , HP.attr (HH.AttrName "style") sliderValueStyle
        ]
        [ HH.text value ]
    ]

propSelect :: forall m. Array String -> H.ComponentHTML Action Slots m
propSelect options =
  HH.select
    [ cls [ "lattice-prop-select" ]
    , HP.attr (HH.AttrName "style") selectStyle
    ]
    (map (\opt -> HH.option [] [ HH.text opt ]) options)

propCheckbox :: forall m. String -> Boolean -> H.ComponentHTML Action Slots m
propCheckbox label checked =
  HH.label
    [ cls [ "lattice-prop-checkbox" ]
    , HP.attr (HH.AttrName "style") checkboxStyle
    ]
    [ HH.input
        [ HP.type_ HP.InputCheckbox
        , HP.checked checked
        ]
    , HH.span [] [ HH.text label ]
    ]

alignButton :: forall m. String -> String -> H.ComponentHTML Action Slots m
alignButton icon tooltip =
  HH.button
    [ cls [ "lattice-align-btn" ]
    , HP.attr (HH.AttrName "style") alignBtnStyle
    , HP.title tooltip
    ]
    [ HH.text icon ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

sidebarStyle :: String
sidebarStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1, #121212);"

propertiesSectionStyle :: String
propertiesSectionStyle =
  "flex: 0 0 45%; min-height: 200px; " <>
  "border-bottom: 1px solid var(--lattice-border, #333);"

panelScrollStyle :: String
panelScrollStyle =
  "height: 100%; overflow-y: auto; overflow-x: hidden;"

resizeHandleStyle :: String
resizeHandleStyle =
  "height: 4px; cursor: row-resize; " <>
  "background: var(--lattice-surface-2, #1a1a1a);"

aiSectionStyle :: String
aiSectionStyle =
  "flex: 1; display: flex; flex-direction: column; min-height: 200px;"

aiHeaderStyle :: String
aiHeaderStyle =
  "padding: 6px 8px; background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-bottom: 1px solid var(--lattice-border, #333); " <>
  "font-size: 11px; font-weight: 600; text-transform: uppercase; " <>
  "letter-spacing: 0.5px; color: var(--lattice-text-secondary, #888);"

aiTabsStyle :: String
aiTabsStyle =
  "display: flex; gap: 0; background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-bottom: 1px solid var(--lattice-border, #333);"

aiTabButtonStyle :: Boolean -> String
aiTabButtonStyle active =
  "flex: 1; padding: 6px 4px; background: transparent; border: none; " <>
  "cursor: pointer; font-size: 10px; font-weight: 500; " <>
  "transition: all 0.15s ease; " <>
  if active
    then "color: var(--lattice-accent, #8b5cf6); " <>
         "background: var(--lattice-surface-1, #121212); " <>
         "border-bottom: 2px solid var(--lattice-accent, #8b5cf6);"
    else "color: var(--lattice-text-secondary, #888);"

aiContentStyle :: String
aiContentStyle =
  "flex: 1; overflow: auto;"

collapsiblePanelStyle :: String
collapsiblePanelStyle =
  "border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);"

collapsibleHeaderStyle :: String
collapsibleHeaderStyle =
  "display: flex; align-items: center; gap: 6px; padding: 8px 12px; " <>
  "cursor: pointer; font-size: 11px; font-weight: 500; " <>
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "transition: background 0.15s ease;"

collapsibleBodyStyle :: String
collapsibleBodyStyle =
  "padding: 8px 12px;"

emptyStateStyle :: String
emptyStateStyle =
  "text-align: center; padding: 16px; font-size: 11px; " <>
  "color: var(--lattice-text-tertiary, #666);"

scopeDisplayStyle :: String
scopeDisplayStyle =
  "display: grid; grid-template-columns: 1fr 1fr; gap: 8px; " <>
  "padding: 8px; background: var(--lattice-surface-0, #0a0a0a); " <>
  "border-radius: 4px; font-size: 10px; text-align: center; " <>
  "color: var(--lattice-text-tertiary, #666); min-height: 60px;"

audioWaveformStyle :: String
audioWaveformStyle =
  "height: 40px; background: var(--lattice-surface-0, #0a0a0a); " <>
  "border-radius: 4px; display: flex; align-items: center; " <>
  "justify-content: center; font-size: 10px; " <>
  "color: var(--lattice-text-tertiary, #666);"

alignRowStyle :: String
alignRowStyle =
  "display: flex; gap: 4px; justify-content: center; margin-bottom: 8px;"

alignBtnStyle :: String
alignBtnStyle =
  "width: 32px; height: 32px; padding: 0; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border, #333); " <>
  "border-radius: 4px; cursor: pointer; font-size: 14px; " <>
  "color: var(--lattice-text-primary, #e5e5e5);"

aiPanelStyle :: String
aiPanelStyle =
  "padding: 12px;"

chatMessagesStyle :: String
chatMessagesStyle =
  "flex: 1; overflow-y: auto; margin-bottom: 12px; " <>
  "font-size: 12px; color: var(--lattice-text-primary, #e5e5e5);"

chatInputContainerStyle :: String
chatInputContainerStyle =
  "display: flex; gap: 8px;"

chatInputStyle :: String
chatInputStyle =
  "flex: 1; min-height: 60px; padding: 8px; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border, #333); " <>
  "border-radius: 6px; font-size: 12px; resize: none; " <>
  "color: var(--lattice-text-primary, #e5e5e5);"

chatSendStyle :: String
chatSendStyle =
  "width: 40px; background: var(--lattice-accent, #8b5cf6); " <>
  "border: none; border-radius: 6px; cursor: pointer; " <>
  "font-size: 16px; color: white;"

sectionTitleStyle :: String
sectionTitleStyle =
  "font-size: 11px; font-weight: 600; margin-bottom: 12px; " <>
  "color: var(--lattice-text-secondary, #888);"

generateButtonsStyle :: String
generateButtonsStyle =
  "display: flex; flex-direction: column; gap: 8px; margin-bottom: 16px;"

generateBtnStyle :: String
generateBtnStyle =
  "padding: 10px 16px; background: var(--lattice-surface-2, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border, #333); " <>
  "border-radius: 6px; cursor: pointer; font-size: 12px; " <>
  "color: var(--lattice-text-primary, #e5e5e5); text-align: left; " <>
  "transition: all 0.15s ease;"

primaryBtnStyle :: String
primaryBtnStyle =
  "width: 100%; padding: 10px 16px; margin-top: 12px; " <>
  "background: var(--lattice-accent, #8b5cf6); " <>
  "border: none; border-radius: 6px; cursor: pointer; " <>
  "font-size: 12px; font-weight: 500; color: white;"

propLabelStyle :: String
propLabelStyle =
  "font-size: 10px; font-weight: 500; margin-bottom: 4px; " <>
  "color: var(--lattice-text-secondary, #888);"

propRowStyle :: String
propRowStyle =
  "display: flex; gap: 8px;"

inputLabelStyle :: String
inputLabelStyle =
  "font-size: 9px; color: var(--lattice-text-tertiary, #666); " <>
  "margin-right: 4px;"

inputFieldStyle :: String
inputFieldStyle =
  "width: 50px; padding: 4px 6px; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border, #333); " <>
  "border-radius: 3px; font-size: 11px; " <>
  "color: var(--lattice-text-primary, #e5e5e5);"

propSliderStyle :: String
propSliderStyle =
  "display: flex; align-items: center; gap: 8px;"

sliderStyle :: String
sliderStyle =
  "flex: 1; height: 4px;"

sliderValueStyle :: String
sliderValueStyle =
  "min-width: 50px; font-size: 11px; " <>
  "color: var(--lattice-text-primary, #e5e5e5);"

selectStyle :: String
selectStyle =
  "width: 100%; padding: 6px 8px; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border, #333); " <>
  "border-radius: 4px; font-size: 11px; " <>
  "color: var(--lattice-text-primary, #e5e5e5);"

checkboxStyle :: String
checkboxStyle =
  "display: flex; align-items: center; gap: 6px; " <>
  "font-size: 11px; cursor: pointer; " <>
  "color: var(--lattice-text-primary, #e5e5e5);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> 
    H.modify_ _ 
      { aiTab = input.aiTab
      , expandedPanels = input.expandedPanels
      , selectedLayerId = input.selectedLayerId
      , hasSelection = input.hasSelection
      }
  
  SwitchAITab tab -> do
    H.modify_ _ { aiTab = tab }
    H.raise (RightSidebarActionSelected (AITabChanged tab))
  
  TogglePanel key -> do
    state <- H.get
    let
      panels = state.expandedPanels
      newPanels = case key of
        "properties" -> panels { properties = not panels.properties }
        "effects" -> panels { effects = not panels.effects }
        "drivers" -> panels { drivers = not panels.drivers }
        "scopes" -> panels { scopes = not panels.scopes }
        "camera" -> panels { camera = not panels.camera }
        "audio" -> panels { audio = not panels.audio }
        "align" -> panels { align = not panels.align }
        "preview" -> panels { preview = not panels.preview }
        _ -> panels
      newExpanded = case key of
        "properties" -> not panels.properties
        "effects" -> not panels.effects
        "drivers" -> not panels.drivers
        "scopes" -> not panels.scopes
        "camera" -> not panels.camera
        "audio" -> not panels.audio
        "align" -> not panels.align
        "preview" -> not panels.preview
        _ -> false
    H.modify_ _ { expandedPanels = newPanels }
    H.raise (RightSidebarActionSelected (PanelToggled key newExpanded))
  
  EmitAction action -> 
    H.raise (RightSidebarActionSelected action)
