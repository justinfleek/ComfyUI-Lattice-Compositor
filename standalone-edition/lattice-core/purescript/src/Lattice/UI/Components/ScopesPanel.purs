-- | Scopes Panel Component
-- |
-- | Professional video scopes panel with:
-- | - Waveform monitor (luma and RGB)
-- | - Vectorscope (YUV color wheel)
-- | - Histogram (RGB distribution)
-- | - RGB Parade (separate R/G/B waveforms)
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/ScopesPanel.vue
module Lattice.UI.Components.ScopesPanel
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , ScopeType(..)
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Web.Event.Event as Event
import Web.HTML as HTML
import Web.HTML.HTMLElement as HTMLElement
import Web.HTML.Window as Window
import Web.UIEvent.KeyboardEvent as KE

import Lattice.UI.Core (cls, textMuted)
import Lattice.UI.Utils (getElementById)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { imageData :: Maybe ImageDataRef
  }

-- | Opaque reference to canvas ImageData
-- | In real implementation, this would be FFI to JavaScript ImageData
type ImageDataRef = { width :: Int, height :: Int }

data Output
  = ScopeTypeChanged ScopeType

data Query a

type Slot id = H.Slot Query Output id

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // scope // types
-- ════════════════════════════════════════════════════════════════════════════

data ScopeType
  = ScopeWaveform
  | ScopeVectorscope
  | ScopeHistogram
  | ScopeRGBParade

derive instance eqScopeType :: Eq ScopeType

instance showScopeType :: Show ScopeType where
  show = case _ of
    ScopeWaveform -> "waveform"
    ScopeVectorscope -> "vectorscope"
    ScopeHistogram -> "histogram"
    ScopeRGBParade -> "rgb-parade"

scopeLabel :: ScopeType -> String
scopeLabel = case _ of
  ScopeWaveform -> "Waveform"
  ScopeVectorscope -> "Vectorscope"
  ScopeHistogram -> "Histogram"
  ScopeRGBParade -> "RGB Parade"

scopeIcon :: ScopeType -> String
scopeIcon = case _ of
  ScopeWaveform -> "〰"
  ScopeVectorscope -> "◎"
  ScopeHistogram -> "▤"
  ScopeRGBParade -> "▦"

data WaveformMode
  = WaveformLuma
  | WaveformRGB
  | WaveformParade

derive instance eqWaveformMode :: Eq WaveformMode

type ScopeSettings =
  { brightness :: Number      -- 0.0 to 2.0
  , showGuides :: Boolean
  , showPeaks :: Boolean
  , waveformMode :: WaveformMode
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // state
-- ════════════════════════════════════════════════════════════════════════════

type State =
  { imageData :: Maybe ImageDataRef
  , activeScope :: ScopeType
  , settings :: ScopeSettings
  , isAnalyzing :: Boolean
  , baseId :: String
  }

data Action
  = Initialize
  | Receive Input
  | SetScopeType ScopeType
  | SetBrightness Number
  | ToggleGuides
  | TogglePeaks
  | SetWaveformMode WaveformMode
  | HandleKeyDown Int KE.KeyboardEvent  -- Index of focused tab

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
  { imageData: input.imageData
  , activeScope: ScopeWaveform
  , settings:
      { brightness: 1.0
      , showGuides: true
      , showPeaks: false
      , waveformMode: WaveformLuma
      }
  , isAnalyzing: false
  , baseId: "lattice-scopes"
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-scopes-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , HP.attr (HH.AttrName "aria-label") "Video Scopes"
    ]
    [ renderHeader state
    , renderScopeSelector state
    , renderScopeDisplay state
    , renderSettings state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader _state =
  HH.div
    [ cls [ "lattice-panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.span [ cls [ "lattice-panel-title" ] ] 
        [ HH.text "Scopes" ]
    ]

-- | All available scope types for keyboard navigation
allScopeTypes :: Array ScopeType
allScopeTypes = [ ScopeWaveform, ScopeVectorscope, ScopeHistogram, ScopeRGBParade ]

renderScopeSelector :: forall m. State -> H.ComponentHTML Action Slots m
renderScopeSelector state =
  HH.div
    [ cls [ "scope-selector" ]
    , HP.attr (HH.AttrName "style") selectorStyle
    , HP.attr (HH.AttrName "role") "tablist"
    , HP.attr (HH.AttrName "aria-label") "Scope type selector"
    , HP.attr (HH.AttrName "aria-orientation") "horizontal"
    ]
    (Array.mapWithIndex (scopeButton state) allScopeTypes)

scopeButton :: forall m. State -> Int -> ScopeType -> H.ComponentHTML Action Slots m
scopeButton state idx scopeType =
  let
    isSelected = scopeType == state.activeScope
    tabId = state.baseId <> "-tab-" <> show scopeType
    panelId = state.baseId <> "-panel-" <> show scopeType
  in
  HH.button
    [ cls [ "scope-btn" ]
    , HP.type_ HP.ButtonButton
    , HP.id tabId
    , HP.tabIndex (if isSelected then 0 else (-1))
    , HP.attr (HH.AttrName "style") (scopeButtonStyle isSelected)
    , HP.attr (HH.AttrName "title") (scopeLabel scopeType)
    , HP.attr (HH.AttrName "role") "tab"
    , ARIA.selected (show isSelected)
    , ARIA.controls panelId
    , HP.attr (HH.AttrName "data-state") (if isSelected then "active" else "inactive")
    , HE.onClick \_ -> SetScopeType scopeType
    , HE.onKeyDown (HandleKeyDown idx)
    ]
    [ HH.span [ cls [ "scope-icon" ], HP.attr (HH.AttrName "aria-hidden") "true" ] 
        [ HH.text (scopeIcon scopeType) ]
    , HH.span [ cls [ "scope-label" ] ] [ HH.text (scopeLabel scopeType) ]
    ]

renderScopeDisplay :: forall m. State -> H.ComponentHTML Action Slots m
renderScopeDisplay state =
  let
    tabId = state.baseId <> "-tab-" <> show state.activeScope
    panelId = state.baseId <> "-panel-" <> show state.activeScope
  in
  HH.div
    [ cls [ "scope-display" ]
    , HP.id panelId
    , HP.attr (HH.AttrName "style") displayStyle
    , HP.attr (HH.AttrName "role") "tabpanel"
    , HP.tabIndex 0
    , ARIA.labelledBy tabId
    , HP.attr (HH.AttrName "data-state") "active"
    ]
    [ case state.imageData of
        Nothing -> renderNoImage
        Just _imgData -> renderScope state
    ]

renderNoImage :: forall m. H.ComponentHTML Action Slots m
renderNoImage =
  HH.div
    [ cls [ "no-image" ]
    , HP.attr (HH.AttrName "style") noImageStyle
    ]
    [ textMuted "No image data available"
    , HH.p [ cls [ "hint" ] ] 
        [ textMuted "Select a layer or play timeline" ]
    ]

renderScope :: forall m. State -> H.ComponentHTML Action Slots m
renderScope state =
  HH.div
    [ cls [ "scope-canvas-container" ]
    , HP.attr (HH.AttrName "style") canvasContainerStyle
    ]
    [ -- Canvas for scope rendering
      HH.canvas
        [ cls [ "scope-canvas" ]
        , HP.attr (HH.AttrName "style") canvasStyle
        , HP.attr (HH.AttrName "width") "400"
        , HP.attr (HH.AttrName "height") "300"
        ]
    
      -- Overlay for guides
    , if state.settings.showGuides
        then renderGuides state
        else HH.text ""
    
      -- Scope label
    , HH.div [ cls [ "scope-label-overlay" ], HP.attr (HH.AttrName "style") labelOverlayStyle ]
        [ HH.text (scopeLabel state.activeScope) ]
    ]

renderGuides :: forall m. State -> H.ComponentHTML Action Slots m
renderGuides state =
  HH.div
    [ cls [ "scope-guides" ]
    , HP.attr (HH.AttrName "style") guidesStyle
    ]
    [ case state.activeScope of
        ScopeWaveform -> renderWaveformGuides
        ScopeVectorscope -> renderVectorscopeGuides
        ScopeHistogram -> renderHistogramGuides
        ScopeRGBParade -> renderParadeGuides
    ]

renderWaveformGuides :: forall m. H.ComponentHTML Action Slots m
renderWaveformGuides =
  HH.div [ cls [ "waveform-guides" ] ]
    [ HH.div [ cls [ "guide-line" ], HP.attr (HH.AttrName "style") (guideLineStyle 0.0) ] 
        [ HH.span [ cls [ "guide-label" ] ] [ HH.text "100" ] ]
    , HH.div [ cls [ "guide-line" ], HP.attr (HH.AttrName "style") (guideLineStyle 25.0) ] 
        [ HH.span [ cls [ "guide-label" ] ] [ HH.text "75" ] ]
    , HH.div [ cls [ "guide-line" ], HP.attr (HH.AttrName "style") (guideLineStyle 50.0) ] 
        [ HH.span [ cls [ "guide-label" ] ] [ HH.text "50" ] ]
    , HH.div [ cls [ "guide-line" ], HP.attr (HH.AttrName "style") (guideLineStyle 75.0) ] 
        [ HH.span [ cls [ "guide-label" ] ] [ HH.text "25" ] ]
    , HH.div [ cls [ "guide-line" ], HP.attr (HH.AttrName "style") (guideLineStyle 100.0) ] 
        [ HH.span [ cls [ "guide-label" ] ] [ HH.text "0" ] ]
    ]

renderVectorscopeGuides :: forall m. H.ComponentHTML Action Slots m
renderVectorscopeGuides =
  HH.div [ cls [ "vectorscope-guides" ] ]
    [ -- Color targets (skin tone, primary colors)
      HH.div [ cls [ "vs-target vs-red" ], HP.attr (HH.AttrName "style") (colorTargetStyle "right" "top") ] 
          [ HH.text "R" ]
    , HH.div [ cls [ "vs-target vs-yellow" ], HP.attr (HH.AttrName "style") (colorTargetStyle "right" "center") ] 
          [ HH.text "Y" ]
    , HH.div [ cls [ "vs-target vs-green" ], HP.attr (HH.AttrName "style") (colorTargetStyle "right" "bottom") ] 
          [ HH.text "G" ]
    , HH.div [ cls [ "vs-target vs-cyan" ], HP.attr (HH.AttrName "style") (colorTargetStyle "left" "bottom") ] 
          [ HH.text "C" ]
    , HH.div [ cls [ "vs-target vs-blue" ], HP.attr (HH.AttrName "style") (colorTargetStyle "left" "center") ] 
          [ HH.text "B" ]
    , HH.div [ cls [ "vs-target vs-magenta" ], HP.attr (HH.AttrName "style") (colorTargetStyle "left" "top") ] 
          [ HH.text "M" ]
      -- Skin tone line
    , HH.div [ cls [ "skin-tone-line" ], HP.attr (HH.AttrName "style") skinToneLineStyle ] []
      -- Graticule circles
    , HH.div [ cls [ "graticule" ], HP.attr (HH.AttrName "style") graticuleStyle ] []
    ]

renderHistogramGuides :: forall m. H.ComponentHTML Action Slots m
renderHistogramGuides =
  HH.div [ cls [ "histogram-guides" ] ]
    [ HH.div [ cls [ "hist-zone shadows" ], HP.attr (HH.AttrName "style") (histZoneStyle 0.0 33.0) ] 
        [ HH.text "Shadows" ]
    , HH.div [ cls [ "hist-zone midtones" ], HP.attr (HH.AttrName "style") (histZoneStyle 33.0 34.0) ] 
        [ HH.text "Midtones" ]
    , HH.div [ cls [ "hist-zone highlights" ], HP.attr (HH.AttrName "style") (histZoneStyle 67.0 33.0) ] 
        [ HH.text "Highlights" ]
    ]

renderParadeGuides :: forall m. H.ComponentHTML Action Slots m
renderParadeGuides =
  HH.div [ cls [ "parade-guides" ] ]
    [ HH.div [ cls [ "parade-channel" ], HP.attr (HH.AttrName "style") (paradeChannelStyle 0.0 "red") ] 
        [ HH.text "R" ]
    , HH.div [ cls [ "parade-channel" ], HP.attr (HH.AttrName "style") (paradeChannelStyle 33.3 "green") ] 
        [ HH.text "G" ]
    , HH.div [ cls [ "parade-channel" ], HP.attr (HH.AttrName "style") (paradeChannelStyle 66.6 "blue") ] 
        [ HH.text "B" ]
    ]

renderSettings :: forall m. State -> H.ComponentHTML Action Slots m
renderSettings state =
  HH.div
    [ cls [ "scope-settings" ]
    , HP.attr (HH.AttrName "style") settingsStyle
    ]
    [ -- Brightness slider
      HH.div [ cls [ "setting-row" ], HP.attr (HH.AttrName "style") settingRowStyle ]
        [ HH.label_ [ HH.text "Brightness" ]
        , HH.input
            [ HP.type_ HP.InputRange
            , HP.attr (HH.AttrName "min") "0.1"
            , HP.attr (HH.AttrName "max") "2.0"
            , HP.attr (HH.AttrName "step") "0.1"
            , HP.value (show state.settings.brightness)
            ]
        ]
    
      -- Checkboxes
    , HH.div [ cls [ "setting-row" ], HP.attr (HH.AttrName "style") settingRowStyle ]
        [ HH.label_
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.settings.showGuides
                , HE.onChecked \_ -> ToggleGuides
                ]
            , HH.text " Show Guides"
            ]
        , HH.label_
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.settings.showPeaks
                , HE.onChecked \_ -> TogglePeaks
                ]
            , HH.text " Show Peaks"
            ]
        ]
    
      -- Waveform mode (only for waveform scope)
    , if state.activeScope == ScopeWaveform
        then HH.div [ cls [ "waveform-modes" ], HP.attr (HH.AttrName "style") waveformModesStyle ]
            [ waveformModeButton "Luma" WaveformLuma state.settings.waveformMode
            , waveformModeButton "RGB" WaveformRGB state.settings.waveformMode
            , waveformModeButton "Parade" WaveformParade state.settings.waveformMode
            ]
        else HH.text ""
    ]

waveformModeButton :: forall m. String -> WaveformMode -> WaveformMode -> H.ComponentHTML Action Slots m
waveformModeButton labelText mode activeMode =
  HH.button
    [ cls [ "wf-mode-btn" ]
    , HP.attr (HH.AttrName "style") (waveformModeButtonStyle (mode == activeMode))
    , HE.onClick \_ -> SetWaveformMode mode
    ]
    [ HH.text labelText ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // styles
-- ════════════════════════════════════════════════════════════════════════════

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary); " <>
  "font-size: 12px;"

headerStyle :: String
headerStyle =
  "padding: 8px 12px; background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle); " <>
  "font-weight: 600; font-size: 12px;"

selectorStyle :: String
selectorStyle =
  "display: flex; padding: 8px; gap: 4px; " <>
  "background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

scopeButtonStyle :: Boolean -> String
scopeButtonStyle active =
  "flex: 1; display: flex; flex-direction: column; align-items: center; gap: 2px; " <>
  "padding: 6px 4px; border: none; border-radius: 4px; cursor: pointer; " <>
  "background: " <> (if active then "var(--lattice-accent-muted)" else "transparent") <> "; " <>
  "color: " <> (if active then "var(--lattice-accent)" else "var(--lattice-text-secondary)") <> "; " <>
  "font-size: 10px;"

displayStyle :: String
displayStyle =
  "flex: 1; position: relative; background: #000; " <>
  "min-height: 200px; overflow: hidden;"

noImageStyle :: String
noImageStyle =
  "display: flex; flex-direction: column; align-items: center; justify-content: center; " <>
  "height: 100%; gap: 8px; color: var(--lattice-text-muted);"

canvasContainerStyle :: String
canvasContainerStyle =
  "position: relative; width: 100%; height: 100%;"

canvasStyle :: String
canvasStyle =
  "width: 100%; height: 100%; display: block;"

labelOverlayStyle :: String
labelOverlayStyle =
  "position: absolute; top: 8px; left: 8px; " <>
  "padding: 2px 6px; background: rgba(0,0,0,0.6); " <>
  "border-radius: 3px; font-size: 10px; " <>
  "color: rgba(255,255,255,0.7);"

guidesStyle :: String
guidesStyle =
  "position: absolute; inset: 0; pointer-events: none;"

guideLineStyle :: Number -> String
guideLineStyle topPercent =
  "position: absolute; left: 0; right: 0; height: 1px; " <>
  "top: " <> show topPercent <> "%; " <>
  "background: rgba(255,255,255,0.2); " <>
  "border-top: 1px dashed rgba(255,255,255,0.15);"

colorTargetStyle :: String -> String -> String
colorTargetStyle hPos vPos =
  let
    h = case hPos of
          "left" -> "left: 15%"
          "right" -> "right: 15%"
          _ -> "left: 50%"
    v = case vPos of
          "top" -> "top: 15%"
          "center" -> "top: 50%"
          "bottom" -> "bottom: 15%"
          _ -> "top: 50%"
  in
    "position: absolute; " <> h <> "; " <> v <> "; " <>
    "width: 20px; height: 20px; " <>
    "border: 1px solid rgba(255,255,255,0.5); " <>
    "border-radius: 50%; " <>
    "display: flex; align-items: center; justify-content: center; " <>
    "font-size: 8px; color: rgba(255,255,255,0.7);"

skinToneLineStyle :: String
skinToneLineStyle =
  "position: absolute; top: 50%; left: 50%; " <>
  "width: 80%; height: 1px; " <>
  "transform: translate(-50%, -50%) rotate(-22deg); " <>
  "background: linear-gradient(90deg, transparent, rgba(255,200,150,0.4), transparent);"

graticuleStyle :: String
graticuleStyle =
  "position: absolute; top: 50%; left: 50%; " <>
  "width: 80%; height: 80%; " <>
  "transform: translate(-50%, -50%); " <>
  "border: 1px solid rgba(255,255,255,0.2); " <>
  "border-radius: 50%;"

histZoneStyle :: Number -> Number -> String
histZoneStyle leftPercent widthPercent =
  "position: absolute; bottom: 0; height: 100%; " <>
  "left: " <> show leftPercent <> "%; " <>
  "width: " <> show widthPercent <> "%; " <>
  "border-right: 1px dashed rgba(255,255,255,0.15); " <>
  "display: flex; align-items: flex-end; justify-content: center; " <>
  "padding-bottom: 4px; font-size: 9px; color: rgba(255,255,255,0.4);"

paradeChannelStyle :: Number -> String -> String
paradeChannelStyle leftPercent color =
  let
    c = case color of
          "red" -> "rgba(255,0,0,0.3)"
          "green" -> "rgba(0,255,0,0.3)"
          "blue" -> "rgba(0,100,255,0.3)"
          _ -> "rgba(255,255,255,0.3)"
  in
    "position: absolute; top: 0; bottom: 0; " <>
    "left: " <> show leftPercent <> "%; " <>
    "width: 33.3%; " <>
    "border-right: 1px solid rgba(255,255,255,0.15); " <>
    "background: " <> c <> "; " <>
    "display: flex; align-items: flex-start; justify-content: center; " <>
    "padding-top: 4px; font-size: 10px; font-weight: bold; " <>
    "color: rgba(255,255,255,0.7);"

settingsStyle :: String
settingsStyle =
  "padding: 8px 12px; background: var(--lattice-surface-2); " <>
  "border-top: 1px solid var(--lattice-border-subtle);"

settingRowStyle :: String
settingRowStyle =
  "display: flex; align-items: center; gap: 12px; margin-bottom: 6px;"

waveformModesStyle :: String
waveformModesStyle =
  "display: flex; gap: 4px;"

waveformModeButtonStyle :: Boolean -> String
waveformModeButtonStyle active =
  "padding: 4px 8px; border: none; border-radius: 3px; cursor: pointer; " <>
  "background: " <> (if active then "var(--lattice-accent)" else "var(--lattice-surface-3)") <> "; " <>
  "color: " <> (if active then "white" else "var(--lattice-text-secondary)") <> "; " <>
  "font-size: 11px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ { imageData = input.imageData }
  
  SetScopeType scopeType -> do
    H.modify_ _ { activeScope = scopeType }
    H.raise (ScopeTypeChanged scopeType)
  
  SetBrightness brightness -> do
    H.modify_ \s -> s { settings = s.settings { brightness = brightness } }
  
  ToggleGuides -> do
    H.modify_ \s -> s { settings = s.settings { showGuides = not s.settings.showGuides } }
  
  TogglePeaks -> do
    H.modify_ \s -> s { settings = s.settings { showPeaks = not s.settings.showPeaks } }
  
  SetWaveformMode mode -> do
    H.modify_ \s -> s { settings = s.settings { waveformMode = mode } }
  
  HandleKeyDown currentIdx ke -> do
    state <- H.get
    let
      key = KE.key ke
      scopeCount = Array.length allScopeTypes
      
      -- Navigate based on key
      nextIdx = case key of
        "ArrowRight" -> Just ((currentIdx + 1) `mod` scopeCount)
        "ArrowLeft" -> Just ((currentIdx - 1 + scopeCount) `mod` scopeCount)
        "Home" -> Just 0
        "End" -> Just (scopeCount - 1)
        _ -> Nothing

    for_ nextIdx \idx -> do
      liftEffect $ Event.preventDefault (KE.toEvent ke)
      case Array.index allScopeTypes idx of
        Just scopeType -> do
          -- Focus the tab
          doc <- liftEffect $ HTML.window >>= Window.document
          let tabId = state.baseId <> "-tab-" <> show scopeType
          mEl <- liftEffect $ getElementById tabId doc
          for_ mEl \el -> liftEffect $ HTMLElement.focus el
          
          -- Automatically select on focus (automatic activation mode)
          handleAction (SetScopeType scopeType)
        Nothing -> pure unit


