-- | Audio Value Preview Component
-- |
-- | Shows real-time audio feature values at the current frame.
-- | Updates as the user scrubs through the timeline.
-- |
-- | Features displayed:
-- | - Amplitude (with bar visualization)
-- | - Frequency bands (bass, mid, high)
-- | - HPSS (harmonic/percussive)
-- | - Beat indicator
-- | - Spectral features (centroid, flux)
-- | - BPM and frame info
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/AudioValuePreview.vue
module Lattice.UI.Components.AudioValuePreview
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , AudioAnalysis
  , AudioFeatures
  ) where

import Prelude

import Data.Int as Int
import Data.Maybe (Maybe(..), isJust)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls)
import Lattice.UI.Utils (formatFixed)

-- =============================================================================
--                                                                      // types
-- =============================================================================

type Input =
  { audioAnalysis :: Maybe AudioAnalysis
  , currentFrame :: Int
  }

data Output
  = ToggleExpanded

data Query a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                         // domain // types
-- =============================================================================

type AudioAnalysis =
  { frameCount :: Int
  , bpm :: Maybe Number
  , features :: AudioFeatures
  }

type AudioFeatures =
  { amplitude :: Number        -- 0-1
  , bass :: Number             -- 0-1
  , mid :: Number              -- 0-1
  , high :: Number             -- 0-1
  , harmonic :: Number         -- 0-1
  , percussive :: Number       -- 0-1
  , spectralCentroid :: Number -- 0-1
  , spectralFlux :: Number     -- 0-1
  , isBeat :: Boolean
  }

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { audioAnalysis :: Maybe AudioAnalysis
  , currentFrame :: Int
  , expanded :: Boolean
  , baseId :: String
  }

data Action
  = Initialize
  | Receive Input
  | ToggleExpandedView

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
  { audioAnalysis: input.audioAnalysis
  , currentFrame: input.currentFrame
  , expanded: false
  , baseId: "lattice-audio-preview"
  }

-- =============================================================================
--                                                                    // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  case state.audioAnalysis of
    Just analysis ->
      HH.div
        [ cls [ "lattice-audio-value-preview" ]
        , HP.attr (HH.AttrName "style") panelStyle
        , HP.attr (HH.AttrName "role") "region"
        , HP.attr (HH.AttrName "aria-label") "Audio Values"
        ]
        [ renderHeader state analysis.features.isBeat
        , renderMainValues analysis.features
        , if state.expanded
            then renderExpandedValues state analysis
            else HH.text ""
        ]
    Nothing ->
      HH.div
        [ cls [ "no-audio" ]
        , HP.attr (HH.AttrName "style") noAudioStyle
        ]
        [ HH.span_ [ HH.text "Load audio to see values" ] ]

renderHeader :: forall m. State -> Boolean -> H.ComponentHTML Action Slots m
renderHeader state isBeat =
  HH.div
    [ cls [ "preview-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    , HE.onClick \_ -> ToggleExpandedView
    , HP.attr (HH.AttrName "role") "button"
    , HP.attr (HH.AttrName "aria-expanded") (if state.expanded then "true" else "false")
    , HP.attr (HH.AttrName "tabindex") "0"
    ]
    [ HH.span [ cls [ "header-title" ], HP.attr (HH.AttrName "style") headerTitleStyle ]
        [ HH.text "Audio Values" ]
    , HH.span
        [ cls [ "beat-indicator" ]
        , HP.attr (HH.AttrName "style") (beatIndicatorStyle isBeat)
        , HP.attr (HH.AttrName "aria-live") "polite"
        ]
        [ HH.text "BEAT" ]
    , HH.span [ cls [ "expand-icon" ], HP.attr (HH.AttrName "style") expandIconStyle ]
        [ HH.text (if state.expanded then "▼" else "▶") ]
    ]

-- =============================================================================
--                                                       // main values section
-- =============================================================================

renderMainValues :: forall m. AudioFeatures -> H.ComponentHTML Action Slots m
renderMainValues features =
  HH.div
    [ cls [ "main-values" ]
    , HP.attr (HH.AttrName "style") mainValuesStyle
    ]
    [ renderValueRow "Amplitude" features.amplitude "amplitude"
    , renderFrequencyBands features
    ]

renderValueRow :: forall m. String -> Number -> String -> H.ComponentHTML Action Slots m
renderValueRow label value barClass =
  HH.div
    [ cls [ "value-row" ]
    , HP.attr (HH.AttrName "style") valueRowStyle
    ]
    [ HH.span [ cls [ "value-label" ], HP.attr (HH.AttrName "style") valueLabelStyle ]
        [ HH.text label ]
    , HH.div
        [ cls [ "value-bar-container" ]
        , HP.attr (HH.AttrName "style") valueBarContainerStyle
        , HP.attr (HH.AttrName "role") "progressbar"
        , HP.attr (HH.AttrName "aria-valuenow") (show (value * 100.0))
        , HP.attr (HH.AttrName "aria-valuemin") "0"
        , HP.attr (HH.AttrName "aria-valuemax") "100"
        , HP.attr (HH.AttrName "aria-label") label
        ]
        [ HH.div
            [ cls [ "value-bar", barClass ]
            , HP.attr (HH.AttrName "style") (valueBarStyle barClass value)
            ]
            []
        ]
    , HH.span [ cls [ "value-text" ], HP.attr (HH.AttrName "style") valueTextStyle ]
        [ HH.text (formatPercent value) ]
    ]

renderFrequencyBands :: forall m. AudioFeatures -> H.ComponentHTML Action Slots m
renderFrequencyBands features =
  HH.div
    [ cls [ "frequency-bands" ]
    , HP.attr (HH.AttrName "style") frequencyBandsStyle
    , HP.attr (HH.AttrName "aria-label") "Frequency bands"
    ]
    [ renderBand "Bass" features.bass "bass"
    , renderBand "Mid" features.mid "mid"
    , renderBand "High" features.high "high"
    ]

renderBand :: forall m. String -> Number -> String -> H.ComponentHTML Action Slots m
renderBand label value bandClass =
  HH.div
    [ cls [ "band" ]
    , HP.attr (HH.AttrName "style") bandStyle
    ]
    [ HH.div
        [ cls [ "band-bar", bandClass ]
        , HP.attr (HH.AttrName "style") (bandBarStyle bandClass value)
        , HP.attr (HH.AttrName "role") "progressbar"
        , HP.attr (HH.AttrName "aria-valuenow") (show (value * 100.0))
        , HP.attr (HH.AttrName "aria-label") label
        ]
        []
    , HH.span [ cls [ "band-label" ], HP.attr (HH.AttrName "style") bandLabelStyle ]
        [ HH.text label ]
    ]

-- =============================================================================
--                                                   // expanded values section
-- =============================================================================

renderExpandedValues :: forall m. State -> AudioAnalysis -> H.ComponentHTML Action Slots m
renderExpandedValues state analysis =
  HH.div
    [ cls [ "expanded-values" ]
    , HP.attr (HH.AttrName "style") expandedValuesStyle
    ]
    [ -- HPSS Section
      HH.div [ cls [ "section-title" ], HP.attr (HH.AttrName "style") sectionTitleStyle ]
        [ HH.text "HPSS (Harmonic/Percussive)" ]
    , renderValueRow "Harmonic" analysis.features.harmonic "harmonic"
    , renderValueRow "Percussive" analysis.features.percussive "percussive"
    
      -- Spectral Section
    , HH.div [ cls [ "section-title" ], HP.attr (HH.AttrName "style") (sectionTitleStyle <> " margin-top: 8px;") ]
        [ HH.text "Spectral" ]
    , renderValueRow "Centroid" analysis.features.spectralCentroid "spectral"
    , renderValueRow "Flux" analysis.features.spectralFlux "spectral"
    
      -- Info Section
    , HH.div [ cls [ "section-title" ], HP.attr (HH.AttrName "style") (sectionTitleStyle <> " margin-top: 8px;") ]
        [ HH.text "Info" ]
    , renderInfoRow "BPM" (formatBpm analysis.bpm)
    , renderInfoRow "Frame" (show state.currentFrame <> " / " <> show analysis.frameCount)
    ]

renderInfoRow :: forall m. String -> String -> H.ComponentHTML Action Slots m
renderInfoRow label value =
  HH.div
    [ cls [ "info-row" ]
    , HP.attr (HH.AttrName "style") infoRowStyle
    ]
    [ HH.span_ [ HH.text (label <> ":") ]
    , HH.span [ cls [ "info-value" ], HP.attr (HH.AttrName "style") infoValueStyle ]
        [ HH.text value ]
    ]

-- =============================================================================
--                                                       // helper // functions
-- =============================================================================

formatPercent :: Number -> String
formatPercent n = show (Int.round (n * 100.0)) <> "%"

formatBpm :: Maybe Number -> String
formatBpm = case _ of
  Just bpm -> formatFixed 1 bpm
  Nothing -> "N/A"

-- =============================================================================
--                                                                    // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "background: var(--lattice-surface-1); border-radius: 4px; padding: 8px; font-size: 11px;"

noAudioStyle :: String
noAudioStyle =
  "padding: 16px; text-align: center; color: var(--lattice-text-muted); font-size: 11px;"

headerStyle :: String
headerStyle =
  "display: flex; align-items: center; gap: 8px; cursor: pointer; " <>
  "padding-bottom: 8px; border-bottom: 1px solid var(--lattice-border-subtle); margin-bottom: 8px;"

headerTitleStyle :: String
headerTitleStyle =
  "font-weight: 600; color: var(--lattice-text-primary); flex: 1;"

beatIndicatorStyle :: Boolean -> String
beatIndicatorStyle active =
  "padding: 2px 6px; border-radius: 3px; font-size: 9px; font-weight: 700; " <>
  "transition: all 0.1s ease; " <>
  if active
    then "background: var(--lattice-accent); color: white; box-shadow: 0 0 8px var(--lattice-accent);"
    else "background: var(--lattice-surface-2); color: var(--lattice-text-muted);"

expandIconStyle :: String
expandIconStyle =
  "color: var(--lattice-text-muted); font-size: 10px;"

mainValuesStyle :: String
mainValuesStyle =
  "display: flex; flex-direction: column; gap: 6px;"

valueRowStyle :: String
valueRowStyle =
  "display: flex; align-items: center; gap: 8px;"

valueLabelStyle :: String
valueLabelStyle =
  "width: 70px; color: var(--lattice-text-muted); flex-shrink: 0;"

valueBarContainerStyle :: String
valueBarContainerStyle =
  "flex: 1; height: 8px; background: var(--lattice-surface-0); border-radius: 4px; overflow: hidden;"

valueBarStyle :: String -> Number -> String
valueBarStyle barClass value =
  let
    baseStyle = "height: 100%; border-radius: 4px; transition: width 0.05s ease; "
    colorStyle = case barClass of
      "amplitude" -> "background: linear-gradient(90deg, var(--lattice-accent), #ec4899);"
      "harmonic" -> "background: #10b981;"
      "percussive" -> "background: #f59e0b;"
      "spectral" -> "background: #06b6d4;"
      _ -> "background: var(--lattice-accent);"
    widthStyle = "width: " <> formatPercent value <> ";"
  in
    baseStyle <> colorStyle <> widthStyle

valueTextStyle :: String
valueTextStyle =
  "width: 40px; text-align: right; color: var(--lattice-text-primary); font-family: monospace;"

frequencyBandsStyle :: String
frequencyBandsStyle =
  "display: flex; justify-content: space-around; height: 50px; padding: 8px 0; gap: 4px;"

bandStyle :: String
bandStyle =
  "display: flex; flex-direction: column; align-items: center; flex: 1;"

bandBarStyle :: String -> Number -> String
bandBarStyle bandClass value =
  let
    baseStyle = "width: 100%; max-width: 30px; border-radius: 3px; transition: height 0.05s ease; "
    colorStyle = case bandClass of
      "bass" -> "background: #ef4444;"
      "mid" -> "background: #f59e0b;"
      "high" -> "background: #10b981;"
      _ -> "background: var(--lattice-accent);"
    heightStyle = "height: " <> formatPercent value <> ";"
  in
    baseStyle <> colorStyle <> heightStyle

bandLabelStyle :: String
bandLabelStyle =
  "margin-top: 4px; font-size: 9px; color: var(--lattice-text-muted);"

expandedValuesStyle :: String
expandedValuesStyle =
  "margin-top: 12px; padding-top: 12px; border-top: 1px solid var(--lattice-border-subtle); " <>
  "display: flex; flex-direction: column; gap: 6px;"

sectionTitleStyle :: String
sectionTitleStyle =
  "font-size: 9px; font-weight: 600; color: var(--lattice-text-muted); " <>
  "text-transform: uppercase; letter-spacing: 0.5px; margin-bottom: 4px;"

infoRowStyle :: String
infoRowStyle =
  "display: flex; justify-content: space-between; color: var(--lattice-text-muted);"

infoValueStyle :: String
infoValueStyle =
  "color: var(--lattice-text-primary); font-family: monospace;"

-- =============================================================================
--                                                                   // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input -> do
    H.modify_ _ { audioAnalysis = input.audioAnalysis, currentFrame = input.currentFrame }

  ToggleExpandedView -> do
    H.modify_ \s -> s { expanded = not s.expanded }
    H.raise ToggleExpanded
