-- | AudioTrack Component
-- |
-- | Timeline audio track showing:
-- | - Waveform visualization
-- | - BPM badge
-- | - Playhead position
-- | - Beat markers (onsets)
-- | - Peak markers
-- | - Hover tooltip with frame/time
module Lattice.UI.Components.AudioTrack
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , AudioAnalysis
  , PeakData
  ) where

import Prelude

import Data.Array (mapWithIndex, length)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Audio analysis data
type AudioAnalysis =
  { bpm :: Number
  , onsets :: Array Int           -- Beat marker frames
  , amplitudeEnvelope :: Array Number
  , rmsEnergy :: Array Number
  }

-- | Peak detection data
type PeakData =
  { indices :: Array Int          -- Peak frame indices
  , values :: Array Number        -- Peak amplitude values
  }

type Input =
  { hasAudio :: Boolean           -- Whether audio is loaded
  , analysis :: Maybe AudioAnalysis
  , peakData :: Maybe PeakData
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Int
  , height :: Int
  }

data Output
  = Seek Int  -- Seek to frame

data Query a

type Slot id = H.Slot Query Output id

type State =
  { hasAudio :: Boolean
  , analysis :: Maybe AudioAnalysis
  , peakData :: Maybe PeakData
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Int
  , height :: Int
  , hoverFrame :: Maybe Int
  }

data Action
  = Receive Input
  | HandleClick Int
  | HandleMouseMove Int
  | HandleMouseLeave

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { hasAudio: input.hasAudio
  , analysis: input.analysis
  , peakData: input.peakData
  , currentFrame: input.currentFrame
  , totalFrames: input.totalFrames
  , fps: input.fps
  , height: input.height
  , hoverFrame: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-audio-track" ]
    , HP.attr (HH.AttrName "style") (audioTrackStyle state.height)
    ]
    [ -- Track header
      renderHeader state
    
      -- Waveform container or empty state
    , if state.hasAudio
        then renderWaveformContainer state
        else renderNoAudio
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ cls [ "lattice-audio-track-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ -- Volume icon
      HH.span [ cls [ "lattice-audio-icon" ] ]
        [ HH.text "🔊" ]
    
      -- Track name
    , HH.span [ cls [ "lattice-audio-track-name" ] ]
        [ HH.text "Audio" ]
    
      -- BPM badge (if analysis available)
    , case state.analysis of
        Just analysis ->
          HH.span
            [ cls [ "lattice-bpm-badge" ]
            , HP.attr (HH.AttrName "style") bpmBadgeStyle
            ]
            [ HH.text (show (Int.round analysis.bpm) <> " BPM") ]
        Nothing ->
          HH.text ""
    ]

renderWaveformContainer :: forall m. State -> H.ComponentHTML Action () m
renderWaveformContainer state =
  let
    playheadPct = Int.toNumber state.currentFrame / Int.toNumber state.totalFrames * 100.0
    
    -- Get onsets from analysis
    onsets = case state.analysis of
      Just a -> a.onsets
      Nothing -> []
    
    -- Get peak indices from peakData  
    peaks = case state.peakData of
      Just p -> p.indices
      Nothing -> []
  in
  HH.div
    [ cls [ "lattice-waveform-container" ]
    , HP.attr (HH.AttrName "style") waveformContainerStyle
    ]
    [ -- Waveform canvas (placeholder - actual drawing would use canvas FFI)
      HH.div
        [ cls [ "lattice-waveform-canvas" ]
        , HP.attr (HH.AttrName "style") waveformCanvasStyle
        ]
        [ -- Placeholder waveform visualization using bars
          renderWaveformBars state
        ]
    
      -- Playhead
    , HH.div
        [ cls [ "lattice-audio-playhead" ]
        , HP.attr (HH.AttrName "style") (audioPlayheadStyle playheadPct)
        ]
        []
    
      -- Hover indicator
    , case state.hoverFrame of
        Just hoverFrame ->
          let 
            hoverPct = Int.toNumber hoverFrame / Int.toNumber state.totalFrames * 100.0
          in
          HH.div
            [ cls [ "lattice-hover-indicator" ]
            , HP.attr (HH.AttrName "style") (hoverIndicatorStyle hoverPct)
            ]
            [ HH.div
                [ cls [ "lattice-hover-tooltip" ]
                , HP.attr (HH.AttrName "style") hoverTooltipStyle
                ]
                [ HH.text ("Frame " <> show hoverFrame)
                , HH.br_
                , HH.text (formatTime hoverFrame state.fps)
                ]
            ]
        Nothing ->
          HH.text ""
    
      -- Beat markers (onsets)
    , HH.div [ cls [ "lattice-beat-markers" ] ]
        (map (renderBeatMarker state.totalFrames) onsets)
    
      -- Peak markers
    , HH.div [ cls [ "lattice-peak-markers" ] ]
        (map (renderPeakMarker state.totalFrames) peaks)
    ]

renderWaveformBars :: forall m. State -> H.ComponentHTML Action () m
renderWaveformBars state =
  let
    -- Generate simple visualization bars based on amplitude envelope
    bars = case state.analysis of
      Just analysis -> 
        -- Use amplitude envelope if available, or generate placeholder
        if length analysis.amplitudeEnvelope > 0
          then mapWithIndex (\i amp -> { index: i, amplitude: amp }) analysis.amplitudeEnvelope
          else generatePlaceholderBars 50
      Nothing -> 
        generatePlaceholderBars 50
  in
  HH.div
    [ cls [ "lattice-waveform-bars" ]
    , HP.attr (HH.AttrName "style") waveformBarsStyle
    ]
    (map renderBar bars)
  where
    generatePlaceholderBars :: Int -> Array { index :: Int, amplitude :: Number }
    generatePlaceholderBars count = 
      mapWithIndex (\i _ -> { index: i, amplitude: 0.3 }) (replicate count unit)
    
    replicate :: forall a. Int -> a -> Array a
    replicate n x = 
      if n <= 0 then []
      else [x] <> replicate (n - 1) x
    
    renderBar :: forall w i. { index :: Int, amplitude :: Number } -> HH.HTML w i
    renderBar { amplitude } =
      HH.div
        [ cls [ "lattice-waveform-bar" ]
        , HP.attr (HH.AttrName "style") (waveformBarStyle amplitude)
        ]
        []

renderBeatMarker :: forall w i. Int -> Int -> HH.HTML w i
renderBeatMarker totalFrames onset =
  let
    leftPct = Int.toNumber onset / Int.toNumber totalFrames * 100.0
  in
  HH.div
    [ cls [ "lattice-beat-marker" ]
    , HP.attr (HH.AttrName "style") (beatMarkerStyle leftPct)
    ]
    []

renderPeakMarker :: forall w i. Int -> Int -> HH.HTML w i
renderPeakMarker totalFrames peak =
  let
    leftPct = Int.toNumber peak / Int.toNumber totalFrames * 100.0
  in
  HH.div
    [ cls [ "lattice-peak-marker" ]
    , HP.attr (HH.AttrName "style") (peakMarkerStyle leftPct)
    ]
    [ HH.div 
        [ cls [ "lattice-peak-diamond" ]
        , HP.attr (HH.AttrName "style") peakDiamondStyle
        ]
        []
    ]

renderNoAudio :: forall m. H.ComponentHTML Action () m
renderNoAudio =
  HH.div
    [ cls [ "lattice-no-audio" ]
    , HP.attr (HH.AttrName "style") noAudioStyle
    ]
    [ HH.span [ cls [ "lattice-upload-icon" ] ]
        [ HH.text "📤" ]
    , HH.span_
        [ HH.text "No audio loaded" ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ════════════════════════════════════════════════════════════════════════════

formatTime :: Int -> Int -> String
formatTime frame fps =
  let
    totalSeconds = Int.toNumber frame / Int.toNumber fps
    mins = Int.floor (totalSeconds / 60.0)
    secs = Int.floor (totalSeconds - Int.toNumber mins * 60.0)
    ms = Int.floor ((totalSeconds - Int.toNumber (mins * 60 + secs)) * 100.0)
  in
  show mins <> ":" <> padZero secs <> "." <> padZero ms
  where
    padZero n = if n < 10 then "0" <> show n else show n

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

audioTrackStyle :: Int -> String
audioTrackStyle height =
  "display: flex; " <>
  "height: " <> show height <> "px; " <>
  "background: var(--lattice-surface-1, #1e1e1e); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #333);"

headerStyle :: String
headerStyle =
  "width: 150px; " <>
  "flex-shrink: 0; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 8px; " <>
  "padding: 0 12px; " <>
  "background: var(--lattice-surface-2, #252525); " <>
  "border-right: 1px solid var(--lattice-border-subtle, #333); " <>
  "font-size: 12px;"

bpmBadgeStyle :: String
bpmBadgeStyle =
  "margin-left: auto; " <>
  "padding: 2px 6px; " <>
  "background: var(--lattice-accent, #4a90d9); " <>
  "color: white; " <>
  "border-radius: 3px; " <>
  "font-size: 12px; " <>
  "font-weight: 500;"

waveformContainerStyle :: String
waveformContainerStyle =
  "flex: 1; " <>
  "position: relative; " <>
  "overflow: hidden;"

waveformCanvasStyle :: String
waveformCanvasStyle =
  "width: 100%; " <>
  "height: 100%; " <>
  "cursor: pointer; " <>
  "background: var(--lattice-surface-1, #1e1e1e);"

waveformBarsStyle :: String
waveformBarsStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "justify-content: space-around; " <>
  "height: 100%; " <>
  "padding: 0 4px;"

waveformBarStyle :: Number -> String
waveformBarStyle amplitude =
  let
    heightPct = amplitude * 80.0 + 10.0  -- 10-90% height range
  in
  "width: 2px; " <>
  "height: " <> show heightPct <> "%; " <>
  "background: var(--lattice-accent-muted, #3d5a80); " <>
  "border-radius: 1px;"

audioPlayheadStyle :: Number -> String
audioPlayheadStyle leftPct =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "left: " <> show leftPct <> "%; " <>
  "width: 2px; " <>
  "background: var(--lattice-error, #ff6b6b); " <>
  "pointer-events: none; " <>
  "z-index: 10;"

hoverIndicatorStyle :: Number -> String
hoverIndicatorStyle leftPct =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "left: " <> show leftPct <> "%; " <>
  "width: 1px; " <>
  "background: rgba(255, 255, 255, 0.3); " <>
  "pointer-events: none; " <>
  "z-index: 5;"

hoverTooltipStyle :: String
hoverTooltipStyle =
  "position: absolute; " <>
  "bottom: 100%; " <>
  "left: 50%; " <>
  "transform: translateX(-50%); " <>
  "padding: 4px 8px; " <>
  "background: var(--lattice-surface-4, #333); " <>
  "border: 1px solid var(--lattice-border-subtle, #444); " <>
  "border-radius: 4px; " <>
  "font-size: 12px; " <>
  "color: white; " <>
  "white-space: nowrap; " <>
  "pointer-events: none; " <>
  "z-index: 20;"

beatMarkerStyle :: Number -> String
beatMarkerStyle leftPct =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "left: " <> show leftPct <> "%; " <>
  "width: 1px; " <>
  "background: rgba(255, 193, 7, 0.5); " <>
  "pointer-events: none; " <>
  "z-index: 3;"

peakMarkerStyle :: Number -> String
peakMarkerStyle leftPct =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "left: " <> show leftPct <> "%; " <>
  "width: 2px; " <>
  "background: rgba(255, 107, 107, 0.6); " <>
  "pointer-events: none; " <>
  "z-index: 4;"

peakDiamondStyle :: String
peakDiamondStyle =
  "position: absolute; " <>
  "top: 2px; " <>
  "left: 50%; " <>
  "transform: translateX(-50%) rotate(45deg); " <>
  "width: 6px; " <>
  "height: 6px; " <>
  "background: var(--lattice-error, #ff6b6b); " <>
  "border: 1px solid white; " <>
  "box-shadow: 0 0 4px rgba(255, 107, 107, 0.8);"

noAudioStyle :: String
noAudioStyle =
  "flex: 1; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "justify-content: center; " <>
  "gap: 8px; " <>
  "color: var(--lattice-text-muted, #666); " <>
  "font-size: 12px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ _
      { hasAudio = input.hasAudio
      , analysis = input.analysis
      , peakData = input.peakData
      , currentFrame = input.currentFrame
      , totalFrames = input.totalFrames
      , fps = input.fps
      , height = input.height
      }
  
  HandleClick frame -> do
    H.raise (Seek frame)
  
  HandleMouseMove frame -> do
    H.modify_ _ { hoverFrame = Just frame }
  
  HandleMouseLeave -> do
    H.modify_ _ { hoverFrame = Nothing }
