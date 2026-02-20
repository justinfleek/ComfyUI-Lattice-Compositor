-- | Preview Panel Component
-- |
-- | Playback controls and preview settings for composition preview.
-- | Supports:
-- | - Transport controls (play, pause, step, go to start/end)
-- | - Loop playback and speed control
-- | - Frame range settings for render range
-- | - Particle cache controls
-- | - Preview quality settings
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/PreviewPanel.vue
module Lattice.UI.Components.PreviewPanel
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  , PlaybackSpeed(..)
  , PreviewResolution(..)
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
import Web.UIEvent.KeyboardEvent as KE

import Lattice.UI.Core (cls)
import Lattice.UI.Utils as Utils

-- =============================================================================
--                                                                      // types
-- =============================================================================

type Input =
  { currentFrame :: Int
  , fps :: Int
  , frameCount :: Int
  , isPlaying :: Boolean
  , particleLayers :: Array ParticleLayerInfo
  }

data Output
  = TogglePlayback
  | GoToStart
  | GoToEnd
  | StepForward
  | StepBackward
  | SetFrame Int
  | SetLoopPlayback Boolean
  | SetPlaybackSpeed PlaybackSpeed
  | SetRenderRange Int Int
  | CacheRenderRange
  | ClearAllCaches
  | SetPreviewResolution PreviewResolution
  | SetAdaptiveQuality Boolean

data Query a
  = UpdateCacheStats (Array CacheStats) a
  | SetCaching Boolean Int Int a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                           // preview // types
-- =============================================================================

data PlaybackSpeed
  = Speed025x
  | Speed05x
  | Speed1x
  | Speed2x
  | Speed4x

derive instance eqPlaybackSpeed :: Eq PlaybackSpeed

instance showPlaybackSpeed :: Show PlaybackSpeed where
  show = case _ of
    Speed025x -> "0.25"
    Speed05x -> "0.5"
    Speed1x -> "1"
    Speed2x -> "2"
    Speed4x -> "4"

speedLabel :: PlaybackSpeed -> String
speedLabel = case _ of
  Speed025x -> "0.25x"
  Speed05x -> "0.5x"
  Speed1x -> "1x"
  Speed2x -> "2x"
  Speed4x -> "4x"

speedValue :: PlaybackSpeed -> Number
speedValue = case _ of
  Speed025x -> 0.25
  Speed05x -> 0.5
  Speed1x -> 1.0
  Speed2x -> 2.0
  Speed4x -> 4.0

data PreviewResolution
  = ResFull
  | ResHalf
  | ResQuarter
  | ResEighth

derive instance eqPreviewResolution :: Eq PreviewResolution

instance showPreviewResolution :: Show PreviewResolution where
  show = case _ of
    ResFull -> "1"
    ResHalf -> "0.5"
    ResQuarter -> "0.25"
    ResEighth -> "0.125"

resolutionLabel :: PreviewResolution -> String
resolutionLabel = case _ of
  ResFull -> "Full (100%)"
  ResHalf -> "Half (50%)"
  ResQuarter -> "Quarter (25%)"
  ResEighth -> "Eighth (12.5%)"

type ParticleLayerInfo =
  { id :: String
  , name :: String
  }

type CacheStats =
  { layerId :: String
  , cachedFrames :: Int
  }

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { input :: Input
  , baseId :: String
  , loopPlayback :: Boolean
  , playbackSpeed :: PlaybackSpeed
  , renderRangeStart :: Int
  , renderRangeEnd :: Int
  , isCaching :: Boolean
  , cacheProgress :: Int
  , currentCachingFrame :: Int
  , totalFramesToCache :: Int
  , previewResolution :: PreviewResolution
  , adaptiveQuality :: Boolean
  , cacheStats :: Array CacheStats
  }

data Action
  = Initialize
  | Receive Input
  | TogglePlaybackAction
  | GoToStartAction
  | GoToEndAction
  | StepForwardAction
  | StepBackwardAction
  | SetLoopAction Boolean
  | SetSpeedAction String
  | SetRangeStartAction String
  | SetRangeEndAction String
  | CacheAction
  | ClearCacheAction
  | SetResolutionAction String
  | SetAdaptiveAction Boolean
  | HandleKeyDown KE.KeyboardEvent

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
  , baseId: "preview-panel"
  , loopPlayback: true
  , playbackSpeed: Speed1x
  , renderRangeStart: 0
  , renderRangeEnd: min 81 input.frameCount
  , isCaching: false
  , cacheProgress: 0
  , currentCachingFrame: 0
  , totalFramesToCache: 0
  , previewResolution: ResFull
  , adaptiveQuality: true
  , cacheStats: []
  }

-- =============================================================================
--                                                                     // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "preview-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , ARIA.label "Preview Controls"
    ]
    [ renderHeader
    , renderContent state
    ]

renderHeader :: forall m. H.ComponentHTML Action Slots m
renderHeader =
  HH.div
    [ cls [ "panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.span
        [ cls [ "panel-title" ]
        , HP.attr (HH.AttrName "style") titleStyle
        ]
        [ HH.text "Preview" ]
    ]

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "panel-content" ]
    , HP.attr (HH.AttrName "style") contentStyle
    ]
    [ renderPlaybackSection state
    , renderRangeSection state
    , renderCacheSection state
    , renderQualitySection state
    ]

-- =============================================================================
--                                                       // playback // section
-- =============================================================================

renderPlaybackSection :: forall m. State -> H.ComponentHTML Action Slots m
renderPlaybackSection state =
  HH.div
    [ cls [ "playback-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ renderTransportControls state
    , renderPlaybackOptions state
    ]

renderTransportControls :: forall m. State -> H.ComponentHTML Action Slots m
renderTransportControls state =
  HH.div
    [ cls [ "control-row" ]
    , HP.attr (HH.AttrName "style") transportRowStyle
    , HP.attr (HH.AttrName "role") "group"
    , ARIA.label "Transport Controls"
    ]
    [ transportBtn "\x{23EE}" "Go to Start (Home)" GoToStartAction false
    , transportBtn "\x{25C0}" "Step Backward (,)" StepBackwardAction false
    , transportBtn 
        (if state.input.isPlaying then "\x{23F8}" else "\x{25B6}") 
        "Play/Pause (Space)" 
        TogglePlaybackAction 
        state.input.isPlaying
    , transportBtn "\x{25B6}" "Step Forward (.)" StepForwardAction false
    , transportBtn "\x{23ED}" "Go to End (End)" GoToEndAction false
    ]

transportBtn :: forall m. String -> String -> Action -> Boolean -> H.ComponentHTML Action Slots m
transportBtn icon tooltip action isActive =
  HH.button
    [ cls [ "transport-btn" ]
    , HP.type_ HP.ButtonButton
    , HP.title tooltip
    , HP.attr (HH.AttrName "style") (transportBtnStyle isActive)
    , HP.attr (HH.AttrName "data-state") (if isActive then "active" else "inactive")
    , HE.onClick \_ -> action
    ]
    [ HH.text icon ]

renderPlaybackOptions :: forall m. State -> H.ComponentHTML Action Slots m
renderPlaybackOptions state =
  HH.div
    [ cls [ "control-row" ]
    , HP.attr (HH.AttrName "style") optionsRowStyle
    ]
    [ HH.label
        [ cls [ "checkbox-label" ]
        , HP.attr (HH.AttrName "style") checkboxLabelStyle
        ]
        [ HH.input
            [ HP.type_ HP.InputCheckbox
            , HP.checked state.loopPlayback
            , HE.onChecked SetLoopAction
            ]
        , HH.text " Loop"
        ]
    , HH.select
        [ cls [ "speed-select" ]
        , HP.attr (HH.AttrName "style") speedSelectStyle
        , HE.onValueChange SetSpeedAction
        ]
        [ HH.option [ HP.value "0.25", HP.selected (state.playbackSpeed == Speed025x) ] [ HH.text "0.25x" ]
        , HH.option [ HP.value "0.5", HP.selected (state.playbackSpeed == Speed05x) ] [ HH.text "0.5x" ]
        , HH.option [ HP.value "1", HP.selected (state.playbackSpeed == Speed1x) ] [ HH.text "1x" ]
        , HH.option [ HP.value "2", HP.selected (state.playbackSpeed == Speed2x) ] [ HH.text "2x" ]
        , HH.option [ HP.value "4", HP.selected (state.playbackSpeed == Speed4x) ] [ HH.text "4x" ]
        ]
    ]

-- =============================================================================
--                                                          // range // section
-- =============================================================================

renderRangeSection :: forall m. State -> H.ComponentHTML Action Slots m
renderRangeSection state =
  HH.div
    [ cls [ "range-section" ]
    , HP.attr (HH.AttrName "style") rangeSectionStyle
    ]
    [ HH.div
        [ cls [ "range-row" ]
        , HP.attr (HH.AttrName "style") rangeRowStyle
        ]
        [ HH.label_ [ HH.text "Render Range: " ]
        , HH.input
            [ HP.type_ HP.InputNumber
            , HP.value (show state.renderRangeStart)
            , HP.attr (HH.AttrName "min") "0"
            , HP.attr (HH.AttrName "max") (show (state.input.frameCount - 1))
            , cls [ "frame-input" ]
            , HP.attr (HH.AttrName "style") frameInputStyle
            , HE.onValueInput SetRangeStartAction
            ]
        , HH.span_ [ HH.text " - " ]
        , HH.input
            [ HP.type_ HP.InputNumber
            , HP.value (show state.renderRangeEnd)
            , HP.attr (HH.AttrName "min") (show state.renderRangeStart)
            , HP.attr (HH.AttrName "max") (show state.input.frameCount)
            , cls [ "frame-input" ]
            , HP.attr (HH.AttrName "style") frameInputStyle
            , HE.onValueInput SetRangeEndAction
            ]
        ]
    , HH.div
        [ cls [ "frame-info" ]
        , HP.attr (HH.AttrName "style") frameInfoStyle
        ]
        [ HH.text (formatFrameInfo state.input.currentFrame state.input.frameCount state.input.fps) ]
    ]

formatFrameInfo :: Int -> Int -> Int -> String
formatFrameInfo current total fps =
  let
    seconds = toNumber current / toNumber fps
    minutes = floor (seconds / 60.0)
    secs = seconds - (toNumber minutes * 60.0)
    timeStr = show minutes <> ":" <> padZeros (formatNum secs) 5
  in
    "Frame " <> show current <> " / " <> show total <> " (" <> timeStr <> ")"

formatNum :: Number -> String
formatNum :: Number -> String
formatNum = Utils.formatFixed 2

padZeros :: String -> Int -> String
padZeros s len = Utils.padStart len '0' s

toNumber :: Int -> Number
toNumber = Utils.toNumber

floor :: Number -> Int
floor = Utils.floor

-- =============================================================================
--                                                          // cache // section
-- =============================================================================

renderCacheSection :: forall m. State -> H.ComponentHTML Action Slots m
renderCacheSection state =
  HH.div
    [ cls [ "cache-section" ]
    , HP.attr (HH.AttrName "style") cacheSectionStyle
    ]
    [ HH.div
        [ cls [ "section-header" ]
        , HP.attr (HH.AttrName "style") sectionHeaderStyle
        ]
        [ HH.text "Particle Cache" ]
    , if Array.null state.input.particleLayers
        then HH.div
              [ cls [ "no-particles" ]
              , HP.attr (HH.AttrName "style") noParticlesStyle
              ]
              [ HH.text "No particle layers in composition" ]
        else renderCacheControls state
    ]

renderCacheControls :: forall m. State -> H.ComponentHTML Action Slots m
renderCacheControls state =
  HH.div_
    [ HH.div
        [ cls [ "cache-controls" ]
        , HP.attr (HH.AttrName "style") cacheControlsStyle
        ]
        [ HH.button
            [ cls [ "cache-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.disabled state.isCaching
            , HP.title "Pre-cache particle frames for smooth playback"
            , HP.attr (HH.AttrName "style") cacheBtnStyle
            , HE.onClick \_ -> CacheAction
            ]
            [ HH.text (if state.isCaching then "Caching..." else "Cache Render Range") ]
        , HH.button
            [ cls [ "cache-btn", "secondary" ]
            , HP.type_ HP.ButtonButton
            , HP.disabled state.isCaching
            , HP.title "Clear all cached particle frames"
            , HP.attr (HH.AttrName "style") cacheBtnSecondaryStyle
            , HE.onClick \_ -> ClearCacheAction
            ]
            [ HH.text "Clear Cache" ]
        ]
    , if state.isCaching
        then renderCacheProgress state
        else HH.text ""
    , renderCacheStats state
    ]

renderCacheProgress :: forall m. State -> H.ComponentHTML Action Slots m
renderCacheProgress state =
  HH.div
    [ cls [ "progress-container" ]
    , HP.attr (HH.AttrName "style") progressContainerStyle
    , HP.attr (HH.AttrName "role") "progressbar"
    , ARIA.valueNow (show state.cacheProgress)
    , ARIA.valueMin "0"
    , ARIA.valueMax "100"
    ]
    [ HH.div
        [ cls [ "progress-bar" ]
        , HP.attr (HH.AttrName "style") progressBarStyle
        ]
        [ HH.div
            [ cls [ "progress-fill" ]
            , HP.attr (HH.AttrName "style") (progressFillStyle state.cacheProgress)
            ]
            []
        ]
    , HH.span
        [ cls [ "progress-text" ]
        , HP.attr (HH.AttrName "style") progressTextStyle
        ]
        [ HH.text (show state.currentCachingFrame <> " / " <> show state.totalFramesToCache) ]
    ]

renderCacheStats :: forall m. State -> H.ComponentHTML Action Slots m
renderCacheStats state =
  HH.div
    [ cls [ "cache-stats" ]
    , HP.attr (HH.AttrName "style") cacheStatsStyle
    ]
    (map (renderLayerCacheInfo state) state.input.particleLayers)

renderLayerCacheInfo :: forall m. State -> ParticleLayerInfo -> H.ComponentHTML Action Slots m
renderLayerCacheInfo state layer =
  let
    cachedFrames = getCacheCount state.cacheStats layer.id
  in
  HH.div
    [ cls [ "layer-cache-info" ]
    , HP.attr (HH.AttrName "style") layerCacheInfoStyle
    ]
    [ HH.span [ cls [ "layer-name" ], HP.attr (HH.AttrName "style") layerNameStyle ] [ HH.text layer.name ]
    , HH.span [ cls [ "cache-count" ], HP.attr (HH.AttrName "style") cacheCountStyle ] [ HH.text (show cachedFrames <> " frames cached") ]
    ]

getCacheCount :: Array CacheStats -> String -> Int
getCacheCount stats layerId =
  case Array.find (\s -> s.layerId == layerId) stats of
    Just s -> s.cachedFrames
    Nothing -> 0

-- =============================================================================
--                                                        // quality // section
-- =============================================================================

renderQualitySection :: forall m. State -> H.ComponentHTML Action Slots m
renderQualitySection state =
  HH.div
    [ cls [ "quality-section" ]
    , HP.attr (HH.AttrName "style") qualitySectionStyle
    ]
    [ HH.div
        [ cls [ "section-header" ]
        , HP.attr (HH.AttrName "style") sectionHeaderStyle
        ]
        [ HH.text "Preview Quality" ]
    , HH.div
        [ cls [ "quality-row" ]
        , HP.attr (HH.AttrName "style") qualityRowStyle
        ]
        [ HH.label_ [ HH.text "Resolution:" ]
        , HH.select
            [ cls [ "quality-select" ]
            , HP.attr (HH.AttrName "style") qualitySelectStyle
            , HE.onValueChange SetResolutionAction
            ]
            [ HH.option [ HP.value "1", HP.selected (state.previewResolution == ResFull) ] [ HH.text "Full (100%)" ]
            , HH.option [ HP.value "0.5", HP.selected (state.previewResolution == ResHalf) ] [ HH.text "Half (50%)" ]
            , HH.option [ HP.value "0.25", HP.selected (state.previewResolution == ResQuarter) ] [ HH.text "Quarter (25%)" ]
            , HH.option [ HP.value "0.125", HP.selected (state.previewResolution == ResEighth) ] [ HH.text "Eighth (12.5%)" ]
            ]
        ]
    , HH.div
        [ cls [ "quality-row" ]
        , HP.attr (HH.AttrName "style") qualityRowStyle
        ]
        [ HH.label
            [ cls [ "checkbox-label" ]
            , HP.attr (HH.AttrName "style") checkboxLabelStyle
            ]
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.adaptiveQuality
                , HE.onChecked SetAdaptiveAction
                ]
            , HH.text " Adaptive (reduce during playback)"
            ]
        ]
    ]

-- =============================================================================
--                                                                     // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--surface-ground); color: var(--text-color);"

headerStyle :: String
headerStyle =
  "display: flex; align-items: center; justify-content: space-between; " <>
  "padding: 8px 12px; background: var(--surface-section); " <>
  "border-bottom: 1px solid var(--surface-border);"

titleStyle :: String
titleStyle =
  "font-weight: 600; font-size: 13px;"

contentStyle :: String
contentStyle =
  "flex: 1; overflow-y: auto; padding: 12px; display: flex; " <>
  "flex-direction: column; gap: 16px;"

sectionStyle :: String
sectionStyle =
  "display: flex; flex-direction: column; gap: 8px;"

transportRowStyle :: String
transportRowStyle =
  "display: flex; align-items: center; justify-content: center; gap: 4px;"

transportBtnStyle :: Boolean -> String
transportBtnStyle isActive =
  let
    baseStyle = "width: 32px; height: 32px; " <>
                "border: 1px solid var(--surface-border); " <>
                "border-radius: 4px; cursor: pointer; font-size: 14px; " <>
                "display: flex; align-items: center; justify-content: center; " <>
                "transition: all 0.15s;"
    activeStyle = if isActive
      then "background: var(--primary-color); color: white; border-color: var(--primary-color);"
      else "background: var(--surface-card);"
  in
    baseStyle <> activeStyle

optionsRowStyle :: String
optionsRowStyle =
  "display: flex; align-items: center; justify-content: center; gap: 16px;"

checkboxLabelStyle :: String
checkboxLabelStyle =
  "display: flex; align-items: center; gap: 6px; cursor: pointer; font-size: 12px;"

speedSelectStyle :: String
speedSelectStyle =
  "padding: 4px 8px; border: 1px solid var(--surface-border); " <>
  "background: var(--surface-card); border-radius: 4px; " <>
  "color: var(--text-color); font-size: 12px;"

rangeSectionStyle :: String
rangeSectionStyle =
  "display: flex; flex-direction: column; gap: 6px; padding: 8px; " <>
  "background: var(--surface-card); border-radius: 4px;"

rangeRowStyle :: String
rangeRowStyle =
  "display: flex; align-items: center; gap: 8px; font-size: 12px;"

frameInputStyle :: String
frameInputStyle =
  "width: 60px; padding: 4px 6px; " <>
  "border: 1px solid var(--surface-border); " <>
  "background: var(--surface-ground); border-radius: 3px; " <>
  "color: var(--text-color); font-size: 12px;"

frameInfoStyle :: String
frameInfoStyle =
  "font-size: 11px; color: var(--text-color-secondary); text-align: center;"

cacheSectionStyle :: String
cacheSectionStyle =
  "display: flex; flex-direction: column; gap: 8px; padding: 8px; " <>
  "background: var(--surface-card); border-radius: 4px;"

sectionHeaderStyle :: String
sectionHeaderStyle =
  "font-weight: 600; font-size: 12px; color: var(--text-color-secondary); " <>
  "text-transform: uppercase; letter-spacing: 0.5px;"

noParticlesStyle :: String
noParticlesStyle =
  "font-size: 12px; color: var(--text-color-secondary); " <>
  "font-style: italic; text-align: center; padding: 8px;"

cacheControlsStyle :: String
cacheControlsStyle =
  "display: flex; gap: 8px;"

cacheBtnStyle :: String
cacheBtnStyle =
  "flex: 1; padding: 8px 12px; " <>
  "border: 1px solid var(--surface-border); " <>
  "background: var(--primary-color); color: white; " <>
  "border-radius: 4px; cursor: pointer; font-size: 12px; font-weight: 500;"

cacheBtnSecondaryStyle :: String
cacheBtnSecondaryStyle =
  "flex: 1; padding: 8px 12px; " <>
  "border: 1px solid var(--surface-border); " <>
  "background: var(--surface-ground); color: var(--text-color); " <>
  "border-radius: 4px; cursor: pointer; font-size: 12px; font-weight: 500;"

progressContainerStyle :: String
progressContainerStyle =
  "display: flex; align-items: center; gap: 8px;"

progressBarStyle :: String
progressBarStyle =
  "flex: 1; height: 6px; background: var(--surface-ground); " <>
  "border-radius: 3px; overflow: hidden;"

progressFillStyle :: Int -> String
progressFillStyle percentage =
  "height: 100%; background: var(--primary-color); " <>
  "transition: width 0.1s linear; width: " <> show percentage <> "%;"

progressTextStyle :: String
progressTextStyle =
  "font-size: 11px; color: var(--text-color-secondary); " <>
  "min-width: 60px; text-align: right;"

cacheStatsStyle :: String
cacheStatsStyle =
  "display: flex; flex-direction: column; gap: 4px; margin-top: 4px;"

layerCacheInfoStyle :: String
layerCacheInfoStyle =
  "display: flex; justify-content: space-between; font-size: 11px; " <>
  "color: var(--text-color-secondary);"

layerNameStyle :: String
layerNameStyle =
  "font-weight: 500;"

cacheCountStyle :: String
cacheCountStyle =
  "color: var(--primary-color);"

qualitySectionStyle :: String
qualitySectionStyle =
  "display: flex; flex-direction: column; gap: 8px; padding: 8px; " <>
  "background: var(--surface-card); border-radius: 4px;"

qualityRowStyle :: String
qualityRowStyle =
  "display: flex; align-items: center; gap: 8px; font-size: 12px;"

qualitySelectStyle :: String
qualitySelectStyle =
  "flex: 1; padding: 4px 8px; " <>
  "border: 1px solid var(--surface-border); " <>
  "background: var(--surface-ground); border-radius: 4px; " <>
  "color: var(--text-color); font-size: 12px;"

-- =============================================================================
--                                                                    // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input -> do
    H.modify_ \s -> s 
      { input = input
      , renderRangeEnd = min s.renderRangeEnd input.frameCount
      }

  TogglePlaybackAction -> H.raise TogglePlayback
  GoToStartAction -> H.raise GoToStart
  GoToEndAction -> H.raise GoToEnd
  StepForwardAction -> H.raise StepForward
  StepBackwardAction -> H.raise StepBackward

  SetLoopAction checked -> do
    H.modify_ _ { loopPlayback = checked }
    H.raise (SetLoopPlayback checked)

  SetSpeedAction val -> do
    let speed = parseSpeed val
    H.modify_ _ { playbackSpeed = speed }
    H.raise (SetPlaybackSpeed speed)

  SetRangeStartAction val -> do
    let start = parseIntSafe val 0
    H.modify_ _ { renderRangeStart = start }
    state <- H.get
    H.raise (SetRenderRange start state.renderRangeEnd)

  SetRangeEndAction val -> do
    state <- H.get
    let end = parseIntSafe val state.input.frameCount
    H.modify_ _ { renderRangeEnd = end }
    H.raise (SetRenderRange state.renderRangeStart end)

  CacheAction -> do
    state <- H.get
    H.modify_ _ 
      { isCaching = true
      , cacheProgress = 0
      , currentCachingFrame = 0
      , totalFramesToCache = state.renderRangeEnd - state.renderRangeStart
      }
    H.raise CacheRenderRange

  ClearCacheAction -> do
    H.raise ClearAllCaches

  SetResolutionAction val -> do
    let res = parseResolution val
    H.modify_ _ { previewResolution = res }
    H.raise (SetPreviewResolution res)

  SetAdaptiveAction checked -> do
    H.modify_ _ { adaptiveQuality = checked }
    H.raise (SetAdaptiveQuality checked)

  HandleKeyDown event -> do
    let key = KE.key event
    case key of
      " " -> H.raise TogglePlayback
      "Home" -> H.raise GoToStart
      "End" -> H.raise GoToEnd
      "." -> H.raise StepForward
      "," -> H.raise StepBackward
      _ -> pure unit

parseSpeed :: String -> PlaybackSpeed
parseSpeed = case _ of
  "0.25" -> Speed025x
  "0.5" -> Speed05x
  "2" -> Speed2x
  "4" -> Speed4x
  _ -> Speed1x

parseResolution :: String -> PreviewResolution
parseResolution = case _ of
  "0.5" -> ResHalf
  "0.25" -> ResQuarter
  "0.125" -> ResEighth
  _ -> ResFull

parseIntSafe :: String -> Int -> Int
parseIntSafe str defaultVal = Utils.parseIntOr defaultVal str

-- =============================================================================
--                                                                    // queries
-- =============================================================================

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  UpdateCacheStats stats next -> do
    H.modify_ _ { cacheStats = stats }
    pure (Just next)

  SetCaching isCaching current total next -> do
    let progress = if total > 0 then (current * 100) / total else 0
    H.modify_ _ 
      { isCaching = isCaching
      , currentCachingFrame = current
      , totalFramesToCache = total
      , cacheProgress = progress
      }
    pure (Just next)
