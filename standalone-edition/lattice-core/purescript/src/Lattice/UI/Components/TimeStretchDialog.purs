-- | Time Stretch Dialog
-- |
-- | Dialog for time stretch operations on video/nested comp layers.
-- | Provides Stretch Factor percentage control and Hold In Place pivot options.
-- |
-- | Features:
-- | - Stretch Factor percentage (100% = normal, 200% = half speed, 50% = double speed)
-- | - Hold In Place options: Layer In-point, Current Frame, Layer Out-point
-- | - Preview of new duration
-- | - Reverse playback option
-- | - Keyboard shortcut: Ctrl+Shift+Alt+R
-- |
-- | System F/Omega: TimeStretch = Factor × HoldPoint × Reverse → LayerTransform
module Lattice.UI.Components.TimeStretchDialog
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  , HoldInPlace(..)
  , TimeStretchResult
  ) where

import Prelude

import Data.Int (round, toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (fromString)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.KeyboardEvent as KE

import Lattice.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                    // types
-- ═══════════════════════════════════════════════════════════════════════════

data HoldInPlace
  = HoldInPoint
  | HoldCurrentFrame
  | HoldOutPoint

derive instance eqHoldInPlace :: Eq HoldInPlace

type SpeedPreset =
  { label :: String
  , value :: Int  -- Stretch factor percentage
  }

type TimeStretchResult =
  { stretchFactor :: Int
  , holdInPlace :: HoldInPlace
  , reverse :: Boolean
  , speed :: Number  -- Effective speed multiplier
  }

type Input =
  { visible :: Boolean
  , layerId :: String
  , originalDuration :: Number  -- In seconds
  , currentStretchFactor :: Int
  , fps :: Int
  }

data Output
  = Applied TimeStretchResult
  | Cancelled

data Query a
  = Close a
  | Open a

type Slot id = H.Slot Query Output id

type State =
  { visible :: Boolean
  , layerId :: String
  , originalDuration :: Number
  , currentStretchFactor :: Int
  , fps :: Int
  , stretchFactor :: Int
  , holdInPlace :: HoldInPlace
  , reversePlayback :: Boolean
  , stretchInput :: String
  }

data Action
  = Initialize
  | Receive Input
  | HandleKeyDown KeyboardEvent
  | UpdateStretchFactor String
  | SelectPreset Int
  | SetHoldInPlace HoldInPlace
  | ToggleReverse Boolean
  | Reset
  | Apply
  | Cancel

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // speed // presets
-- ═══════════════════════════════════════════════════════════════════════════

speedPresets :: Array SpeedPreset
speedPresets =
  [ { label: "25%", value: 400 }   -- Quarter speed (4x duration)
  , { label: "50%", value: 200 }   -- Half speed (2x duration)
  , { label: "100%", value: 100 }  -- Normal speed
  , { label: "200%", value: 50 }   -- Double speed (0.5x duration)
  , { label: "400%", value: 25 }   -- 4x speed (0.25x duration)
  ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                // component
-- ═══════════════════════════════════════════════════════════════════════════

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
  { visible: input.visible
  , layerId: input.layerId
  , originalDuration: input.originalDuration
  , currentStretchFactor: input.currentStretchFactor
  , fps: input.fps
  , stretchFactor: input.currentStretchFactor
  , holdInPlace: HoldInPoint
  , reversePlayback: false
  , stretchInput: show input.currentStretchFactor
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                   // render
-- ═══════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state
  | not state.visible = HH.text ""
  | otherwise =
      HH.div
        [ cls [ "lattice-timestretch-overlay" ]
        , HP.attr (HH.AttrName "style") overlayStyle
        , ARIA.role "dialog"
        , ARIA.modal "true"
        , ARIA.labelledBy "timestretch-title"
        , HE.onKeyDown HandleKeyDown
        , HP.tabIndex 0
        ]
        [ HH.div
            [ cls [ "lattice-timestretch-container" ]
            , HP.attr (HH.AttrName "style") containerStyle
            ]
            [ renderHeader
            , renderBody state
            , renderFooter
            ]
        ]

renderHeader :: forall m. H.ComponentHTML Action () m
renderHeader =
  HH.div
    [ cls [ "dialog-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.h2
        [ HP.id "timestretch-title"
        , HP.attr (HH.AttrName "style") titleStyle
        ]
        [ HH.text "Time Stretch" ]
    , HH.button
        [ cls [ "close-btn" ]
        , HP.attr (HH.AttrName "style") closeButtonStyle
        , HP.title "Close"
        , ARIA.label "Close"
        , HE.onClick \_ -> Cancel
        ]
        [ HH.text "×" ]
    ]

renderBody :: forall m. State -> H.ComponentHTML Action () m
renderBody state =
  HH.div
    [ cls [ "dialog-body" ]
    , HP.attr (HH.AttrName "style") bodyStyle
    ]
    [ -- Original info section
      HH.div
        [ cls [ "info-section" ]
        , HP.attr (HH.AttrName "style") infoSectionStyle
        ]
        [ renderInfoRow "Original Duration:" (formatDuration state.originalDuration state.fps)
        , renderInfoRow "Original Speed:" (formatPercent (100.0 / toNumber state.currentStretchFactor * 100.0) <> "%")
        ]
    
    -- Stretch factor control
    , HH.div
        [ cls [ "control-section" ]
        , HP.attr (HH.AttrName "style") controlSectionStyle
        ]
        [ HH.div
            [ cls [ "control-row" ]
            , HP.attr (HH.AttrName "style") controlRowStyle
            ]
            [ HH.label
                [ HP.for "stretch-factor"
                , HP.attr (HH.AttrName "style") labelStyle
                ]
                [ HH.text "Stretch Factor:" ]
            , HH.div
                [ cls [ "input-group" ]
                , HP.attr (HH.AttrName "style") inputGroupStyle
                ]
                [ HH.input
                    [ HP.id "stretch-factor"
                    , HP.type_ HP.InputNumber
                    , HP.value state.stretchInput
                    , HP.attr (HH.AttrName "min") "10"
                    , HP.attr (HH.AttrName "max") "1000"
                    , HP.attr (HH.AttrName "style") stretchInputStyle
                    , HE.onValueInput UpdateStretchFactor
                    ]
                , HH.span
                    [ cls [ "unit" ]
                    , HP.attr (HH.AttrName "style") unitStyle
                    ]
                    [ HH.text "%" ]
                ]
            ]
        , HH.p
            [ cls [ "hint" ]
            , HP.attr (HH.AttrName "style") hintStyle
            ]
            [ HH.text "100% = normal, 200% = half speed, 50% = double speed" ]
        
        -- Speed presets
        , HH.div
            [ cls [ "presets" ]
            , HP.attr (HH.AttrName "style") presetsStyle
            ]
            (map (renderPreset state) speedPresets)
        ]
    
    -- Hold in place control
    , HH.div
        [ cls [ "control-section" ]
        , HP.attr (HH.AttrName "style") controlSectionStyle
        ]
        [ HH.div
            [ cls [ "control-row" ]
            , HP.attr (HH.AttrName "style") controlRowStyle
            ]
            [ HH.label
                [ HP.for "hold-in-place"
                , HP.attr (HH.AttrName "style") labelStyle
                ]
                [ HH.text "Hold In Place:" ]
            , HH.select
                [ HP.id "hold-in-place"
                , HP.attr (HH.AttrName "style") selectStyle
                , HE.onValueChange \v -> SetHoldInPlace (parseHoldInPlace v)
                ]
                [ HH.option
                    [ HP.value "in-point"
                    , HP.selected (state.holdInPlace == HoldInPoint)
                    ]
                    [ HH.text "Layer In-point" ]
                , HH.option
                    [ HP.value "current-frame"
                    , HP.selected (state.holdInPlace == HoldCurrentFrame)
                    ]
                    [ HH.text "Current Frame" ]
                , HH.option
                    [ HP.value "out-point"
                    , HP.selected (state.holdInPlace == HoldOutPoint)
                    ]
                    [ HH.text "Layer Out-point" ]
                ]
            ]
        , HH.p
            [ cls [ "hint" ]
            , HP.attr (HH.AttrName "style") hintStyle
            ]
            [ HH.text "The layer will stretch from this anchor point." ]
        ]
    
    -- Preview section
    , HH.div
        [ cls [ "preview-section" ]
        , HP.attr (HH.AttrName "style") previewSectionStyle
        ]
        [ renderHighlightRow "New Duration:" (formatDuration newDuration state.fps)
        , renderHighlightRow "Effective Speed:" (formatPercent effectiveSpeed <> "%")
        ]
    
    -- Reverse option
    , HH.div
        [ cls [ "control-section" ]
        , HP.attr (HH.AttrName "style") controlSectionStyle
        ]
        [ HH.label
            [ cls [ "checkbox-row" ]
            , HP.attr (HH.AttrName "style") checkboxRowStyle
            ]
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.reversePlayback
                , HE.onChecked ToggleReverse
                , HP.attr (HH.AttrName "style") checkboxStyle
                ]
            , HH.span [] [ HH.text "Reverse Playback" ]
            ]
        ]
    ]
  where
    newDuration = state.originalDuration * (toNumber state.stretchFactor / 100.0)
    effectiveSpeed = 
      let speed = (100.0 / toNumber state.stretchFactor) * 100.0
      in if state.reversePlayback then -speed else speed

renderInfoRow :: forall m. String -> String -> H.ComponentHTML Action () m
renderInfoRow label value =
  HH.div
    [ cls [ "info-row" ]
    , HP.attr (HH.AttrName "style") infoRowStyle
    ]
    [ HH.span
        [ cls [ "info-label" ]
        , HP.attr (HH.AttrName "style") infoLabelStyle
        ]
        [ HH.text label ]
    , HH.span
        [ cls [ "info-value" ]
        , HP.attr (HH.AttrName "style") infoValueStyle
        ]
        [ HH.text value ]
    ]

renderHighlightRow :: forall m. String -> String -> H.ComponentHTML Action () m
renderHighlightRow label value =
  HH.div
    [ cls [ "info-row", "highlight" ]
    , HP.attr (HH.AttrName "style") highlightRowStyle
    ]
    [ HH.span
        [ cls [ "info-label" ]
        , HP.attr (HH.AttrName "style") infoLabelStyle
        ]
        [ HH.text label ]
    , HH.span
        [ cls [ "info-value" ]
        , HP.attr (HH.AttrName "style") infoValueStyle
        ]
        [ HH.text value ]
    ]

renderPreset :: forall m. State -> SpeedPreset -> H.ComponentHTML Action () m
renderPreset state preset =
  HH.button
    [ cls [ "preset-btn" ]
    , HP.attr (HH.AttrName "style") (presetButtonStyle isActive)
    , HE.onClick \_ -> SelectPreset preset.value
    ]
    [ HH.text preset.label ]
  where
    isActive = state.stretchFactor == preset.value

renderFooter :: forall m. H.ComponentHTML Action () m
renderFooter =
  HH.div
    [ cls [ "dialog-footer" ]
    , HP.attr (HH.AttrName "style") footerStyle
    ]
    [ HH.button
        [ cls [ "btn", "btn-secondary" ]
        , HP.attr (HH.AttrName "style") secondaryButtonStyle
        , HE.onClick \_ -> Reset
        ]
        [ HH.text "Reset" ]
    , HH.div
        [ cls [ "spacer" ]
        , HP.attr (HH.AttrName "style") "flex: 1;"
        ]
        []
    , HH.button
        [ cls [ "btn", "btn-secondary" ]
        , HP.attr (HH.AttrName "style") secondaryButtonStyle
        , HE.onClick \_ -> Cancel
        ]
        [ HH.text "Cancel" ]
    , HH.button
        [ cls [ "btn", "btn-primary" ]
        , HP.attr (HH.AttrName "style") primaryButtonStyle
        , HE.onClick \_ -> Apply
        ]
        [ HH.text "Apply" ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ═══════════════════════════════════════════════════════════════════════════

formatDuration :: Number -> Int -> String
formatDuration seconds fps =
  let
    totalSeconds = floor seconds
    mins = totalSeconds / 60
    secs = totalSeconds `mod` 60
    frames = floor ((seconds - toNumber totalSeconds) * toNumber fps)
  in
  padZero mins <> ":" <> padZero secs <> ":" <> padZero frames
  where
    floor :: Number -> Int
    floor n = round n
    
    mod :: Int -> Int -> Int
    mod a b = a - (a / b) * b
    
    padZero :: Int -> String
    padZero n = if n < 10 then "0" <> show n else show n

formatPercent :: Number -> String
formatPercent n = 
  let 
    rounded = toNumber (round (n * 10.0)) / 10.0
  in 
  show rounded

parseHoldInPlace :: String -> HoldInPlace
parseHoldInPlace = case _ of
  "current-frame" -> HoldCurrentFrame
  "out-point" -> HoldOutPoint
  _ -> HoldInPoint

-- ═══════════════════════════════════════════════════════════════════════════
--                                                         // inline // styles
-- ═══════════════════════════════════════════════════════════════════════════

overlayStyle :: String
overlayStyle =
  "position: fixed; inset: 0; " <>
  "background: rgba(0, 0, 0, 0.7); " <>
  "display: flex; align-items: center; justify-content: center; " <>
  "z-index: 10000;"

containerStyle :: String
containerStyle =
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border-default, #333); " <>
  "border-radius: var(--lattice-radius-lg, 8px); " <>
  "box-shadow: 0 8px 32px rgba(0, 0, 0, 0.4); " <>
  "min-width: 380px; max-width: 480px;"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 16px 20px; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);"

titleStyle :: String
titleStyle =
  "margin: 0; font-size: 16px; font-weight: 600; " <>
  "color: var(--lattice-text-primary, #e5e5e5);"

closeButtonStyle :: String
closeButtonStyle =
  "background: none; border: none; " <>
  "color: var(--lattice-text-muted, #6b7280); " <>
  "font-size: 20px; cursor: pointer; " <>
  "padding: 4px 8px; border-radius: 4px;"

bodyStyle :: String
bodyStyle =
  "padding: 20px; display: flex; flex-direction: column; gap: 16px;"

infoSectionStyle :: String
infoSectionStyle =
  "background: var(--lattice-surface-1, #121212); " <>
  "border-radius: 4px; padding: 12px;"

infoRowStyle :: String
infoRowStyle =
  "display: flex; justify-content: space-between; " <>
  "align-items: center; padding: 4px 0;"

infoLabelStyle :: String
infoLabelStyle =
  "color: var(--lattice-text-secondary, #9ca3af); font-size: 13px;"

infoValueStyle :: String
infoValueStyle =
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "font-family: monospace; font-size: 13px;"

controlSectionStyle :: String
controlSectionStyle =
  "display: flex; flex-direction: column; gap: 8px;"

controlRowStyle :: String
controlRowStyle =
  "display: flex; align-items: center; gap: 12px;"

labelStyle :: String
labelStyle =
  "width: 120px; color: var(--lattice-text-secondary, #9ca3af); " <>
  "font-size: 13px; flex-shrink: 0;"

inputGroupStyle :: String
inputGroupStyle =
  "display: flex; align-items: center; gap: 4px;"

stretchInputStyle :: String
stretchInputStyle =
  "width: 80px; padding: 6px 10px; " <>
  "background: var(--lattice-surface-3, #222); " <>
  "border: 1px solid var(--lattice-border-subtle, #2a2a2a); " <>
  "border-radius: 4px; " <>
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "font-size: 14px; text-align: right;"

unitStyle :: String
unitStyle =
  "color: var(--lattice-text-muted, #6b7280); font-size: 13px;"

hintStyle :: String
hintStyle =
  "font-size: 11px; color: var(--lattice-text-muted, #6b7280); " <>
  "margin: 0; font-style: italic;"

presetsStyle :: String
presetsStyle =
  "display: flex; gap: 8px; flex-wrap: wrap;"

presetButtonStyle :: Boolean -> String
presetButtonStyle isActive =
  "padding: 4px 12px; " <>
  "background: " <> (if isActive then "var(--lattice-accent, #8b5cf6)" else "var(--lattice-surface-3, #222)") <> "; " <>
  "border: 1px solid " <> (if isActive then "var(--lattice-accent, #8b5cf6)" else "var(--lattice-border-subtle, #2a2a2a)") <> "; " <>
  "border-radius: 999px; " <>
  "color: " <> (if isActive then "white" else "var(--lattice-text-secondary, #9ca3af)") <> "; " <>
  "font-size: 12px; cursor: pointer; " <>
  "transition: all 0.15s ease;"

selectStyle :: String
selectStyle =
  "flex: 1; padding: 6px 10px; " <>
  "background: var(--lattice-surface-3, #222); " <>
  "border: 1px solid var(--lattice-border-subtle, #2a2a2a); " <>
  "border-radius: 4px; " <>
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "font-size: 13px; cursor: pointer;"

previewSectionStyle :: String
previewSectionStyle =
  "background: var(--lattice-surface-1, #121212); " <>
  "border-radius: 4px; padding: 12px;"

highlightRowStyle :: String
highlightRowStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.1)); " <>
  "padding: 8px 12px; border-radius: 4px; margin: 4px 0;"

checkboxRowStyle :: String
checkboxRowStyle =
  "display: flex; align-items: center; gap: 8px; cursor: pointer; " <>
  "color: var(--lattice-text-secondary, #9ca3af); font-size: 13px;"

checkboxStyle :: String
checkboxStyle =
  "width: 16px; height: 16px; " <>
  "accent-color: var(--lattice-accent, #8b5cf6);"

footerStyle :: String
footerStyle =
  "display: flex; align-items: center; gap: 8px; " <>
  "padding: 16px 20px; " <>
  "border-top: 1px solid var(--lattice-border-subtle, #2a2a2a);"

secondaryButtonStyle :: String
secondaryButtonStyle =
  "padding: 8px 16px; border-radius: 4px; " <>
  "font-size: 13px; font-weight: 500; cursor: pointer; " <>
  "background: var(--lattice-surface-3, #222); " <>
  "border: 1px solid var(--lattice-border-subtle, #2a2a2a); " <>
  "color: var(--lattice-text-secondary, #9ca3af); " <>
  "transition: all 0.15s ease;"

primaryButtonStyle :: String
primaryButtonStyle =
  "padding: 8px 16px; border-radius: 4px; " <>
  "font-size: 13px; font-weight: 500; cursor: pointer; " <>
  "background: var(--lattice-accent, #8b5cf6); " <>
  "border: 1px solid var(--lattice-accent, #8b5cf6); " <>
  "color: white; transition: all 0.15s ease;"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // actions
-- ═══════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    state <- H.get
    -- Reset when opening
    when (input.visible && not state.visible) do
      H.modify_ _ 
        { stretchFactor = input.currentStretchFactor
        , stretchInput = show input.currentStretchFactor
        , holdInPlace = HoldInPoint
        , reversePlayback = false
        }
    H.modify_ _ 
      { visible = input.visible
      , layerId = input.layerId
      , originalDuration = input.originalDuration
      , currentStretchFactor = input.currentStretchFactor
      , fps = input.fps
      }
  
  HandleKeyDown event -> do
    let key = KE.key event
    when (key == "Escape") do
      H.raise Cancelled
    when (key == "Enter" && not (KE.shiftKey event)) do
      handleAction Apply
  
  UpdateStretchFactor value -> do
    H.modify_ _ { stretchInput = value }
    case fromString value of
      Just n | n >= 10.0 && n <= 1000.0 -> 
        H.modify_ _ { stretchFactor = round n }
      _ -> pure unit
  
  SelectPreset value -> do
    H.modify_ _ 
      { stretchFactor = value
      , stretchInput = show value
      }
  
  SetHoldInPlace holdPoint -> do
    H.modify_ _ { holdInPlace = holdPoint }
  
  ToggleReverse enabled -> do
    H.modify_ _ { reversePlayback = enabled }
  
  Reset -> do
    H.modify_ _ 
      { stretchFactor = 100
      , stretchInput = "100"
      , reversePlayback = false
      , holdInPlace = HoldInPoint
      }
  
  Apply -> do
    state <- H.get
    let
      speed = (if state.reversePlayback then -1.0 else 1.0) * 
              (100.0 / toNumber state.stretchFactor)
      result =
        { stretchFactor: state.stretchFactor
        , holdInPlace: state.holdInPlace
        , reverse: state.reversePlayback
        , speed: speed
        }
    H.raise (Applied result)
  
  Cancel -> do
    H.raise Cancelled

handleQuery :: forall m a. Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  Close a -> do
    H.modify_ _ { visible = false }
    pure (Just a)
  
  Open a -> do
    H.modify_ _ { visible = true }
    pure (Just a)
