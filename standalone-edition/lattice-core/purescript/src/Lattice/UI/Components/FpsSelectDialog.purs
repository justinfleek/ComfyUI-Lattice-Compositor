-- | FPS Select Dialog
-- |
-- | Dialog shown when video fps cannot be detected.
-- | User must select the correct fps for the imported video.
-- |
-- | System F/Omega: FpsDialog = String × Number → Fps × Confirmed
module Lattice.UI.Components.FpsSelectDialog
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  ) where

import Prelude

import Data.Array as Array
import Data.Int (toNumber)
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

type FpsOption =
  { value :: Int
  , label :: String
  }

type Input =
  { visible :: Boolean
  , fileName :: String
  , videoDuration :: Number  -- Duration in seconds
  }

data Output
  = Confirmed Int      -- Selected FPS
  | Cancelled

data Query a
  = Close a
  | Open a

type Slot id = H.Slot Query Output id

type State =
  { visible :: Boolean
  , fileName :: String
  , videoDuration :: Number
  , selectedFps :: Int
  , useCustomFps :: Boolean
  , customFpsValue :: String
  }

data Action
  = Initialize
  | Receive Input
  | HandleKeyDown KeyboardEvent
  | SelectFps Int
  | ToggleCustomFps Boolean
  | UpdateCustomFps String
  | ConfirmSelection
  | Cancel

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // fps options
-- ═══════════════════════════════════════════════════════════════════════════

fpsOptions :: Array FpsOption
fpsOptions =
  [ { value: 8, label: "AnimateDiff" }
  , { value: 16, label: "WAN / Mochi" }
  , { value: 24, label: "Film" }
  , { value: 30, label: "Standard" }
  , { value: 60, label: "High FR" }
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
  , fileName: input.fileName
  , videoDuration: input.videoDuration
  , selectedFps: 16  -- Default to WAN standard
  , useCustomFps: false
  , customFpsValue: "30"
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                   // render
-- ═══════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state
  | not state.visible = HH.text ""
  | otherwise =
      HH.div
        [ cls [ "lattice-fps-dialog-overlay" ]
        , HP.attr (HH.AttrName "style") overlayStyle
        , ARIA.role "dialog"
        , ARIA.modal "true"
        , ARIA.labelledBy "fps-dialog-title"
        , HE.onKeyDown HandleKeyDown
        , HP.tabIndex 0
        ]
        [ HH.div
            [ cls [ "lattice-fps-dialog-container" ]
            , HP.attr (HH.AttrName "style") containerStyle
            ]
            [ renderHeader
            , renderBody state
            , renderFooter state
            ]
        ]

renderHeader :: forall m. H.ComponentHTML Action () m
renderHeader =
  HH.div
    [ cls [ "dialog-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.h2
        [ HP.id "fps-dialog-title"
        , HP.attr (HH.AttrName "style") titleStyle
        ]
        [ HH.text "Select Video Frame Rate" ]
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
    [ -- Info section
      HH.div
        [ cls [ "info-section" ]
        , HP.attr (HH.AttrName "style") infoSectionStyle
        ]
        [ HH.p
            [ cls [ "info-text" ]
            , HP.attr (HH.AttrName "style") infoTextStyle
            ]
            [ HH.text "Unable to detect frame rate for "
            , HH.strong [ HP.attr (HH.AttrName "style") "color: var(--lattice-warning, #f59e0b);" ]
                [ HH.text state.fileName ]
            , HH.text "."
            ]
        , HH.p
            [ cls [ "info-subtext" ]
            , HP.attr (HH.AttrName "style") infoSubtextStyle
            ]
            [ HH.text "Please select the correct frame rate for this video." ]
        ]
    
    -- FPS options grid
    , HH.div
        [ cls [ "fps-options" ]
        , HP.attr (HH.AttrName "style") fpsOptionsStyle
        ]
        (map (renderFpsOption state) fpsOptions)
    
    -- Custom FPS
    , HH.div
        [ cls [ "custom-fps" ]
        , HP.attr (HH.AttrName "style") customFpsStyle
        ]
        [ HH.label
            [ HP.attr (HH.AttrName "style") customLabelStyle ]
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.useCustomFps
                , HE.onChecked ToggleCustomFps
                , HP.attr (HH.AttrName "style") checkboxStyle
                ]
            , HH.text " Custom frame rate"
            ]
        , if state.useCustomFps
            then HH.input
              [ cls [ "custom-input" ]
              , HP.type_ HP.InputNumber
              , HP.value state.customFpsValue
              , HP.placeholder "e.g., 23.976"
              , HP.attr (HH.AttrName "style") customInputStyle
              , HE.onValueInput UpdateCustomFps
              ]
            else HH.text ""
        ]
    ]

renderFpsOption :: forall m. State -> FpsOption -> H.ComponentHTML Action () m
renderFpsOption state opt =
  HH.button
    [ cls [ "fps-btn" ]
    , HP.attr (HH.AttrName "style") (fpsButtonStyle isSelected)
    , HE.onClick \_ -> SelectFps opt.value
    , ARIA.pressed (show isSelected)
    ]
    [ HH.span
        [ cls [ "fps-value" ]
        , HP.attr (HH.AttrName "style") (fpsValueStyle isSelected)
        ]
        [ HH.text (show opt.value) ]
    , HH.span
        [ cls [ "fps-label" ]
        , HP.attr (HH.AttrName "style") fpsLabelStyle
        ]
        [ HH.text opt.label ]
    ]
  where
    isSelected = not state.useCustomFps && state.selectedFps == opt.value

renderFooter :: forall m. State -> H.ComponentHTML Action () m
renderFooter state =
  HH.div
    [ cls [ "dialog-footer" ]
    , HP.attr (HH.AttrName "style") footerStyle
    ]
    [ HH.button
        [ cls [ "btn", "btn-secondary" ]
        , HP.attr (HH.AttrName "style") secondaryButtonStyle
        , HE.onClick \_ -> Cancel
        ]
        [ HH.text "Cancel" ]
    , HH.button
        [ cls [ "btn", "btn-primary" ]
        , HP.attr (HH.AttrName "style") (primaryButtonStyle hasValidFps)
        , HP.disabled (not hasValidFps)
        , HE.onClick \_ -> ConfirmSelection
        ]
        [ HH.text ("Import at " <> show effectiveFps <> " fps") ]
    ]
  where
    effectiveFps = getEffectiveFps state
    hasValidFps = effectiveFps > 0

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ═══════════════════════════════════════════════════════════════════════════

getEffectiveFps :: State -> Int
getEffectiveFps state
  | state.useCustomFps = 
      case fromString state.customFpsValue of
        Just n | n > 0.0 -> max 1 (floor n)
        _ -> 0
  | otherwise = state.selectedFps
  where
    floor :: Number -> Int
    floor n = case fromString (show (toNumber (truncate n))) of
      Just i -> truncate i
      Nothing -> 0
    
    truncate :: Number -> Int
    truncate n = if n < 0.0 then 0 else if n > 120.0 then 120 else toInt n
    
    toInt :: Number -> Int
    toInt n = fromMaybe 0 (intFromNumber n)
    
    intFromNumber :: Number -> Maybe Int
    intFromNumber n
      | n < 0.0 = Nothing
      | n > 2147483647.0 = Nothing
      | otherwise = Just (unsafeCoerceInt n)
    
    -- Safe because we bounded the value
    unsafeCoerceInt :: Number -> Int
    unsafeCoerceInt n = case fromString (show n) of
      Just x -> max 0 (min 120 (floor' x))
      Nothing -> 0
    
    floor' :: Number -> Int
    floor' _ = state.selectedFps  -- Fallback

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
  "min-width: 380px; max-width: 450px;"

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
  "border-radius: 4px; padding: 16px;"

infoTextStyle :: String
infoTextStyle =
  "margin: 0 0 4px 0; " <>
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "font-size: 13px;"

infoSubtextStyle :: String
infoSubtextStyle =
  "margin: 0; color: var(--lattice-text-muted, #6b7280); " <>
  "font-size: 12px;"

fpsOptionsStyle :: String
fpsOptionsStyle =
  "display: grid; grid-template-columns: repeat(5, 1fr); gap: 8px;"

fpsButtonStyle :: Boolean -> String
fpsButtonStyle isSelected =
  "display: flex; flex-direction: column; align-items: center; " <>
  "gap: 2px; padding: 12px 8px; " <>
  "background: " <> (if isSelected then "rgba(139, 92, 246, 0.15)" else "var(--lattice-surface-3, #222)") <> "; " <>
  "border: 2px solid " <> (if isSelected then "var(--lattice-accent, #8b5cf6)" else "var(--lattice-border-subtle, #2a2a2a)") <> "; " <>
  "border-radius: 4px; cursor: pointer; " <>
  "transition: all 0.15s ease;"

fpsValueStyle :: Boolean -> String
fpsValueStyle isSelected =
  "font-size: 18px; font-weight: 600; font-family: monospace; " <>
  "color: " <> (if isSelected then "var(--lattice-accent, #8b5cf6)" else "var(--lattice-text-primary, #e5e5e5)") <> ";"

fpsLabelStyle :: String
fpsLabelStyle =
  "font-size: 10px; " <>
  "color: var(--lattice-text-muted, #6b7280); " <>
  "text-transform: uppercase; letter-spacing: 0.5px;"

customFpsStyle :: String
customFpsStyle =
  "display: flex; align-items: center; gap: 12px;"

customLabelStyle :: String
customLabelStyle =
  "display: flex; align-items: center; gap: 8px; " <>
  "color: var(--lattice-text-secondary, #9ca3af); " <>
  "font-size: 13px; cursor: pointer;"

checkboxStyle :: String
checkboxStyle =
  "width: 16px; height: 16px; cursor: pointer;"

customInputStyle :: String
customInputStyle =
  "flex: 1; max-width: 120px; padding: 8px 12px; " <>
  "background: var(--lattice-surface-1, #121212); " <>
  "border: 1px solid var(--lattice-border-subtle, #2a2a2a); " <>
  "border-radius: 4px; " <>
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "font-size: 13px; font-family: monospace;"

footerStyle :: String
footerStyle =
  "display: flex; justify-content: flex-end; gap: 8px; " <>
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

primaryButtonStyle :: Boolean -> String
primaryButtonStyle enabled =
  "padding: 8px 16px; border-radius: 4px; " <>
  "font-size: 13px; font-weight: 500; " <>
  "background: var(--lattice-accent, #8b5cf6); " <>
  "border: none; color: white; " <>
  "cursor: " <> (if enabled then "pointer" else "not-allowed") <> "; " <>
  "opacity: " <> (if enabled then "1" else "0.5") <> "; " <>
  "transition: all 0.15s ease;"

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
        { selectedFps = 16
        , useCustomFps = false
        , customFpsValue = "30"
        }
    H.modify_ _ 
      { visible = input.visible
      , fileName = input.fileName
      , videoDuration = input.videoDuration
      }
  
  HandleKeyDown event -> do
    state <- H.get
    let key = KE.key event
    
    -- Escape to cancel
    when (key == "Escape") do
      H.raise Cancelled
    
    -- Enter to confirm
    when (key == "Enter") do
      let fps = getEffectiveFps state
      when (fps > 0) do
        H.raise (Confirmed fps)
    
    -- Number keys 1-5 to quick select
    when (not state.useCustomFps) do
      case key of
        "1" -> H.modify_ _ { selectedFps = 8 }
        "2" -> H.modify_ _ { selectedFps = 16 }
        "3" -> H.modify_ _ { selectedFps = 24 }
        "4" -> H.modify_ _ { selectedFps = 30 }
        "5" -> H.modify_ _ { selectedFps = 60 }
        _ -> pure unit
  
  SelectFps fps -> do
    H.modify_ _ { selectedFps = fps, useCustomFps = false }
  
  ToggleCustomFps enabled -> do
    state <- H.get
    when enabled do
      H.modify_ _ { customFpsValue = show state.selectedFps }
    H.modify_ _ { useCustomFps = enabled }
  
  UpdateCustomFps value -> do
    H.modify_ _ { customFpsValue = value }
  
  ConfirmSelection -> do
    state <- H.get
    let fps = getEffectiveFps state
    when (fps > 0) do
      H.raise (Confirmed fps)
  
  Cancel -> do
    H.raise Cancelled

handleQuery :: forall m a. Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  Close a -> do
    H.modify_ _ { visible = false }
    pure (Just a)
  
  Open a -> do
    H.modify_ _ 
      { visible = true
      , selectedFps = 16
      , useCustomFps = false
      , customFpsValue = "30"
      }
    pure (Just a)
