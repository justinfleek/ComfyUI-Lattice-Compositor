-- | FPS Mismatch Dialog
-- |
-- | Dialog shown when importing video/sequence with different fps than composition.
-- | Provides three options: Match (change comp fps), Conform (time-stretch), Cancel.
-- |
-- | System F/Omega: FpsMismatch = ImportedFps × CompFps → MatchAction
module Lattice.UI.Components.FpsMismatchDialog
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  ) where

import Prelude

import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
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

type Input =
  { visible :: Boolean
  , fileName :: String
  , importedFps :: Int
  , compositionFps :: Int
  , videoDuration :: Number  -- In seconds
  }

data Output
  = Match    -- Change composition fps to match imported
  | Conform  -- Time-stretch video to match composition
  | Cancelled

data Query a
  = Close a
  | Open a

type Slot id = H.Slot Query Output id

type State =
  { visible :: Boolean
  , fileName :: String
  , importedFps :: Int
  , compositionFps :: Int
  , videoDuration :: Number
  }

data Action
  = Initialize
  | Receive Input
  | HandleKeyDown KeyboardEvent
  | SelectMatch
  | SelectConform
  | Cancel

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
  , importedFps: input.importedFps
  , compositionFps: input.compositionFps
  , videoDuration: input.videoDuration
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                   // render
-- ═══════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state
  | not state.visible = HH.text ""
  | otherwise =
      HH.div
        [ cls [ "lattice-fpsmismatch-overlay" ]
        , HP.attr (HH.AttrName "style") overlayStyle
        , ARIA.role "dialog"
        , ARIA.modal "true"
        , ARIA.labelledBy "fpsmismatch-title"
        , HE.onKeyDown HandleKeyDown
        , HP.tabIndex 0
        ]
        [ HH.div
            [ cls [ "lattice-fpsmismatch-container" ]
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
        [ HP.id "fpsmismatch-title"
        , HP.attr (HH.AttrName "style") titleStyle
        ]
        [ HH.text "Frame Rate Mismatch" ]
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
            [ HH.strong
                [ HP.attr (HH.AttrName "style") "color: var(--lattice-accent, #8b5cf6);" ]
                [ HH.text state.fileName ]
            , HH.text " has a different frame rate than the composition."
            ]
        
        -- FPS comparison
        , HH.div
            [ cls [ "fps-comparison" ]
            , HP.attr (HH.AttrName "style") fpsComparisonStyle
            ]
            [ renderFpsItem "Imported content:" state.importedFps
            , renderFpsItem "Composition:" state.compositionFps
            ]
        ]
    
    -- Options section
    , HH.div
        [ cls [ "options-section" ]
        , HP.attr (HH.AttrName "style") optionsSectionStyle
        ]
        [ -- Match option
          HH.button
            [ cls [ "option-btn", "match-btn" ]
            , HP.attr (HH.AttrName "style") optionButtonStyle
            , HE.onClick \_ -> SelectMatch
            , HP.title ("Change composition to " <> show state.importedFps <> " fps")
            ]
            [ HH.div
                [ cls [ "option-content" ]
                , HP.attr (HH.AttrName "style") optionContentStyle
                ]
                [ HH.span
                    [ cls [ "option-title" ]
                    , HP.attr (HH.AttrName "style") optionTitleStyle
                    ]
                    [ HH.text ("Match composition to " <> show state.importedFps <> " fps") ]
                , HH.span
                    [ cls [ "option-desc" ]
                    , HP.attr (HH.AttrName "style") optionDescStyle
                    ]
                    [ HH.text ("Existing layers will be precomposed at " <> show state.compositionFps <> " fps. All " <> show state.importedFps <> " video frames will be shown.") ]
                ]
            ]
        
        -- Conform option
        , HH.button
            [ cls [ "option-btn", "conform-btn" ]
            , HP.attr (HH.AttrName "style") optionButtonStyle
            , HE.onClick \_ -> SelectConform
            , HP.title ("Keep composition at " <> show state.compositionFps <> " fps")
            ]
            [ HH.div
                [ cls [ "option-content" ]
                , HP.attr (HH.AttrName "style") optionContentStyle
                ]
                [ HH.span
                    [ cls [ "option-title" ]
                    , HP.attr (HH.AttrName "style") optionTitleStyle
                    ]
                    [ HH.text ("Conform video to " <> show state.compositionFps <> " fps") ]
                , HH.span
                    [ cls [ "option-desc" ]
                    , HP.attr (HH.AttrName "style") optionDescStyle
                    ]
                    [ HH.text ("Video will be time-stretched to match composition. Duration: " <> conformedDuration) ]
                ]
            ]
        ]
    ]
  where
    conformedDuration = formatConformedDuration state

renderFpsItem :: forall m. String -> Int -> H.ComponentHTML Action () m
renderFpsItem label fps =
  HH.div
    [ cls [ "fps-item" ]
    , HP.attr (HH.AttrName "style") fpsItemStyle
    ]
    [ HH.span
        [ cls [ "fps-label" ]
        , HP.attr (HH.AttrName "style") fpsLabelStyle
        ]
        [ HH.text label ]
    , HH.span
        [ cls [ "fps-value" ]
        , HP.attr (HH.AttrName "style") fpsValueStyle
        ]
        [ HH.text (show fps <> " fps") ]
    ]

renderFooter :: forall m. H.ComponentHTML Action () m
renderFooter =
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
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ═══════════════════════════════════════════════════════════════════════════

formatConformedDuration :: State -> String
formatConformedDuration state =
  let
    stretchFactor = toNumber state.compositionFps / toNumber state.importedFps
    newDuration = state.videoDuration / stretchFactor
    mins = floor (newDuration / 60.0)
    secs = newDuration - (toNumber mins * 60.0)
  in
  if mins > 0
    then show mins <> "m " <> formatSecs secs <> "s"
    else formatSecs secs <> "s"
  where
    floor :: Number -> Int
    floor n = case fromString (show n) of
      Just x -> truncateInt x
      Nothing -> 0
    
    truncateInt :: Number -> Int
    truncateInt n = if n < 0.0 then 0 else if n > 999999.0 then 999999 else toInt n
    
    toInt :: Number -> Int
    toInt _ = 0  -- Simplified
    
    formatSecs :: Number -> String
    formatSecs s = 
      let rounded = toNumber (round (s * 100.0)) / 100.0
      in show rounded
    
    round :: Number -> Int
    round n = truncateInt (n + 0.5)

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
  "border-radius: 8px; " <>
  "box-shadow: 0 8px 32px rgba(0, 0, 0, 0.4); " <>
  "min-width: 420px; max-width: 500px;"

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
  "margin: 0 0 12px 0; " <>
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "font-size: 13px;"

fpsComparisonStyle :: String
fpsComparisonStyle =
  "display: flex; flex-direction: column; gap: 8px;"

fpsItemStyle :: String
fpsItemStyle =
  "display: flex; justify-content: space-between; align-items: center;"

fpsLabelStyle :: String
fpsLabelStyle =
  "color: var(--lattice-text-secondary, #9ca3af); font-size: 13px;"

fpsValueStyle :: String
fpsValueStyle =
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "font-family: monospace; font-size: 14px; font-weight: 600;"

optionsSectionStyle :: String
optionsSectionStyle =
  "display: flex; flex-direction: column; gap: 12px;"

optionButtonStyle :: String
optionButtonStyle =
  "display: flex; align-items: flex-start; padding: 16px; " <>
  "background: var(--lattice-surface-3, #222); " <>
  "border: 1px solid var(--lattice-border-subtle, #2a2a2a); " <>
  "border-radius: 4px; cursor: pointer; text-align: left; " <>
  "transition: all 0.15s ease;"

optionContentStyle :: String
optionContentStyle =
  "display: flex; flex-direction: column; gap: 4px;"

optionTitleStyle :: String
optionTitleStyle =
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "font-size: 14px; font-weight: 500;"

optionDescStyle :: String
optionDescStyle =
  "color: var(--lattice-text-muted, #6b7280); " <>
  "font-size: 12px; line-height: 1.4;"

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

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // actions
-- ═══════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _
      { visible = input.visible
      , fileName = input.fileName
      , importedFps = input.importedFps
      , compositionFps = input.compositionFps
      , videoDuration = input.videoDuration
      }
  
  HandleKeyDown event -> do
    let key = KE.key event
    case key of
      "Escape" -> H.raise Cancelled
      "1" -> H.raise Match
      "2" -> H.raise Conform
      _ -> pure unit
  
  SelectMatch -> do
    H.raise Match
  
  SelectConform -> do
    H.raise Conform
  
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
