-- | Pre-compose Dialog
-- |
-- | Simple dialog for creating a new composition from selected layers.
-- | User enters a name and layers are moved to the new composition.
-- |
-- | System F/Omega: Precompose = LayerCount × String → CompName
module Lattice.UI.Components.PrecomposeDialog
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String (trim)
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
  , layerCount :: Int
  , defaultName :: String
  }

data Output
  = Confirmed String  -- Composition name
  | Cancelled

data Query a
  = Close a
  | Open a

type Slot id = H.Slot Query Output id

type State =
  { visible :: Boolean
  , layerCount :: Int
  , compName :: String
  }

data Action
  = Initialize
  | Receive Input
  | HandleKeyDown KeyboardEvent
  | UpdateName String
  | Confirm
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
  , layerCount: input.layerCount
  , compName: input.defaultName
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                   // render
-- ═══════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state
  | not state.visible = HH.text ""
  | otherwise =
      HH.div
        [ cls [ "lattice-precompose-overlay" ]
        , HP.attr (HH.AttrName "style") overlayStyle
        , ARIA.role "dialog"
        , ARIA.modal "true"
        , ARIA.labelledBy "precompose-title"
        , HE.onKeyDown HandleKeyDown
        , HP.tabIndex 0
        ]
        [ HH.div
            [ cls [ "lattice-precompose-container" ]
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
    [ HH.h3
        [ HP.id "precompose-title"
        , HP.attr (HH.AttrName "style") titleStyle
        ]
        [ HH.text "Pre-compose" ]
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
    [ -- Name input
      HH.div
        [ cls [ "form-row" ]
        , HP.attr (HH.AttrName "style") formRowStyle
        ]
        [ HH.label
            [ HP.for "precomp-name"
            , HP.attr (HH.AttrName "style") labelStyle
            ]
            [ HH.text "New composition name" ]
        , HH.input
            [ HP.id "precomp-name"
            , HP.type_ HP.InputText
            , HP.value state.compName
            , HP.placeholder "Enter name..."
            , HP.autofocus true
            , HP.attr (HH.AttrName "style") inputStyle
            , HE.onValueInput UpdateName
            ]
        ]
    
    -- Info text
    , HH.div
        [ cls [ "info-text" ]
        , HP.attr (HH.AttrName "style") infoTextStyle
        ]
        [ HH.text (layerText state.layerCount) ]
    ]
  where
    layerText :: Int -> String
    layerText count =
      show count <> " layer" <> (if count /= 1 then "s" else "") <> 
      " will be moved to the new composition."

renderFooter :: forall m. State -> H.ComponentHTML Action () m
renderFooter state =
  HH.div
    [ cls [ "dialog-footer" ]
    , HP.attr (HH.AttrName "style") footerStyle
    ]
    [ HH.button
        [ cls [ "btn-cancel" ]
        , HP.attr (HH.AttrName "style") cancelButtonStyle
        , HE.onClick \_ -> Cancel
        ]
        [ HH.text "Cancel" ]
    , HH.button
        [ cls [ "btn-confirm" ]
        , HP.attr (HH.AttrName "style") (confirmButtonStyle hasValidName)
        , HP.disabled (not hasValidName)
        , HE.onClick \_ -> Confirm
        ]
        [ HH.text "OK" ]
    ]
  where
    hasValidName = trim state.compName /= ""

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
  "background: #1e1e1e; " <>
  "border: 1px solid #333; " <>
  "border-radius: 8px; " <>
  "width: 360px; " <>
  "box-shadow: 0 8px 32px rgba(0, 0, 0, 0.5);"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 12px 16px; " <>
  "border-bottom: 1px solid #333;"

titleStyle :: String
titleStyle =
  "margin: 0; font-size: 14px; font-weight: 600; color: #fff;"

closeButtonStyle :: String
closeButtonStyle =
  "background: transparent; border: none; " <>
  "color: #888; font-size: 20px; cursor: pointer; " <>
  "padding: 0; line-height: 1;"

bodyStyle :: String
bodyStyle =
  "padding: 16px;"

formRowStyle :: String
formRowStyle =
  "margin-bottom: 12px;"

labelStyle :: String
labelStyle =
  "display: block; color: #aaa; font-size: 12px; margin-bottom: 6px;"

inputStyle :: String
inputStyle =
  "width: 100%; background: #111; " <>
  "border: 1px solid #444; color: #fff; " <>
  "padding: 8px 12px; border-radius: 4px; font-size: 13px; " <>
  "box-sizing: border-box;"

infoTextStyle :: String
infoTextStyle =
  "color: #666; font-size: 12px; font-style: italic;"

footerStyle :: String
footerStyle =
  "display: flex; justify-content: flex-end; gap: 8px; " <>
  "padding: 12px 16px; border-top: 1px solid #333;"

cancelButtonStyle :: String
cancelButtonStyle =
  "padding: 8px 16px; border-radius: 4px; " <>
  "font-size: 13px; cursor: pointer; " <>
  "background: #333; border: 1px solid #444; color: #ccc;"

confirmButtonStyle :: Boolean -> String
confirmButtonStyle enabled =
  "padding: 8px 16px; border-radius: 4px; " <>
  "font-size: 13px; " <>
  "background: #4a90d9; border: none; color: #fff; " <>
  "cursor: " <> (if enabled then "pointer" else "not-allowed") <> "; " <>
  "opacity: " <> (if enabled then "1" else "0.5") <> ";"

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
      H.modify_ _ { compName = input.defaultName }
    H.modify_ _ 
      { visible = input.visible
      , layerCount = input.layerCount
      }
  
  HandleKeyDown event -> do
    let key = KE.key event
    when (key == "Escape") do
      H.raise Cancelled
    when (key == "Enter") do
      handleAction Confirm
  
  UpdateName name -> do
    H.modify_ _ { compName = name }
  
  Confirm -> do
    state <- H.get
    let trimmedName = trim state.compName
    when (trimmedName /= "") do
      H.raise (Confirmed trimmedName)
  
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
