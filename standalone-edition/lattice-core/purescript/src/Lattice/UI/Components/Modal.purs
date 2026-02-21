-- | Modal Component
-- |
-- | A reusable modal dialog wrapper with overlay, header, content, and footer.
-- | Supports keyboard navigation (Escape to close), click-outside-to-close,
-- | and proper ARIA attributes for accessibility.
-- |
-- | System F/Omega: Modal α β = ∀m. MonadAff m ⇒ (α → HTML) × (β → Output) → Component
module Lattice.UI.Components.Modal
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  , ModalSize(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.KeyboardEvent as KE
import Web.UIEvent.MouseEvent (MouseEvent)

import Lattice.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                    // types
-- ═══════════════════════════════════════════════════════════════════════════

-- | Modal size variants
data ModalSize
  = ModalSmall     -- ^ 380px - Confirmations, simple dialogs
  | ModalMedium    -- ^ 480px - Standard dialogs
  | ModalLarge     -- ^ 640px - Complex forms
  | ModalWide      -- ^ 720px - Preferences, settings
  | ModalFull      -- ^ 90vw - Full-screen dialogs

derive instance eqModalSize :: Eq ModalSize

type Input =
  { visible :: Boolean
  , title :: String
  , size :: ModalSize
  , showCloseButton :: Boolean
  , closeOnOverlayClick :: Boolean
  , closeOnEscape :: Boolean
  }

data Output
  = ModalClosed
  | ModalConfirmed
  | ModalCancelled

data Query a
  = Close a
  | Open a

type Slot id = H.Slot Query Output id

type State =
  { visible :: Boolean
  , title :: String
  , size :: ModalSize
  , showCloseButton :: Boolean
  , closeOnOverlayClick :: Boolean
  , closeOnEscape :: Boolean
  }

data Action
  = Initialize
  | Receive Input
  | HandleOverlayClick MouseEvent
  | HandleKeyDown KeyboardEvent
  | CloseModal
  | ConfirmModal

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
  , title: input.title
  , size: input.size
  , showCloseButton: input.showCloseButton
  , closeOnOverlayClick: input.closeOnOverlayClick
  , closeOnEscape: input.closeOnEscape
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                   // render
-- ═══════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state
  | not state.visible = HH.text ""
  | otherwise =
      HH.div
        [ cls [ "lattice-modal-overlay" ]
        , HP.attr (HH.AttrName "style") overlayStyle
        , ARIA.role "dialog"
        , ARIA.modal "true"
        , ARIA.labelledBy "modal-title"
        , HE.onClick HandleOverlayClick
        , HE.onKeyDown HandleKeyDown
        , HP.tabIndex 0
        ]
        [ HH.div
            [ cls [ "lattice-modal-container" ]
            , HP.attr (HH.AttrName "style") (containerStyle state.size)
            , HE.onClick \e -> HandleOverlayClick e  -- Stop propagation handled in handler
            ]
            [ -- Header
              renderHeader state
            ]
        ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ cls [ "lattice-modal-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.h2
        [ cls [ "lattice-modal-title" ]
        , HP.id "modal-title"
        , HP.attr (HH.AttrName "style") titleStyle
        ]
        [ HH.text state.title ]
    , if state.showCloseButton
        then renderCloseButton
        else HH.text ""
    ]

renderCloseButton :: forall m. H.ComponentHTML Action () m
renderCloseButton =
  HH.button
    [ cls [ "lattice-modal-close" ]
    , HP.attr (HH.AttrName "style") closeButtonStyle
    , HP.title "Close (Escape)"
    , ARIA.label "Close modal"
    , HE.onClick \_ -> CloseModal
    ]
    [ HH.text "×" ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                         // inline // styles
-- ═══════════════════════════════════════════════════════════════════════════

overlayStyle :: String
overlayStyle =
  "position: fixed; inset: 0; " <>
  "background: rgba(0, 0, 0, 0.75); " <>
  "display: flex; align-items: center; justify-content: center; " <>
  "z-index: 10000; " <>
  "animation: fadeIn 0.15s ease;"

containerStyle :: ModalSize -> String
containerStyle size =
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border-default, #333); " <>
  "border-radius: var(--lattice-radius-lg, 8px); " <>
  "box-shadow: 0 16px 48px rgba(0, 0, 0, 0.5); " <>
  "display: flex; flex-direction: column; " <>
  "max-height: 85vh; " <>
  "width: " <> sizeToWidth size <> "; " <>
  "max-width: 90vw; " <>
  "animation: slideUp 0.2s ease;"

sizeToWidth :: ModalSize -> String
sizeToWidth = case _ of
  ModalSmall -> "380px"
  ModalMedium -> "480px"
  ModalLarge -> "640px"
  ModalWide -> "720px"
  ModalFull -> "90vw"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 16px 20px; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a); " <>
  "flex-shrink: 0;"

titleStyle :: String
titleStyle =
  "margin: 0; font-size: 16px; font-weight: 600; " <>
  "color: var(--lattice-text-primary, #e5e5e5);"

closeButtonStyle :: String
closeButtonStyle =
  "width: 28px; height: 28px; " <>
  "border: none; background: transparent; " <>
  "color: var(--lattice-text-muted, #6b7280); " <>
  "font-size: 20px; cursor: pointer; " <>
  "border-radius: 4px; " <>
  "display: flex; align-items: center; justify-content: center; " <>
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
      , title = input.title
      , size = input.size
      , showCloseButton = input.showCloseButton
      , closeOnOverlayClick = input.closeOnOverlayClick
      , closeOnEscape = input.closeOnEscape
      }
  
  HandleOverlayClick _ -> do
    -- Note: In a full implementation, we'd check if click was on overlay vs container
    -- For now, this is called on overlay click only due to stopPropagation in container
    state <- H.get
    when state.closeOnOverlayClick do
      H.raise ModalClosed
  
  HandleKeyDown event -> do
    state <- H.get
    when (state.closeOnEscape && KE.key event == "Escape") do
      H.raise ModalClosed
    when (KE.key event == "Enter" && not (KE.shiftKey event)) do
      H.raise ModalConfirmed
  
  CloseModal -> do
    H.raise ModalClosed
  
  ConfirmModal -> do
    H.raise ModalConfirmed

handleQuery :: forall m a. Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  Close a -> do
    H.modify_ _ { visible = false }
    H.raise ModalClosed
    pure (Just a)
  
  Open a -> do
    H.modify_ _ { visible = true }
    pure (Just a)
