-- | Pure Dialog Implementation
-- |
-- | A dialog component implemented entirely in PureScript/Halogen.
-- | This provides behavioral accessibility features:
-- |
-- | - Modal/non-modal modes
-- | - Focus trapping with Tab loop
-- | - Scroll locking
-- | - Escape to close
-- | - Click outside to close
-- | - Focus restoration
-- | - Proper ARIA attributes
-- |
-- | This is a SLOT-BASED component - parents provide content via slots:
-- | - trigger: The button/element that opens the dialog
-- | - title: Dialog title (required for accessibility)
-- | - description: Dialog description (optional)
-- | - body: Main dialog content
-- | - close: Close button content
-- |
-- | STYLING: Uses Lattice design tokens from design-tokens.css
module Lattice.UI.Radix.Dialog
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Action
  , Slot
  , Slots
  , _trigger
  , _title
  , _description
  , _body
  , _close
  , defaultInput
  ) where

import Prelude

import Data.Foldable (for_)
import Data.Const (Const)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Void (Void)
-- Data.Symbol.SProxy is deprecated; using Type.Proxy.Proxy instead
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Halogen.Query.Event as HQE
import Lattice.UI.Radix.AriaHider as AH
import Lattice.UI.Radix.FocusTrap as FT
import Lattice.UI.Radix.Id as Id
import Lattice.UI.Radix.ScrollLock as ScrollLock
import Type.Proxy (Proxy(..))
import Web.Event.Event as Event
import Web.HTML as HTML
import Web.HTML.HTMLDocument as HTMLDocument
import Web.HTML.HTMLElement as HTMLElement
import Web.HTML.Window as Window
import Web.UIEvent.KeyboardEvent as KE
import Web.UIEvent.KeyboardEvent.EventTypes as KET

-- | Dialog input props
type Input =
  { open :: Maybe Boolean           -- Controlled open state
  , defaultOpen :: Boolean          -- Initial state if uncontrolled
  , modal :: Boolean                -- Modal (blocking) vs modeless
  , closeOnEscape :: Boolean        -- Close on Escape key
  , closeOnOutsideClick :: Boolean  -- Close on click outside
  }

defaultInput :: Input
defaultInput =
  { open: Nothing
  , defaultOpen: false
  , modal: true
  , closeOnEscape: true
  , closeOnOutsideClick: true
  }

-- | Output events
data Output
  = Opened
  | Closed
  | OpenChanged Boolean

-- | Queries for external control
data Query a
  = Open a
  | Close a
  | Toggle a
  | IsOpen (Boolean -> a)

-- | Slot labels for child content
_trigger :: Proxy "trigger"
_trigger = Proxy

_title :: Proxy "title"
_title = Proxy

_description :: Proxy "description"
_description = Proxy

_body :: Proxy "body"
_body = Proxy

_close :: Proxy "close"
_close = Proxy

-- | Child slots type - parents render content into these slots
type Slots =
  ( trigger :: H.Slot (Const Void) Void Unit
  , title :: H.Slot (Const Void) Void Unit  
  , description :: H.Slot (Const Void) Void Unit
  , body :: H.Slot (Const Void) Void Unit
  , close :: H.Slot (Const Void) Void Unit
  )

-- | Internal state
type State =
  { isOpen :: Boolean
  , input :: Input
  , triggerRef :: Maybe HTMLElement.HTMLElement
  , contentRef :: Maybe HTMLElement.HTMLElement
  , previousActiveElement :: Maybe HTMLElement.HTMLElement
  , focusScope :: Maybe FT.FocusScope
  , ariaHiderState :: Maybe AH.AriaHiderState
  , idGen :: Maybe Id.IdGenerator
  , contentId :: String
  , titleId :: String
  , descriptionId :: String
  }

-- | Internal actions
data Action
  = Initialize
  | Finalize
  | Receive Input
  | HandleTriggerClick
  | HandleCloseClick
  | HandleKeyDown KE.KeyboardEvent
  | HandleOverlayClick
  | ContentClicked
  | SetTriggerRef (Maybe HTMLElement.HTMLElement)
  | SetContentRef (Maybe HTMLElement.HTMLElement)

-- | Slot type for parent components
type Slot id = H.Slot Query Output id

-- | The component accepts child HTML for each slot area
component :: forall m. MonadAff m 
  => { trigger :: H.ComponentHTML Action Slots m
     , title :: H.ComponentHTML Action Slots m
     , description :: H.ComponentHTML Action Slots m
     , body :: H.ComponentHTML Action Slots m
     , close :: H.ComponentHTML Action Slots m
     }
  -> H.Component Query Input Output m
component content = H.mkComponent
  { initialState
  , render: renderWithContent content
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      , finalize = Just Finalize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { isOpen: fromMaybe input.defaultOpen input.open
  , input
  , triggerRef: Nothing
  , contentRef: Nothing
  , previousActiveElement: Nothing
  , focusScope: Nothing
  , ariaHiderState: Nothing
  , idGen: Nothing
  , contentId: ""
  , titleId: ""
  , descriptionId: ""
  }

renderWithContent :: forall m. MonadAff m
  => { trigger :: H.ComponentHTML Action Slots m
     , title :: H.ComponentHTML Action Slots m
     , description :: H.ComponentHTML Action Slots m
     , body :: H.ComponentHTML Action Slots m
     , close :: H.ComponentHTML Action Slots m
     }
  -> State 
  -> H.ComponentHTML Action Slots m
renderWithContent content state =
  HH.div
    [ HP.class_ (HH.ClassName "lattice-dialog-root") ]
    [ renderTrigger content.trigger state
    , if state.isOpen then renderPortal content state else HH.text ""
    ]

renderTrigger :: forall m. MonadAff m 
  => H.ComponentHTML Action Slots m
  -> State 
  -> H.ComponentHTML Action Slots m
renderTrigger triggerContent state =
  HH.div
    [ HP.class_ (HH.ClassName "lattice-dialog-trigger-wrapper")
    , HE.onClick \_ -> HandleTriggerClick
    , HP.ref (H.RefLabel "trigger")
    , ARIA.hasPopup "dialog"
    , ARIA.expanded (show state.isOpen)
    , ARIA.controls state.contentId
    , HP.attr (HH.AttrName "data-state") (if state.isOpen then "open" else "closed")
    ]
    [ triggerContent ]

renderPortal :: forall m. MonadAff m
  => { trigger :: H.ComponentHTML Action Slots m
     , title :: H.ComponentHTML Action Slots m
     , description :: H.ComponentHTML Action Slots m
     , body :: H.ComponentHTML Action Slots m
     , close :: H.ComponentHTML Action Slots m
     }
  -> State 
  -> H.ComponentHTML Action Slots m
renderPortal content state =
  HH.div
    [ HP.class_ (HH.ClassName "lattice-dialog-portal") ]
    [ renderOverlay state
    , renderContent content state
    ]

renderOverlay :: forall m. State -> H.ComponentHTML Action Slots m
renderOverlay state =
  HH.div
    [ HP.class_ (HH.ClassName "lattice-dialog-overlay")
    , HP.attr (HH.AttrName "data-state") (if state.isOpen then "open" else "closed")
    , HE.onClick \_ -> HandleOverlayClick
    ]
    []

renderContent :: forall m. MonadAff m
  => { trigger :: H.ComponentHTML Action Slots m
     , title :: H.ComponentHTML Action Slots m
     , description :: H.ComponentHTML Action Slots m
     , body :: H.ComponentHTML Action Slots m
     , close :: H.ComponentHTML Action Slots m
     }
  -> State 
  -> H.ComponentHTML Action Slots m
renderContent content state =
  HH.div
    [ HP.class_ (HH.ClassName "lattice-dialog-content")
    , HP.ref (H.RefLabel "content")
    , HP.id state.contentId
    , HP.attr (HH.AttrName "role") "dialog"
    , HP.attr (HH.AttrName "aria-modal") (if state.input.modal then "true" else "false")
    , ARIA.labelledBy state.titleId
    , ARIA.describedBy state.descriptionId
    , HP.attr (HH.AttrName "data-state") (if state.isOpen then "open" else "closed")
    , HP.tabIndex 0
    , HE.onClick \_ -> ContentClicked
    ]
    [ HH.div 
        [ HP.id state.titleId
        , HP.class_ (HH.ClassName "lattice-dialog-title")
        ]
        [ content.title ]
    , HH.div
        [ HP.id state.descriptionId
        , HP.class_ (HH.ClassName "lattice-dialog-description")
        ]
        [ content.description ]
    , HH.div [ HP.class_ (HH.ClassName "lattice-dialog-body") ]
        [ content.body ]
    , HH.div
        [ HP.class_ (HH.ClassName "lattice-dialog-close")
        , HE.onClick \_ -> HandleCloseClick
        ]
        [ content.close ]
    ]

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> do
    idGen <- liftEffect $ Id.createIdGenerator "lattice-dialog"
    contentId <- liftEffect $ Id.useId idGen "content"
    titleId <- liftEffect $ Id.useId idGen "title"
    descriptionId <- liftEffect $ Id.useId idGen "description"
    H.modify_ _ 
      { idGen = Just idGen
      , contentId = contentId
      , titleId = titleId
      , descriptionId = descriptionId
      }
    
    doc <- liftEffect $ HTML.window >>= Window.document
    void $ H.subscribe $ HQE.eventListener
      KET.keydown
      (HTMLDocument.toEventTarget doc)
      (KE.fromEvent >>> map HandleKeyDown)

  Finalize -> do
    state <- H.get
    when state.isOpen do
      for_ state.focusScope \scope ->
        liftEffect $ FT.destroyFocusScope scope
      for_ state.ariaHiderState \ariaState ->
        liftEffect $ AH.restoreOthers ariaState
      liftEffect restoreBodyScroll

  Receive newInput -> do
    case newInput.open of
      Just newOpen -> do
        state <- H.get
        when (newOpen /= state.isOpen) do
          if newOpen
            then openDialog
            else closeDialog
      Nothing -> pure unit
    H.modify_ _ { input = newInput }

  HandleTriggerClick -> do
    state <- H.get
    mTrigger <- H.getHTMLElementRef (H.RefLabel "trigger")
    H.modify_ _ { triggerRef = mTrigger }
    
    if state.isOpen
      then closeDialog
      else openDialog

  HandleCloseClick -> closeDialog

  HandleKeyDown ke -> do
    state <- H.get
    when state.isOpen do
      when (state.input.closeOnEscape && KE.key ke == "Escape") do
        liftEffect $ Event.preventDefault (KE.toEvent ke)
        closeDialog
      
      when (state.input.modal && KE.key ke == "Tab") do
        for_ state.focusScope \scope -> do
          handled <- liftEffect $ FT.handleTabKey scope ke
          when handled do
            liftEffect $ Event.preventDefault (KE.toEvent ke)

  HandleOverlayClick -> do
    state <- H.get
    when (state.isOpen && state.input.closeOnOutsideClick) do
      closeDialog

  ContentClicked -> pure unit

  SetTriggerRef ref -> H.modify_ _ { triggerRef = ref }
  SetContentRef ref -> H.modify_ _ { contentRef = ref }

openDialog :: forall m. MonadAff m => H.HalogenM State Action Slots Output m Unit
openDialog = do
  state <- H.get
  
  doc <- liftEffect $ HTML.window >>= Window.document
  mActive <- liftEffect $ HTMLDocument.activeElement doc
  H.modify_ _ { previousActiveElement = mActive }
  
  when state.input.modal do
    liftEffect lockBodyScroll
  
  H.modify_ _ { isOpen = true }
  
  mContent <- H.getHTMLElementRef (H.RefLabel "content")
  for_ mContent \el -> do
    when state.input.modal do
      ariaState <- liftEffect $ AH.hideOthers el
      H.modify_ _ { ariaHiderState = Just ariaState }
    
    scope <- liftEffect $ FT.createFocusScope el
    H.modify_ _ { focusScope = Just scope }
    
    liftEffect $ FT.trapFocus scope
  
  H.raise Opened
  H.raise (OpenChanged true)

closeDialog :: forall m. MonadAff m => H.HalogenM State Action Slots Output m Unit
closeDialog = do
  state <- H.get
  
  for_ state.focusScope \scope ->
    liftEffect $ FT.destroyFocusScope scope
  H.modify_ _ { focusScope = Nothing }
  
  for_ state.ariaHiderState \ariaState ->
    liftEffect $ AH.restoreOthers ariaState
  H.modify_ _ { ariaHiderState = Nothing }
  
  when state.input.modal do
    liftEffect restoreBodyScroll
  
  H.modify_ _ { isOpen = false }
  
  for_ state.triggerRef \el ->
    liftEffect $ HTMLElement.focus el
  
  H.raise Closed
  H.raise (OpenChanged false)

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  Open a -> do
    openDialog
    pure (Just a)
  
  Close a -> do
    closeDialog
    pure (Just a)
  
  Toggle a -> do
    state <- H.get
    if state.isOpen then closeDialog else openDialog
    pure (Just a)
  
  IsOpen reply -> do
    state <- H.get
    pure (Just (reply state.isOpen))

-- | Lock body scroll using CSS
lockBodyScroll :: Effect Unit
lockBodyScroll = ScrollLock.lock

-- | Restore body scroll
restoreBodyScroll :: Effect Unit
restoreBodyScroll = ScrollLock.unlock
