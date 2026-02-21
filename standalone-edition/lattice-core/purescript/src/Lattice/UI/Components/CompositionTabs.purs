-- | CompositionTabs Component
-- |
-- | Tab bar for managing multiple compositions:
-- | - Composition tabs with name and info
-- | - Breadcrumb navigation for nested compositions
-- | - Context menu for composition operations
-- | - New composition button
module Lattice.UI.Components.CompositionTabs
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , CompositionInfo
  ) where

import Prelude

import Data.Array (filter, length, mapWithIndex)
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

-- | Composition metadata for tabs
type CompositionInfo =
  { id :: String
  , name :: String
  , width :: Int
  , height :: Int
  , fps :: Int
  , isNestedComp :: Boolean
  }

-- | Breadcrumb item
type BreadcrumbItem =
  { id :: String
  , name :: String
  }

type Input =
  { compositions :: Array CompositionInfo
  , activeCompositionId :: String
  , mainCompositionId :: String
  , breadcrumbs :: Array BreadcrumbItem
  }

data Output
  = SwitchToComposition String
  | CloseComposition String
  | NewComposition
  | OpenCompositionSettings
  | RenameComposition String String
  | DuplicateComposition String
  | SetAsMainComposition String
  | DeleteComposition String
  | NavigateToBreadcrumb Int
  | NavigateBack

data Query a

type Slot id = H.Slot Query Output id

type State =
  { compositions :: Array CompositionInfo
  , activeCompositionId :: String
  , mainCompositionId :: String
  , breadcrumbs :: Array BreadcrumbItem
  , editingId :: Maybe String
  , editingName :: String
  , contextMenu :: Maybe ContextMenuState
  }

type ContextMenuState =
  { compId :: String
  , x :: Number
  , y :: Number
  }

data Action
  = Receive Input
  | HandleSwitchTab String
  | HandleCloseTab String
  | HandleNewComposition
  | HandleStartRename String String
  | HandleRenameInput String
  | HandleFinishRename
  | HandleCancelRename
  | HandleShowContextMenu String Number Number
  | HandleHideContextMenu
  | HandleOpenSettings
  | HandleDuplicate
  | HandleSetAsMain
  | HandleDelete
  | HandleBreadcrumbClick Int
  | HandleBackClick

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
  { compositions: input.compositions
  , activeCompositionId: input.activeCompositionId
  , mainCompositionId: input.mainCompositionId
  , breadcrumbs: input.breadcrumbs
  , editingId: Nothing
  , editingName: ""
  , contextMenu: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-composition-tabs" ]
    , HP.attr (HH.AttrName "style") compositionTabsStyle
    ]
    [ -- Breadcrumb navigation (if nested)
      if length state.breadcrumbs > 1
        then renderBreadcrumbs state
        else HH.text ""
    
      -- Tabs container
    , HH.div
        [ cls [ "lattice-tabs-container" ]
        , HP.attr (HH.AttrName "style") tabsContainerStyle
        ]
        ( -- Composition tabs
          (map (renderTab state) state.compositions)
          <>
          -- New composition button
          [ renderNewCompButton ]
        )
    
      -- Context menu
    , case state.contextMenu of
        Just ctx -> renderContextMenu state ctx
        Nothing -> HH.text ""
    ]

renderBreadcrumbs :: forall m. State -> H.ComponentHTML Action () m
renderBreadcrumbs state =
  HH.div
    [ cls [ "lattice-breadcrumb-nav" ]
    , HP.attr (HH.AttrName "style") breadcrumbNavStyle
    ]
    ( -- Breadcrumb items with separators
      (flattenWithSeparators (mapWithIndex renderBreadcrumbItem state.breadcrumbs))
      <>
      -- Back button
      [ HH.button
          [ cls [ "lattice-back-btn" ]
          , HP.attr (HH.AttrName "style") backBtnStyle
          , HP.title "Go back (Backspace)"
          , HE.onClick \_ -> HandleBackClick
          ]
          [ HH.text "⬅" ]
      ]
    )
  where
    renderBreadcrumbItem :: Int -> BreadcrumbItem -> { item :: H.ComponentHTML Action () m, isLast :: Boolean }
    renderBreadcrumbItem idx crumb =
      let
        isLast = idx == length state.breadcrumbs - 1
      in
      { item: HH.span
          [ cls $ [ "lattice-breadcrumb-item" ] <> (if isLast then [ "current" ] else [])
          , HP.attr (HH.AttrName "style") (breadcrumbItemStyle isLast)
          , HE.onClick \_ -> HandleBreadcrumbClick idx
          ]
          [ HH.text crumb.name ]
      , isLast: isLast
      }
    
    flattenWithSeparators :: Array { item :: H.ComponentHTML Action () m, isLast :: Boolean } -> Array (H.ComponentHTML Action () m)
    flattenWithSeparators items = 
      items >>= \{ item, isLast } ->
        if isLast
          then [item]
          else [item, HH.span [ cls [ "lattice-breadcrumb-sep" ] ] [ HH.text "›" ]]

renderTab :: forall m. State -> CompositionInfo -> H.ComponentHTML Action () m
renderTab state comp =
  let
    isActive = comp.id == state.activeCompositionId
    isEditing = state.editingId == Just comp.id
    canClose = length state.compositions > 1
  in
  HH.div
    [ cls $ [ "lattice-tab" ]
          <> (if isActive then [ "active" ] else [])
          <> (if comp.isNestedComp then [ "nested-comp" ] else [])
    , HP.attr (HH.AttrName "style") (tabStyle isActive)
    , HE.onClick \_ -> HandleSwitchTab comp.id
    , HE.onDoubleClick \_ -> HandleStartRename comp.id comp.name
    -- Context menu handled via right-click
    ]
    [ -- Nested comp icon
      if comp.isNestedComp
        then HH.span
          [ cls [ "lattice-nested-comp-icon" ]
          , HP.title "Nested Composition"
          ]
          [ HH.text "■" ]
        else HH.text ""
    
      -- Tab name (editable or static)
    , if isEditing
        then HH.input
          [ cls [ "lattice-rename-input" ]
          , HP.attr (HH.AttrName "style") renameInputStyle
          , HP.value state.editingName
          , HE.onValueInput HandleRenameInput
          , HE.onBlur \_ -> HandleFinishRename
          ]
        else HH.span
          [ cls [ "lattice-tab-name" ] ]
          [ HH.text comp.name ]
    
      -- Tab info (resolution, fps)
    , HH.span
        [ cls [ "lattice-tab-info" ]
        , HP.attr (HH.AttrName "style") tabInfoStyle
        ]
        [ HH.text (formatCompInfo comp) ]
    
      -- Close button
    , if canClose
        then HH.button
          [ cls [ "lattice-close-btn" ]
          , HP.attr (HH.AttrName "style") closeBtnStyle
          , HP.title "Close tab"
          , HE.onClick \_ -> HandleCloseTab comp.id
          ]
          [ HH.text "×" ]
        else HH.text ""
    ]

renderNewCompButton :: forall m. H.ComponentHTML Action () m
renderNewCompButton =
  HH.button
    [ cls [ "lattice-new-comp-btn" ]
    , HP.attr (HH.AttrName "style") newCompBtnStyle
    , HP.title "New Composition (Ctrl+K)"
    , HE.onClick \_ -> HandleNewComposition
    ]
    [ HH.text "+" ]

renderContextMenu :: forall m. State -> ContextMenuState -> H.ComponentHTML Action () m
renderContextMenu state ctx =
  let
    isMain = ctx.compId == state.mainCompositionId
  in
  HH.div
    [ cls [ "lattice-context-menu" ]
    , HP.attr (HH.AttrName "style") (contextMenuStyle ctx.x ctx.y)
    ]
    [ menuButton "Composition Settings..." HandleOpenSettings false
    , menuButton "Rename" (HandleStartRename ctx.compId "") false
    , menuButton "Duplicate" HandleDuplicate false
    , HH.hr [ HP.attr (HH.AttrName "style") menuHrStyle ]
    , menuButton "Set as Main Composition" HandleSetAsMain isMain
    , HH.hr [ HP.attr (HH.AttrName "style") menuHrStyle ]
    , menuButtonDanger "Delete Composition" HandleDelete isMain
    ]
  where
    menuButton :: String -> Action -> Boolean -> H.ComponentHTML Action () m
    menuButton label action disabled =
      HH.button
        [ cls [ "lattice-context-menu-btn" ]
        , HP.attr (HH.AttrName "style") menuBtnStyle
        , HP.disabled disabled
        , HE.onClick \_ -> action
        ]
        [ HH.text label ]
    
    menuButtonDanger :: String -> Action -> Boolean -> H.ComponentHTML Action () m
    menuButtonDanger label action disabled =
      HH.button
        [ cls [ "lattice-context-menu-btn", "danger" ]
        , HP.attr (HH.AttrName "style") (menuBtnStyle <> " color: #e57373;")
        , HP.disabled disabled
        , HE.onClick \_ -> action
        ]
        [ HH.text label ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ════════════════════════════════════════════════════════════════════════════

formatCompInfo :: CompositionInfo -> String
formatCompInfo comp =
  show comp.width <> "x" <> show comp.height <> " " <> show comp.fps <> "fps"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

compositionTabsStyle :: String
compositionTabsStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "background: var(--lattice-surface-2, #252525); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #333); " <>
  "height: 28px; " <>
  "padding: 0 4px; " <>
  "overflow-x: auto; " <>
  "overflow-y: hidden;"

tabsContainerStyle :: String
tabsContainerStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 2px; " <>
  "min-width: max-content;"

tabStyle :: Boolean -> String
tabStyle isActive =
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 4px; " <>
  "padding: 4px 8px; " <>
  "background: " <> (if isActive then "var(--lattice-surface-1, #1a1a1a)" else "var(--lattice-surface-3, #1e1e1e)") <> "; " <>
  "border: 1px solid " <> (if isActive then "var(--lattice-accent, #4a90d9)" else "var(--lattice-border-subtle, #333)") <> "; " <>
  "border-bottom: " <> (if isActive then "1px solid var(--lattice-surface-1, #1a1a1a)" else "none") <> "; " <>
  "border-radius: 4px 4px 0 0; " <>
  "cursor: pointer; " <>
  "font-size: 13px; " <>
  "color: " <> (if isActive then "var(--lattice-text-primary, #e0e0e0)" else "var(--lattice-text-muted, #888)") <> "; " <>
  "max-width: 200px; " <>
  "white-space: nowrap; " <>
  "user-select: none;" <>
  (if isActive then " margin-bottom: -1px;" else "")

tabInfoStyle :: String
tabInfoStyle =
  "font-size: 11px; " <>
  "color: var(--lattice-text-muted, #666);"

closeBtnStyle :: String
closeBtnStyle =
  "width: 14px; " <>
  "height: 14px; " <>
  "padding: 0; " <>
  "border: none; " <>
  "background: transparent; " <>
  "color: var(--lattice-text-muted, #666); " <>
  "font-size: 14px; " <>
  "line-height: 1; " <>
  "cursor: pointer; " <>
  "border-radius: 2px; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "justify-content: center;"

newCompBtnStyle :: String
newCompBtnStyle =
  "width: 22px; " <>
  "height: 22px; " <>
  "padding: 0; " <>
  "border: 1px dashed var(--lattice-border-subtle, #444); " <>
  "background: transparent; " <>
  "color: var(--lattice-text-muted, #666); " <>
  "font-size: 14px; " <>
  "cursor: pointer; " <>
  "border-radius: 4px; " <>
  "margin-left: 4px;"

renameInputStyle :: String
renameInputStyle =
  "width: 100px; " <>
  "padding: 1px 4px; " <>
  "border: 1px solid var(--lattice-accent, #4a90d9); " <>
  "background: var(--lattice-surface-1, #1a1a1a); " <>
  "color: var(--lattice-text-primary, #e0e0e0); " <>
  "font-size: 13px; " <>
  "border-radius: 2px; " <>
  "outline: none;"

breadcrumbNavStyle :: String
breadcrumbNavStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 2px; " <>
  "padding: 0 8px; " <>
  "margin-right: 8px; " <>
  "border-right: 1px solid var(--lattice-border-subtle, #444); " <>
  "font-size: 13px;"

breadcrumbItemStyle :: Boolean -> String
breadcrumbItemStyle isCurrent =
  "color: " <> (if isCurrent then "var(--lattice-text-primary, #e0e0e0)" else "var(--lattice-text-muted, #888)") <> "; " <>
  "cursor: " <> (if isCurrent then "default" else "pointer") <> "; " <>
  "padding: 2px 4px; " <>
  "border-radius: 2px; " <>
  "white-space: nowrap; " <>
  "max-width: 100px; " <>
  "overflow: hidden; " <>
  "text-overflow: ellipsis;" <>
  (if isCurrent then " font-weight: 500;" else "")

backBtnStyle :: String
backBtnStyle =
  "width: 20px; " <>
  "height: 20px; " <>
  "padding: 0; " <>
  "border: none; " <>
  "background: transparent; " <>
  "color: var(--lattice-text-muted, #888); " <>
  "font-size: 12px; " <>
  "cursor: pointer; " <>
  "border-radius: 2px; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "justify-content: center; " <>
  "margin-left: 4px;"

contextMenuStyle :: Number -> Number -> String
contextMenuStyle x y =
  "position: fixed; " <>
  "left: " <> show x <> "px; " <>
  "top: " <> show y <> "px; " <>
  "background: var(--lattice-surface-3, #2a2a2a); " <>
  "border: 1px solid var(--lattice-border-subtle, #444); " <>
  "border-radius: 4px; " <>
  "box-shadow: 0 4px 12px rgba(0, 0, 0, 0.4); " <>
  "z-index: 1000; " <>
  "min-width: 160px; " <>
  "padding: 4px 0;"

menuBtnStyle :: String
menuBtnStyle =
  "display: block; " <>
  "width: 100%; " <>
  "padding: 6px 12px; " <>
  "border: none; " <>
  "background: transparent; " <>
  "color: var(--lattice-text-primary, #e0e0e0); " <>
  "font-size: 13px; " <>
  "text-align: left; " <>
  "cursor: pointer;"

menuHrStyle :: String
menuHrStyle =
  "border: none; " <>
  "border-top: 1px solid var(--lattice-border-subtle, #444); " <>
  "margin: 4px 0;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ _
      { compositions = input.compositions
      , activeCompositionId = input.activeCompositionId
      , mainCompositionId = input.mainCompositionId
      , breadcrumbs = input.breadcrumbs
      }
  
  HandleSwitchTab compId -> do
    H.raise (SwitchToComposition compId)
  
  HandleCloseTab compId -> do
    H.raise (CloseComposition compId)
  
  HandleNewComposition -> do
    H.raise NewComposition
  
  HandleStartRename compId name -> do
    H.modify_ _ { editingId = Just compId, editingName = name }
    handleAction HandleHideContextMenu
  
  HandleRenameInput name -> do
    H.modify_ _ { editingName = name }
  
  HandleFinishRename -> do
    state <- H.get
    case state.editingId of
      Just compId -> do
        when (state.editingName /= "") do
          H.raise (RenameComposition compId state.editingName)
        H.modify_ _ { editingId = Nothing, editingName = "" }
      Nothing -> pure unit
  
  HandleCancelRename -> do
    H.modify_ _ { editingId = Nothing, editingName = "" }
  
  HandleShowContextMenu compId x y -> do
    H.modify_ _ { contextMenu = Just { compId, x, y } }
  
  HandleHideContextMenu -> do
    H.modify_ _ { contextMenu = Nothing }
  
  HandleOpenSettings -> do
    H.raise OpenCompositionSettings
    handleAction HandleHideContextMenu
  
  HandleDuplicate -> do
    state <- H.get
    case state.contextMenu of
      Just ctx -> H.raise (DuplicateComposition ctx.compId)
      Nothing -> pure unit
    handleAction HandleHideContextMenu
  
  HandleSetAsMain -> do
    state <- H.get
    case state.contextMenu of
      Just ctx -> H.raise (SetAsMainComposition ctx.compId)
      Nothing -> pure unit
    handleAction HandleHideContextMenu
  
  HandleDelete -> do
    state <- H.get
    case state.contextMenu of
      Just ctx -> 
        when (ctx.compId /= state.mainCompositionId) do
          H.raise (DeleteComposition ctx.compId)
      Nothing -> pure unit
    handleAction HandleHideContextMenu
  
  HandleBreadcrumbClick idx -> do
    H.raise (NavigateToBreadcrumb idx)
  
  HandleBackClick -> do
    H.raise NavigateBack
