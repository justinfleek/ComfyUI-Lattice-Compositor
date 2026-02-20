-- | Project Panel Component
-- |
-- | Project management panel for organizing compositions, footage, and assets.
-- | Supports:
-- | - Folder hierarchy with expand/collapse
-- | - Search filtering
-- | - Asset preview thumbnails
-- | - Drag and drop for timeline import
-- | - Keyboard navigation (Arrow keys, Enter, Space)
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/ProjectPanel.vue
module Lattice.UI.Components.ProjectPanel
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  , ProjectItem
  , ProjectItemType(..)
  , Folder
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.String as String
import Data.Tuple (Tuple(..))
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
  { compositions :: Array CompositionInfo
  , footage :: Array ProjectItem
  , solids :: Array ProjectItem
  , dataAssets :: Array ProjectItem
  }

data Output
  = OpenComposition String
  | CreateLayer ProjectItem
  | ImportFile
  | CreateComposition
  | CreateFolder
  | CreateSolid
  | CreateText
  | CreateSpline
  | CreateModel
  | CreatePointCloud
  | OpenDecomposeDialog
  | OpenVectorizeDialog
  | CleanupUnusedAssets

data Query a
  = RefreshItems a
  | SetSelectedItem (Maybe String) a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                            // project // types
-- =============================================================================

data ProjectItemType
  = ItemComposition
  | ItemFootage
  | ItemSolid
  | ItemAudio
  | ItemFolder
  | ItemData

derive instance eqProjectItemType :: Eq ProjectItemType

instance showProjectItemType :: Show ProjectItemType where
  show = case _ of
    ItemComposition -> "composition"
    ItemFootage -> "footage"
    ItemSolid -> "solid"
    ItemAudio -> "audio"
    ItemFolder -> "folder"
    ItemData -> "data"

type ProjectItem =
  { id :: String
  , name :: String
  , itemType :: ProjectItemType
  , width :: Maybe Int
  , height :: Maybe Int
  , duration :: Maybe Int
  , fps :: Maybe Int
  , dataType :: Maybe String
  , dataInfo :: Maybe String
  }

type CompositionInfo =
  { id :: String
  , name :: String
  , width :: Int
  , height :: Int
  , fps :: Int
  , frameCount :: Int
  }

type Folder =
  { id :: String
  , name :: String
  , items :: Array ProjectItem
  }

type SelectedPreview =
  { previewType :: String
  , name :: String
  , details :: String
  , icon :: String
  , url :: Maybe String
  }

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { input :: Input
  , baseId :: String
  , showSearch :: Boolean
  , showNewMenu :: Boolean
  , searchQuery :: String
  , selectedItem :: Maybe String
  , expandedFolders :: Array String
  , customFolders :: Array Folder
  }

data Action
  = Initialize
  | Receive Input
  | ToggleSearch
  | ToggleNewMenu
  | UpdateSearchQuery String
  | SelectItem String
  | ToggleFolder String
  | OpenItem ProjectItem
  | HandleKeyDown Int KE.KeyboardEvent
  | TriggerImport
  | CreateCompositionAction
  | CreateFolderAction
  | CreateSolidAction
  | CreateTextAction
  | CreateSplineAction
  | CreateModelAction
  | CreatePointCloudAction
  | OpenDecomposeAction
  | OpenVectorizeAction
  | CleanupAction

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
  , baseId: "project-panel"
  , showSearch: false
  , showNewMenu: false
  , searchQuery: ""
  , selectedItem: Nothing
  , expandedFolders: ["compositions", "footage"]
  , customFolders: []
  }

-- =============================================================================
--                                                                     // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "project-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , ARIA.label "Project"
    ]
    [ renderHeader state
    , if state.showSearch then renderSearchBar state else HH.text ""
    , renderPreviewArea state
    , renderContent state
    , renderFooter state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.span
        [ cls [ "panel-title" ]
        , HP.attr (HH.AttrName "style") titleStyle
        ]
        [ HH.text "Project" ]
    , HH.div
        [ cls [ "header-actions" ]
        , HP.attr (HH.AttrName "style") headerActionsStyle
        ]
        [ HH.button
            [ cls [ "action-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Import File (Ctrl+I)"
            , HP.attr (HH.AttrName "style") actionBtnStyle
            , HE.onClick \_ -> TriggerImport
            ]
            [ HH.text "\x{1F4E5}" ]  -- Import icon
        , renderNewMenu state
        , HH.button
            [ cls [ "action-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Search"
            , HP.attr (HH.AttrName "style") actionBtnStyle
            , HE.onClick \_ -> ToggleSearch
            ]
            [ HH.text "\x{1F50D}" ]  -- Search icon
        ]
    ]

renderNewMenu :: forall m. State -> H.ComponentHTML Action Slots m
renderNewMenu state =
  HH.div
    [ cls [ "dropdown-container" ]
    , HP.attr (HH.AttrName "style") dropdownContainerStyle
    ]
    [ HH.button
        [ cls [ "action-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.title "New Item"
        , HP.attr (HH.AttrName "style") actionBtnStyle
        , HE.onClick \_ -> ToggleNewMenu
        ]
        [ HH.text "+" ]
    , if state.showNewMenu
        then renderDropdownMenu
        else HH.text ""
    ]

renderDropdownMenu :: forall m. H.ComponentHTML Action Slots m
renderDropdownMenu =
  HH.div
    [ cls [ "dropdown-menu" ]
    , HP.attr (HH.AttrName "style") dropdownMenuStyle
    , HP.attr (HH.AttrName "role") "menu"
    ]
    [ menuItem "\x{1F3AC}" "New Composition" CreateCompositionAction
    , menuItem "\x{1F4C1}" "New Folder" CreateFolderAction
    , menuDivider
    , menuItem "\x{2B1C}" "New Solid" CreateSolidAction
    , menuItem "\x{1F524}" "New Text" CreateTextAction
    , menuItem "\x{270F}" "New Spline" CreateSplineAction
    , menuItem "\x{1F9CA}" "New 3D Model" CreateModelAction
    , menuItem "\x{2601}" "New Point Cloud" CreatePointCloudAction
    , menuDivider
    , menuItem "\x{2728}" "AI Layer Decompose" OpenDecomposeAction
    , menuItem "\x{2712}" "Vectorize Image" OpenVectorizeAction
    , menuDivider
    , menuItem "\x{1F5D1}" "Remove Unused Assets" CleanupAction
    ]

menuItem :: forall m. String -> String -> Action -> H.ComponentHTML Action Slots m
menuItem icon labelText action =
  HH.button
    [ cls [ "menu-item" ]
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "style") menuItemStyle
    , HP.attr (HH.AttrName "role") "menuitem"
    , HE.onClick \_ -> action
    ]
    [ HH.span [ cls [ "menu-icon" ], HP.attr (HH.AttrName "style") menuIconStyle ] [ HH.text icon ]
    , HH.span_ [ HH.text labelText ]
    ]

menuDivider :: forall m. H.ComponentHTML Action Slots m
menuDivider =
  HH.hr [ cls [ "menu-divider" ], HP.attr (HH.AttrName "style") menuDividerStyle ]

renderSearchBar :: forall m. State -> H.ComponentHTML Action Slots m
renderSearchBar state =
  HH.div
    [ cls [ "search-bar" ]
    , HP.attr (HH.AttrName "style") searchBarStyle
    ]
    [ HH.input
        [ HP.type_ HP.InputText
        , HP.placeholder "Search project..."
        , HP.value state.searchQuery
        , cls [ "search-input" ]
        , HP.attr (HH.AttrName "style") searchInputStyle
        , HE.onValueInput UpdateSearchQuery
        ]
    ]

renderPreviewArea :: forall m. State -> H.ComponentHTML Action Slots m
renderPreviewArea state =
  case getSelectedPreview state of
    Just preview ->
      HH.div
        [ cls [ "preview-area" ]
        , HP.attr (HH.AttrName "style") previewAreaStyle
        ]
        [ HH.div
            [ cls [ "preview-thumbnail" ]
            , HP.attr (HH.AttrName "style") previewThumbnailStyle
            ]
            [ HH.div
                [ cls [ "preview-placeholder" ]
                , HP.attr (HH.AttrName "style") previewPlaceholderStyle
                ]
                [ HH.span [ cls [ "preview-icon" ] ] [ HH.text preview.icon ] ]
            ]
        , HH.div
            [ cls [ "preview-info" ]
            , HP.attr (HH.AttrName "style") previewInfoStyle
            ]
            [ HH.div
                [ cls [ "preview-name" ]
                , HP.attr (HH.AttrName "style") previewNameStyle
                ]
                [ HH.text preview.name ]
            , HH.div
                [ cls [ "preview-details" ]
                , HP.attr (HH.AttrName "style") previewDetailsStyle
                ]
                [ HH.text preview.details ]
            ]
        ]
    Nothing -> HH.text ""

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "panel-content" ]
    , HP.attr (HH.AttrName "style") contentStyle
    ]
    [ HH.div
        [ cls [ "folder-tree" ]
        , HP.attr (HH.AttrName "style") folderTreeStyle
        , HP.attr (HH.AttrName "role") "tree"
        , HP.tabIndex 0
        ]
        (renderFolders state <> renderRootItems state)
    , if Array.null (getAllItems state)
        then renderEmptyState
        else HH.text ""
    ]

renderFolders :: forall m. State -> Array (H.ComponentHTML Action Slots m)
renderFolders state =
  let
    folders = getFilteredFolders state
  in
    map (renderFolder state) folders

renderFolder :: forall m. State -> Folder -> H.ComponentHTML Action Slots m
renderFolder state folder =
  let
    isExpanded = Array.elem folder.id state.expandedFolders
    items = filterBySearch state.searchQuery folder.items
    idx = fromMaybe 0 (Array.findIndex (\f -> f.id == folder.id) (getFilteredFolders state))
  in
  HH.div
    [ cls [ "folder-item" ]
    , HP.attr (HH.AttrName "style") folderItemStyle
    , HP.attr (HH.AttrName "role") "treeitem"
    , ARIA.expanded (show isExpanded)
    ]
    [ HH.div
        [ cls [ "folder-header" ]
        , HP.attr (HH.AttrName "style") (folderHeaderStyle (state.selectedItem == Just folder.id))
        , HP.tabIndex (if idx == 0 then 0 else (-1))
        , HE.onClick \_ -> SelectItem folder.id
        , HE.onDoubleClick \_ -> ToggleFolder folder.id
        , HE.onKeyDown (HandleKeyDown idx)
        ]
        [ HH.span
            [ cls [ "expand-icon" ]
            , HP.attr (HH.AttrName "style") expandIconStyle
            , HE.onClick \_ -> ToggleFolder folder.id
            ]
            [ HH.text (if isExpanded then "\x{25BC}" else "\x{25B6}") ]
        , HH.span [ cls [ "folder-icon" ], HP.attr (HH.AttrName "style") folderIconStyle ] [ HH.text "\x{1F4C1}" ]
        , HH.span [ cls [ "folder-name" ], HP.attr (HH.AttrName "style") folderNameStyle ] [ HH.text folder.name ]
        , HH.span [ cls [ "item-count" ], HP.attr (HH.AttrName "style") itemCountStyle ] [ HH.text (show (Array.length items)) ]
        ]
    , if isExpanded
        then HH.div
              [ cls [ "folder-contents" ]
              , HP.attr (HH.AttrName "style") folderContentsStyle
              , HP.attr (HH.AttrName "role") "group"
              ]
              (Array.mapWithIndex (renderProjectItem state) items)
        else HH.text ""
    ]

renderRootItems :: forall m. State -> Array (H.ComponentHTML Action Slots m)
renderRootItems state =
  let
    rootItems = filterBySearch state.searchQuery (getRootItems state)
    folderCount = Array.length (getFilteredFolders state)
  in
    Array.mapWithIndex (\i item -> renderProjectItem state (folderCount + i) item) rootItems

renderProjectItem :: forall m. State -> Int -> ProjectItem -> H.ComponentHTML Action Slots m
renderProjectItem state idx item =
  let
    isSelected = state.selectedItem == Just item.id
  in
  HH.div
    [ cls [ "project-item" ]
    , HP.attr (HH.AttrName "style") (projectItemStyle isSelected)
    , HP.attr (HH.AttrName "role") "treeitem"
    , HP.attr (HH.AttrName "draggable") "true"
    , HP.tabIndex (if idx == 0 then 0 else (-1))
    , ARIA.selected (show isSelected)
    , HP.attr (HH.AttrName "data-state") (if isSelected then "selected" else "unselected")
    , HE.onClick \_ -> SelectItem item.id
    , HE.onDoubleClick \_ -> OpenItem item
    , HE.onKeyDown (HandleKeyDown idx)
    ]
    [ HH.span [ cls [ "item-icon" ], HP.attr (HH.AttrName "style") itemIconStyle ] [ HH.text (getItemIcon item.itemType) ]
    , HH.span [ cls [ "item-name" ], HP.attr (HH.AttrName "style") itemNameStyle ] [ HH.text item.name ]
    , HH.span [ cls [ "item-info" ], HP.attr (HH.AttrName "style") itemInfoStyle ] [ HH.text (getItemInfo item) ]
    ]

renderEmptyState :: forall m. H.ComponentHTML Action Slots m
renderEmptyState =
  HH.div
    [ cls [ "empty-state" ]
    , HP.attr (HH.AttrName "style") emptyStateStyle
    ]
    [ HH.p_ [ HH.text "No items in project" ]
    , HH.p [ cls [ "hint" ], HP.attr (HH.AttrName "style") hintStyle ] [ HH.text "Import footage or create compositions" ]
    ]

renderFooter :: forall m. State -> H.ComponentHTML Action Slots m
renderFooter state =
  case getSelectedItemDetails state of
    Just details ->
      HH.div
        [ cls [ "panel-footer" ]
        , HP.attr (HH.AttrName "style") footerStyle
        ]
        [ HH.div [ cls [ "item-details" ], HP.attr (HH.AttrName "style") itemDetailsStyle ]
            [ HH.span [ cls [ "detail-label" ], HP.attr (HH.AttrName "style") detailLabelStyle ] [ HH.text details.name ]
            , HH.span [ cls [ "detail-info" ], HP.attr (HH.AttrName "style") detailInfoStyle ] [ HH.text details.info ]
            ]
        ]
    Nothing -> HH.text ""

-- =============================================================================
--                                                                    // helpers
-- =============================================================================

getItemIcon :: ProjectItemType -> String
getItemIcon = case _ of
  ItemComposition -> "\x{25B6}"
  ItemFootage -> "\x{25A7}"
  ItemSolid -> "\x{25A0}"
  ItemAudio -> "\x{266A}"
  ItemFolder -> "\x{25A3}"
  ItemData -> "\x{229F}"

getItemInfo :: ProjectItem -> String
getItemInfo item =
  case item.itemType of
    ItemComposition -> formatDimensions item
    ItemFootage -> formatDimensions item
    ItemData -> formatDataInfo item
    _ -> ""

formatDimensions :: ProjectItem -> String
formatDimensions item =
  let
    dims = case Tuple item.width item.height of
      Tuple (Just w) (Just h) -> show w <> "\x{00D7}" <> show h
      _ -> ""
    fpsStr = case item.fps of
      Just f -> show f <> "fps"
      Nothing -> ""
    durStr = case Tuple item.duration item.fps of
      Tuple (Just d) (Just f) ->
        let secs = toNumber d / toNumber f
        in formatSecs secs <> "s"
      _ -> ""
    parts = Array.filter (\s -> s /= "") [dims, fpsStr, durStr]
  in
    String.joinWith " \x{2022} " parts

formatDataInfo :: ProjectItem -> String
formatDataInfo item =
  let
    dtype = fromMaybe "" item.dataType
    info = fromMaybe "" item.dataInfo
    parts = Array.filter (\s -> s /= "") [String.toUpper dtype, info]
  in
    String.joinWith " \x{2022} " parts

formatSecs :: Number -> String
formatSecs = Utils.formatFixed 1

toNumber :: Int -> Number
toNumber = Utils.toNumber

floor :: Number -> Int
floor = Utils.floor

-- =============================================================================
--                                                       // data // transformers
-- =============================================================================

getAllFolders :: State -> Array Folder
getAllFolders state =
  let
    compositionFolder =
      { id: "compositions"
      , name: "Compositions"
      , items: map compositionToItem state.input.compositions
      }
    footageFolder =
      { id: "footage"
      , name: "Footage"
      , items: state.input.footage
      }
    solidsFolder =
      { id: "solids"
      , name: "Solids"
      , items: state.input.solids
      }
  in
    [ compositionFolder, footageFolder, solidsFolder ] <> state.customFolders

compositionToItem :: CompositionInfo -> ProjectItem
compositionToItem comp =
  { id: comp.id
  , name: comp.name
  , itemType: ItemComposition
  , width: Just comp.width
  , height: Just comp.height
  , duration: Just comp.frameCount
  , fps: Just comp.fps
  , dataType: Nothing
  , dataInfo: Nothing
  }

getFilteredFolders :: State -> Array Folder
getFilteredFolders state =
  if String.null state.searchQuery
    then getAllFolders state
    else
      let
        query = String.toLower state.searchQuery
        filterFolder folder =
          let
            filtered = Array.filter (matchesSearch query) folder.items
            nameMatch = String.contains (String.Pattern query) (String.toLower folder.name)
          in
            if Array.null filtered && not nameMatch
              then Nothing
              else Just (folder { items = filtered })
      in
        Array.mapMaybe filterFolder (getAllFolders state)

filterBySearch :: String -> Array ProjectItem -> Array ProjectItem
filterBySearch query items =
  if String.null query
    then items
    else
      let q = String.toLower query
      in Array.filter (matchesSearch q) items

matchesSearch :: String -> ProjectItem -> Boolean
matchesSearch query item =
  String.contains (String.Pattern query) (String.toLower item.name)

getRootItems :: State -> Array ProjectItem
getRootItems _state = []  -- No root items outside folders for now

getAllItems :: State -> Array ProjectItem
getAllItems state =
  let
    folders = getAllFolders state
    folderItems = Array.concatMap _.items folders
  in
    folderItems <> getRootItems state

getSelectedPreview :: State -> Maybe SelectedPreview
getSelectedPreview state =
  case state.selectedItem of
    Nothing -> Nothing
    Just itemId ->
      let
        allItems = getAllItems state
        maybeItem = Array.find (\i -> i.id == itemId) allItems
      in
        case maybeItem of
          Nothing -> Nothing
          Just item ->
            Just
              { previewType: show item.itemType
              , name: item.name
              , details: getItemInfo item
              , icon: getPreviewIcon item.itemType
              , url: Nothing
              }

getPreviewIcon :: ProjectItemType -> String
getPreviewIcon = case _ of
  ItemComposition -> "\x{1F3AC}"
  ItemFootage -> "\x{1F5BC}"
  ItemSolid -> "\x{2B1C}"
  ItemAudio -> "\x{1F50A}"
  ItemFolder -> "\x{1F4C1}"
  ItemData -> "\x{1F4CA}"

getSelectedItemDetails :: State -> Maybe { name :: String, info :: String }
getSelectedItemDetails state =
  case state.selectedItem of
    Nothing -> Nothing
    Just itemId ->
      let
        allItems = getAllItems state
        maybeItem = Array.find (\i -> i.id == itemId) allItems
      in
        case maybeItem of
          Nothing -> Nothing
          Just item ->
            Just { name: item.name, info: getItemInfo item }

-- =============================================================================
--                                                                     // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1, #0f0f0f); " <>
  "color: var(--lattice-text-primary, #e0e0e0); font-size: 13px;"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 8px 10px; background: var(--lattice-surface-2, #161616); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);"

titleStyle :: String
titleStyle =
  "font-weight: 600; font-size: 13px; color: var(--lattice-text-primary, #E5E5E5);"

headerActionsStyle :: String
headerActionsStyle =
  "display: flex; gap: 6px;"

actionBtnStyle :: String
actionBtnStyle =
  "width: 28px; height: 28px; padding: 0; border: none; " <>
  "background: transparent; color: var(--lattice-text-muted, #6B7280); " <>
  "border-radius: 4px; cursor: pointer; font-size: 16px; " <>
  "display: flex; align-items: center; justify-content: center;"

dropdownContainerStyle :: String
dropdownContainerStyle =
  "position: relative;"

dropdownMenuStyle :: String
dropdownMenuStyle =
  "position: absolute; top: 100%; right: 0; " <>
  "background: var(--lattice-surface-2, #161616); " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "border-radius: 6px; box-shadow: 0 4px 16px rgba(0, 0, 0, 0.5); " <>
  "z-index: 1000; min-width: 200px; white-space: nowrap; padding: 8px 0;"

menuItemStyle :: String
menuItemStyle =
  "display: flex; align-items: center; justify-content: flex-start; " <>
  "gap: 12px; width: 100%; padding: 10px 16px; border: none; " <>
  "background: transparent; color: var(--lattice-text-primary, #e0e0e0); " <>
  "font-size: 13px; text-align: left; cursor: pointer; line-height: 1.4;"

menuIconStyle :: String
menuIconStyle =
  "display: inline-flex; align-items: center; justify-content: center; " <>
  "width: 20px; font-size: 14px; flex-shrink: 0;"

menuDividerStyle :: String
menuDividerStyle =
  "border: none; border-top: 1px solid var(--lattice-border-subtle, #1a1a1a); margin: 8px 12px;"

searchBarStyle :: String
searchBarStyle =
  "padding: 6px 8px; background: var(--lattice-surface-2, #161616); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);"

searchInputStyle :: String
searchInputStyle =
  "width: 100%; padding: 5px 8px; " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "background: var(--lattice-surface-0, #080808); " <>
  "color: var(--lattice-text-primary, #e0e0e0); " <>
  "border-radius: 4px; font-size: 13px;"

previewAreaStyle :: String
previewAreaStyle =
  "background: var(--lattice-surface-0, #080808); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "padding: 16px; display: flex; flex-direction: column; " <>
  "gap: 10px; align-items: center;"

previewThumbnailStyle :: String
previewThumbnailStyle =
  "width: 100%; max-width: 200px; height: 150px; " <>
  "background: var(--lattice-void, #0a0a0a); " <>
  "border-radius: 6px; overflow: hidden; " <>
  "display: flex; align-items: center; justify-content: center; " <>
  "flex-shrink: 0; border: 1px solid var(--lattice-border-subtle, #1a1a1a);"

previewPlaceholderStyle :: String
previewPlaceholderStyle =
  "display: flex; align-items: center; justify-content: center; " <>
  "width: 100%; height: 100%; font-size: 24px; opacity: 0.6;"

previewInfoStyle :: String
previewInfoStyle =
  "text-align: center; width: 100%;"

previewNameStyle :: String
previewNameStyle =
  "font-size: 12px; font-weight: 500; " <>
  "color: var(--lattice-text-primary, #e0e0e0); " <>
  "white-space: nowrap; overflow: hidden; text-overflow: ellipsis;"

previewDetailsStyle :: String
previewDetailsStyle =
  "font-size: 11px; color: var(--lattice-text-muted, #6B7280); margin-top: 4px;"

contentStyle :: String
contentStyle =
  "flex: 1; overflow-y: auto;"

folderTreeStyle :: String
folderTreeStyle =
  "padding: 4px 0;"

folderItemStyle :: String
folderItemStyle =
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);"

folderHeaderStyle :: Boolean -> String
folderHeaderStyle isSelected =
  let
    baseStyle = "display: flex; align-items: center; gap: 6px; " <>
                "padding: 8px 10px; cursor: pointer; user-select: none;"
    selectedStyle = if isSelected
      then "background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15)); " <>
           "border-left: 3px solid var(--lattice-accent, #8B5CF6);"
      else ""
  in
    baseStyle <> selectedStyle

expandIconStyle :: String
expandIconStyle =
  "width: 12px; font-size: 11px; color: var(--lattice-text-secondary, #9CA3AF);"

folderIconStyle :: String
folderIconStyle =
  "font-size: 12px;"

folderNameStyle :: String
folderNameStyle =
  "flex: 1; color: var(--lattice-text-primary, #E5E5E5); font-weight: 500;"

itemCountStyle :: String
itemCountStyle =
  "font-size: 11px; color: var(--lattice-text-muted, #6B7280); " <>
  "background: var(--lattice-surface-3, #1e1e1e); " <>
  "padding: 1px 6px; border-radius: 8px;"

folderContentsStyle :: String
folderContentsStyle =
  "background: var(--lattice-surface-0, #080808);"

projectItemStyle :: Boolean -> String
projectItemStyle isSelected =
  let
    baseStyle = "display: flex; align-items: center; gap: 8px; " <>
                "padding: 8px 12px 8px 28px; cursor: pointer; " <>
                "user-select: none; border-radius: 4px; margin: 2px 4px;"
    selectedStyle = if isSelected
      then "background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15)); " <>
           "border-left: 3px solid var(--lattice-accent, #8B5CF6);"
      else ""
  in
    baseStyle <> selectedStyle

itemIconStyle :: String
itemIconStyle =
  "font-size: 12px; width: 18px; text-align: center;"

itemNameStyle :: String
itemNameStyle =
  "flex: 1; overflow: hidden; text-overflow: ellipsis; " <>
  "white-space: nowrap; color: var(--lattice-text-primary, #E5E5E5);"

itemInfoStyle :: String
itemInfoStyle =
  "font-size: 11px; color: var(--lattice-text-muted, #6B7280);"

emptyStateStyle :: String
emptyStateStyle =
  "padding: 24px; text-align: center; color: var(--lattice-text-muted, #6B7280);"

hintStyle :: String
hintStyle =
  "font-size: 12px; margin-top: 4px;"

footerStyle :: String
footerStyle =
  "padding: 8px 12px; background: var(--lattice-surface-2, #161616); " <>
  "border-top: 1px solid var(--lattice-border-subtle, #1a1a1a);"

itemDetailsStyle :: String
itemDetailsStyle =
  "display: flex; justify-content: space-between; align-items: center;"

detailLabelStyle :: String
detailLabelStyle =
  "font-weight: 500;"

detailInfoStyle :: String
detailInfoStyle =
  "font-size: 12px; color: var(--lattice-text-muted, #6B7280);"

-- =============================================================================
--                                                                    // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input -> do
    H.modify_ _ { input = input }

  ToggleSearch -> do
    H.modify_ \s -> s { showSearch = not s.showSearch }

  ToggleNewMenu -> do
    H.modify_ \s -> s { showNewMenu = not s.showNewMenu }

  UpdateSearchQuery query -> do
    H.modify_ _ { searchQuery = query }

  SelectItem itemId -> do
    H.modify_ _ { selectedItem = Just itemId, showNewMenu = false }

  ToggleFolder folderId -> do
    H.modify_ \s ->
      if Array.elem folderId s.expandedFolders
        then s { expandedFolders = Array.filter (_ /= folderId) s.expandedFolders }
        else s { expandedFolders = s.expandedFolders <> [folderId] }

  OpenItem item -> do
    case item.itemType of
      ItemComposition -> H.raise (OpenComposition item.id)
      ItemFolder -> handleAction (ToggleFolder item.id)
      _ -> H.raise (CreateLayer item)

  HandleKeyDown _idx event -> do
    let key = KE.key event
    case key of
      "Enter" -> do
        state <- H.get
        case state.selectedItem of
          Nothing -> pure unit
          Just itemId -> do
            let allItems = getAllItems state
            case Array.find (\i -> i.id == itemId) allItems of
              Just item -> handleAction (OpenItem item)
              Nothing -> pure unit
      "ArrowDown" -> navigateItems 1
      "ArrowUp" -> navigateItems (-1)
      "ArrowRight" -> expandSelected
      "ArrowLeft" -> collapseSelected
      _ -> pure unit

  TriggerImport -> do
    H.modify_ _ { showNewMenu = false }
    H.raise ImportFile

  CreateCompositionAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise CreateComposition

  CreateFolderAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise CreateFolder

  CreateSolidAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise CreateSolid

  CreateTextAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise CreateText

  CreateSplineAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise CreateSpline

  CreateModelAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise CreateModel

  CreatePointCloudAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise CreatePointCloud

  OpenDecomposeAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise OpenDecomposeDialog

  OpenVectorizeAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise OpenVectorizeDialog

  CleanupAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise CleanupUnusedAssets

-- | Navigate items up or down
navigateItems :: forall m. MonadAff m => Int -> H.HalogenM State Action Slots Output m Unit
navigateItems delta = do
  state <- H.get
  let
    allItems = getAllItems state
    maybeIdx = case state.selectedItem of
      Nothing -> if delta > 0 then Just 0 else Nothing
      Just itemId -> Array.findIndex (\i -> i.id == itemId) allItems
    newIdx = case maybeIdx of
      Nothing -> 0
      Just idx -> max 0 (min (Array.length allItems - 1) (idx + delta))
  case Array.index allItems newIdx of
    Just item -> H.modify_ _ { selectedItem = Just item.id }
    Nothing -> pure unit

-- | Expand selected folder
expandSelected :: forall m. MonadAff m => H.HalogenM State Action Slots Output m Unit
expandSelected = do
  state <- H.get
  case state.selectedItem of
    Nothing -> pure unit
    Just itemId ->
      if not (Array.elem itemId state.expandedFolders)
        then H.modify_ \s -> s { expandedFolders = s.expandedFolders <> [itemId] }
        else pure unit

-- | Collapse selected folder
collapseSelected :: forall m. MonadAff m => H.HalogenM State Action Slots Output m Unit
collapseSelected = do
  state <- H.get
  case state.selectedItem of
    Nothing -> pure unit
    Just itemId ->
      if Array.elem itemId state.expandedFolders
        then H.modify_ \s -> s { expandedFolders = Array.filter (_ /= itemId) s.expandedFolders }
        else pure unit

-- =============================================================================
--                                                                    // queries
-- =============================================================================

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  RefreshItems next -> do
    pure (Just next)

  SetSelectedItem maybeId next -> do
    H.modify_ _ { selectedItem = maybeId }
    pure (Just next)
