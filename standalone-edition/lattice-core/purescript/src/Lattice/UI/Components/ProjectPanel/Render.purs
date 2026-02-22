-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | ProjectPanel Render
-- |
-- | Render functions for project panel UI.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.ProjectPanel.Render
  ( render
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

import Lattice.UI.Core (cls)
import Lattice.UI.Components.ProjectPanel.Types
  ( State
  , Action(..)
  , Slots
  , ProjectItem
  , ProjectItemType(..)
  , Folder
  )
import Lattice.UI.Components.ProjectPanel.Styles as S
import Lattice.UI.Components.ProjectPanel.Helpers
  ( getFilteredFolders
  , filterBySearch
  , getRootItems
  , getAllItems
  , getSelectedPreview
  , getSelectedItemDetails
  , getItemInfo
  , getItemIcon
  )

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // main render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "project-panel" ]
    , HP.attr (HH.AttrName "style") S.panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , ARIA.label "Project"
    ]
    [ renderHeader state
    , if state.showSearch then renderSearchBar state else HH.text ""
    , renderPreviewArea state
    , renderContent state
    , renderFooter state
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                // header
-- ════════════════════════════════════════════════════════════════════════════

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "panel-header" ]
    , HP.attr (HH.AttrName "style") S.headerStyle
    ]
    [ HH.span
        [ cls [ "panel-title" ]
        , HP.attr (HH.AttrName "style") S.titleStyle
        ]
        [ HH.text "Project" ]
    , HH.div
        [ cls [ "header-actions" ]
        , HP.attr (HH.AttrName "style") S.headerActionsStyle
        ]
        [ HH.button
            [ cls [ "action-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Import File (Ctrl+I)"
            , HP.attr (HH.AttrName "style") S.actionBtnStyle
            , HE.onClick \_ -> TriggerImport
            ]
            [ HH.text "[I]" ]
        , renderNewMenu state
        , HH.button
            [ cls [ "action-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Search"
            , HP.attr (HH.AttrName "style") S.actionBtnStyle
            , HE.onClick \_ -> ToggleSearch
            ]
            [ HH.text "[S]" ]
        ]
    ]

renderNewMenu :: forall m. State -> H.ComponentHTML Action Slots m
renderNewMenu state =
  HH.div
    [ cls [ "dropdown-container" ]
    , HP.attr (HH.AttrName "style") S.dropdownContainerStyle
    ]
    [ HH.button
        [ cls [ "action-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.title "New Item"
        , HP.attr (HH.AttrName "style") S.actionBtnStyle
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
    , HP.attr (HH.AttrName "style") S.dropdownMenuStyle
    , HP.attr (HH.AttrName "role") "menu"
    ]
    [ menuItem "[C]" "New Composition" CreateCompositionAction
    , menuItem "[D]" "New Folder" CreateFolderAction
    , menuDivider
    , menuItem "[S]" "New Solid" CreateSolidAction
    , menuItem "[T]" "New Text" CreateTextAction
    , menuItem "[~]" "New Spline" CreateSplineAction
    , menuItem "[3D]" "New 3D Model" CreateModelAction
    , menuItem "[*]" "New Point Cloud" CreatePointCloudAction
    , menuDivider
    , menuItem "[AI]" "AI Layer Decompose" OpenDecomposeAction
    , menuItem "[V]" "Vectorize Image" OpenVectorizeAction
    , menuDivider
    , menuItem "[X]" "Remove Unused Assets" CleanupAction
    ]

menuItem :: forall m. String -> String -> Action -> H.ComponentHTML Action Slots m
menuItem icon labelText action =
  HH.button
    [ cls [ "menu-item" ]
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "style") S.menuItemStyle
    , HP.attr (HH.AttrName "role") "menuitem"
    , HE.onClick \_ -> action
    ]
    [ HH.span [ cls [ "menu-icon" ], HP.attr (HH.AttrName "style") S.menuIconStyle ] [ HH.text icon ]
    , HH.span_ [ HH.text labelText ]
    ]

menuDivider :: forall m. H.ComponentHTML Action Slots m
menuDivider =
  HH.hr [ cls [ "menu-divider" ], HP.attr (HH.AttrName "style") S.menuDividerStyle ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // search bar
-- ════════════════════════════════════════════════════════════════════════════

renderSearchBar :: forall m. State -> H.ComponentHTML Action Slots m
renderSearchBar state =
  HH.div
    [ cls [ "search-bar" ]
    , HP.attr (HH.AttrName "style") S.searchBarStyle
    ]
    [ HH.input
        [ HP.type_ HP.InputText
        , HP.placeholder "Search project..."
        , HP.value state.searchQuery
        , cls [ "search-input" ]
        , HP.attr (HH.AttrName "style") S.searchInputStyle
        , HE.onValueInput UpdateSearchQuery
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // preview area
-- ════════════════════════════════════════════════════════════════════════════

renderPreviewArea :: forall m. State -> H.ComponentHTML Action Slots m
renderPreviewArea state =
  case getSelectedPreview state of
    Just preview ->
      HH.div
        [ cls [ "preview-area" ]
        , HP.attr (HH.AttrName "style") S.previewAreaStyle
        ]
        [ HH.div
            [ cls [ "preview-thumbnail" ]
            , HP.attr (HH.AttrName "style") S.previewThumbnailStyle
            ]
            [ HH.div
                [ cls [ "preview-placeholder" ]
                , HP.attr (HH.AttrName "style") S.previewPlaceholderStyle
                ]
                [ HH.span [ cls [ "preview-icon" ] ] [ HH.text preview.icon ] ]
            ]
        , HH.div
            [ cls [ "preview-info" ]
            , HP.attr (HH.AttrName "style") S.previewInfoStyle
            ]
            [ HH.div
                [ cls [ "preview-name" ]
                , HP.attr (HH.AttrName "style") S.previewNameStyle
                ]
                [ HH.text preview.name ]
            , HH.div
                [ cls [ "preview-details" ]
                , HP.attr (HH.AttrName "style") S.previewDetailsStyle
                ]
                [ HH.text preview.details ]
            ]
        ]
    Nothing -> HH.text ""

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // content
-- ════════════════════════════════════════════════════════════════════════════

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "panel-content" ]
    , HP.attr (HH.AttrName "style") S.contentStyle
    ]
    [ HH.div
        [ cls [ "folder-tree" ]
        , HP.attr (HH.AttrName "style") S.folderTreeStyle
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
    , HP.attr (HH.AttrName "style") S.folderItemStyle
    , HP.attr (HH.AttrName "role") "treeitem"
    , ARIA.expanded (show isExpanded)
    ]
    [ HH.div
        [ cls [ "folder-header" ]
        , HP.attr (HH.AttrName "style") (S.folderHeaderStyle (state.selectedItem == Just folder.id))
        , HP.tabIndex (if idx == 0 then 0 else (-1))
        , HE.onClick \_ -> SelectItem folder.id
        , HE.onDoubleClick \_ -> ToggleFolder folder.id
        , HE.onKeyDown (HandleKeyDown idx)
        ]
        [ HH.span
            [ cls [ "expand-icon" ]
            , HP.attr (HH.AttrName "style") S.expandIconStyle
            , HE.onClick \_ -> ToggleFolder folder.id
            ]
            [ HH.text (if isExpanded then "v" else ">") ]
        , HH.span [ cls [ "folder-icon" ], HP.attr (HH.AttrName "style") S.folderIconStyle ] [ HH.text "[D]" ]
        , HH.span [ cls [ "folder-name" ], HP.attr (HH.AttrName "style") S.folderNameStyle ] [ HH.text folder.name ]
        , HH.span [ cls [ "item-count" ], HP.attr (HH.AttrName "style") S.itemCountStyle ] [ HH.text (show (Array.length items)) ]
        ]
    , if isExpanded
        then HH.div
              [ cls [ "folder-contents" ]
              , HP.attr (HH.AttrName "style") S.folderContentsStyle
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
    , HP.attr (HH.AttrName "style") (S.projectItemStyle isSelected)
    , HP.attr (HH.AttrName "role") "treeitem"
    , HP.attr (HH.AttrName "draggable") "true"
    , HP.tabIndex (if idx == 0 then 0 else (-1))
    , ARIA.selected (show isSelected)
    , HP.attr (HH.AttrName "data-state") (if isSelected then "selected" else "unselected")
    , HE.onClick \_ -> SelectItem item.id
    , HE.onDoubleClick \_ -> OpenItem item
    , HE.onKeyDown (HandleKeyDown idx)
    ]
    [ HH.span [ cls [ "item-icon" ], HP.attr (HH.AttrName "style") S.itemIconStyle ] [ HH.text (getItemIcon item.itemType) ]
    , HH.span [ cls [ "item-name" ], HP.attr (HH.AttrName "style") S.itemNameStyle ] [ HH.text item.name ]
    , HH.span [ cls [ "item-info" ], HP.attr (HH.AttrName "style") S.itemInfoStyle ] [ HH.text (getItemInfo item) ]
    ]

renderEmptyState :: forall m. H.ComponentHTML Action Slots m
renderEmptyState =
  HH.div
    [ cls [ "empty-state" ]
    , HP.attr (HH.AttrName "style") S.emptyStateStyle
    ]
    [ HH.p_ [ HH.text "No items in project" ]
    , HH.p [ cls [ "hint" ], HP.attr (HH.AttrName "style") S.hintStyle ] [ HH.text "Import footage or create compositions" ]
    ]

renderFooter :: forall m. State -> H.ComponentHTML Action Slots m
renderFooter state =
  case getSelectedItemDetails state of
    Just details ->
      HH.div
        [ cls [ "panel-footer" ]
        , HP.attr (HH.AttrName "style") S.footerStyle
        ]
        [ HH.div [ cls [ "item-details" ], HP.attr (HH.AttrName "style") S.itemDetailsStyle ]
            [ HH.span [ cls [ "detail-label" ], HP.attr (HH.AttrName "style") S.detailLabelStyle ] [ HH.text details.name ]
            , HH.span [ cls [ "detail-info" ], HP.attr (HH.AttrName "style") S.detailInfoStyle ] [ HH.text details.info ]
            ]
        ]
    Nothing -> HH.text ""
