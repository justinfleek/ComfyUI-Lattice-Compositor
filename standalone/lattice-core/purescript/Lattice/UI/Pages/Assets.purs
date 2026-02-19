-- | Assets Page Component
-- |
-- | Asset library and browser for the Lattice Compositor.
-- | Shows:
-- | - Asset categories (Footage, Audio, Images, Precomps)
-- | - Asset search
-- | - Import functionality
module Lattice.UI.Pages.Assets
  ( component
  ) where

import Prelude

import Data.Array (filter, length)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)

-- ============================================================
-- TYPES
-- ============================================================

data AssetType
  = Footage
  | Audio
  | Image
  | Precomp

derive instance eqAssetType :: Eq AssetType

type Asset =
  { id :: String
  , name :: String
  , assetType :: AssetType
  , path :: String
  , duration :: Number  -- for video/audio, 0 for images
  , size :: String      -- file size as string
  }

type State =
  { assets :: Array Asset
  , searchQuery :: String
  , selectedCategory :: AssetType
  , selectedAsset :: String  -- asset id or empty
  }

data Action
  = Initialize
  | SetCategory AssetType
  | SetSearch String
  | SelectAsset String
  | ImportAsset
  | DeleteAsset String

-- ============================================================
-- COMPONENT
-- ============================================================

component :: forall q i o m. MonadAff m => H.Component q i o m
component = H.mkComponent
  { initialState: const initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

initialState :: State
initialState =
  { assets: []  -- Empty library - user needs to import
  , searchQuery: ""
  , selectedCategory: Footage
  , selectedAsset: ""
  }

-- ============================================================
-- RENDER
-- ============================================================

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-page", "lattice-assets-page" ]
    , HP.attr (HH.AttrName "style") pageStyle
    ]
    [ HH.div
        [ cls [ "lattice-assets-container" ]
        , HP.attr (HH.AttrName "style") containerStyle
        ]
        [ -- Header
          renderHeader state
        
          -- Main content
        , HH.div 
            [ cls [ "lattice-assets-content" ]
            , HP.attr (HH.AttrName "style") contentStyle
            ]
            [ -- Sidebar with categories
              renderSidebar state
            
              -- Asset grid
            , renderAssetGrid state
            ]
        ]
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.header
    [ cls [ "lattice-assets-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.div [ cls [ "lattice-assets-title-section" ] ]
        [ HH.h1 
            [ HP.attr (HH.AttrName "style") titleStyle ]
            [ HH.text "Asset Library" ]
        , HH.span 
            [ HP.attr (HH.AttrName "style") countStyle ]
            [ HH.text $ show (length state.assets) <> " assets" ]
        ]
    , HH.div 
        [ cls [ "lattice-assets-actions" ]
        , HP.attr (HH.AttrName "style") actionsStyle
        ]
        [ -- Search input
          HH.div [ cls [ "lattice-search-wrapper" ], HP.attr (HH.AttrName "style") searchWrapperStyle ]
            [ HH.input
                [ cls [ "lattice-input" ]
                , HP.placeholder "Search assets..."
                , HP.value state.searchQuery
                , HP.attr (HH.AttrName "style") searchInputStyle
                , HE.onValueInput SetSearch
                ]
            ]
        , HH.button
            [ cls [ "lattice-btn", "lattice-btn-primary" ]
            , HE.onClick \_ -> ImportAsset
            ]
            [ HH.text "Import" ]
        ]
    ]

renderSidebar :: forall m. State -> H.ComponentHTML Action () m
renderSidebar state =
  HH.aside
    [ cls [ "lattice-assets-sidebar" ]
    , HP.attr (HH.AttrName "style") sidebarStyle
    ]
    [ HH.h3 
        [ HP.attr (HH.AttrName "style") sidebarTitleStyle ]
        [ HH.text "Categories" ]
    , HH.nav [ cls [ "lattice-category-nav" ] ]
        [ renderCategoryItem state Footage "Footage" (countByType state.assets Footage)
        , renderCategoryItem state Audio "Audio" (countByType state.assets Audio)
        , renderCategoryItem state Image "Images" (countByType state.assets Image)
        , renderCategoryItem state Precomp "Precomps" (countByType state.assets Precomp)
        ]
    ]

renderCategoryItem :: forall m. State -> AssetType -> String -> Int -> H.ComponentHTML Action () m
renderCategoryItem state category label count =
  let isActive = state.selectedCategory == category
  in HH.button
    [ cls [ "lattice-category-item" ]
    , HP.attr (HH.AttrName "style") (categoryItemStyle isActive)
    , HP.attr (HH.AttrName "data-active") (if isActive then "true" else "false")
    , HE.onClick \_ -> SetCategory category
    ]
    [ HH.span [ cls [ "lattice-category-icon" ] ] [ HH.text (categoryIcon category) ]
    , HH.span [ cls [ "lattice-category-label" ] ] [ HH.text label ]
    , HH.span 
        [ cls [ "lattice-category-count" ]
        , HP.attr (HH.AttrName "style") categoryCountStyle
        ] 
        [ HH.text $ show count ]
    ]

renderAssetGrid :: forall m. State -> H.ComponentHTML Action () m
renderAssetGrid state =
  let 
    filteredAssets = filterAssets state
  in HH.main
    [ cls [ "lattice-assets-grid-container" ]
    , HP.attr (HH.AttrName "style") gridContainerStyle
    ]
    [ if length filteredAssets == 0
        then renderEmptyState state
        else HH.div 
            [ cls [ "lattice-assets-grid" ]
            , HP.attr (HH.AttrName "style") gridStyle
            ]
            (map (renderAssetCard state) filteredAssets)
    ]

renderEmptyState :: forall m. State -> H.ComponentHTML Action () m
renderEmptyState state =
  HH.div 
    [ cls [ "lattice-empty-state" ]
    , HP.attr (HH.AttrName "style") emptyStateStyle
    ]
    [ HH.div 
        [ cls [ "lattice-empty-icon" ]
        , HP.attr (HH.AttrName "style") emptyIconStyle
        ]
        [ HH.text (categoryIcon state.selectedCategory) ]
    , HH.h3 
        [ HP.attr (HH.AttrName "style") emptyTitleStyle ]
        [ HH.text $ "No " <> categoryLabel state.selectedCategory ]
    , HH.p 
        [ HP.attr (HH.AttrName "style") emptyTextStyle ]
        [ HH.text "Import assets to get started" ]
    , HH.button
        [ cls [ "lattice-btn", "lattice-btn-primary" ]
        , HE.onClick \_ -> ImportAsset
        ]
        [ HH.text "Import Assets" ]
    ]

renderAssetCard :: forall m. State -> Asset -> H.ComponentHTML Action () m
renderAssetCard state asset =
  let isSelected = state.selectedAsset == asset.id
  in HH.div
    [ cls [ "lattice-asset-card" ]
    , HP.attr (HH.AttrName "style") (assetCardStyle isSelected)
    , HP.attr (HH.AttrName "data-selected") (if isSelected then "true" else "false")
    , HE.onClick \_ -> SelectAsset asset.id
    ]
    [ HH.div 
        [ cls [ "lattice-asset-thumb" ]
        , HP.attr (HH.AttrName "style") assetThumbStyle
        ]
        [ HH.text (categoryIcon asset.assetType) ]
    , HH.div [ cls [ "lattice-asset-info" ] ]
        [ HH.span 
            [ cls [ "lattice-asset-name" ]
            , HP.attr (HH.AttrName "style") assetNameStyle
            ]
            [ HH.text asset.name ]
        , HH.span 
            [ cls [ "lattice-asset-meta" ]
            , HP.attr (HH.AttrName "style") assetMetaStyle
            ]
            [ HH.text asset.size ]
        ]
    ]

-- ============================================================
-- HELPERS
-- ============================================================

filterAssets :: State -> Array Asset
filterAssets state =
  let 
    byCategory = filter (\a -> a.assetType == state.selectedCategory) state.assets
    bySearch = if state.searchQuery == ""
      then byCategory
      else filter (\a -> contains state.searchQuery a.name) byCategory
  in bySearch

contains :: String -> String -> Boolean
contains _ _ = true  -- Simplified - would use proper string search

countByType :: Array Asset -> AssetType -> Int
countByType assets assetType = length $ filter (\a -> a.assetType == assetType) assets

categoryIcon :: AssetType -> String
categoryIcon = case _ of
  Footage -> "🎬"
  Audio -> "🎵"
  Image -> "🖼"
  Precomp -> "📦"

categoryLabel :: AssetType -> String
categoryLabel = case _ of
  Footage -> "Footage"
  Audio -> "Audio"
  Image -> "Images"
  Precomp -> "Precomps"

-- ============================================================
-- ACTIONS
-- ============================================================

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  SetCategory category ->
    H.modify_ _ { selectedCategory = category, selectedAsset = "" }
  
  SetSearch query ->
    H.modify_ _ { searchQuery = query }
  
  SelectAsset assetId ->
    H.modify_ _ { selectedAsset = assetId }
  
  ImportAsset -> 
    pure unit  -- Would open file picker
  
  DeleteAsset _ ->
    pure unit  -- Would remove asset

-- ============================================================
-- STYLES
-- ============================================================

pageStyle :: String
pageStyle =
  "min-height: 100vh; background: var(--lattice-void);"

containerStyle :: String
containerStyle =
  "height: 100vh; display: flex; flex-direction: column;"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: var(--lattice-space-4) var(--lattice-space-6); " <>
  "background: var(--lattice-surface-1); border-bottom: 1px solid var(--lattice-border-subtle);"

titleStyle :: String
titleStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-xl); " <>
  "font-weight: var(--lattice-font-semibold); margin: 0;"

countStyle :: String
countStyle =
  "color: var(--lattice-text-muted); font-size: var(--lattice-text-sm); display: block;"

actionsStyle :: String
actionsStyle =
  "display: flex; gap: var(--lattice-space-3); align-items: center;"

searchWrapperStyle :: String
searchWrapperStyle =
  "position: relative;"

searchInputStyle :: String
searchInputStyle =
  "width: 250px;"

contentStyle :: String
contentStyle =
  "flex: 1; display: flex; overflow: hidden;"

sidebarStyle :: String
sidebarStyle =
  "width: 200px; background: var(--lattice-surface-1); " <>
  "border-right: 1px solid var(--lattice-border-subtle); " <>
  "padding: var(--lattice-space-4);"

sidebarTitleStyle :: String
sidebarTitleStyle =
  "color: var(--lattice-text-muted); font-size: var(--lattice-text-xs); " <>
  "text-transform: uppercase; letter-spacing: 0.5px; margin: 0 0 var(--lattice-space-3);"

categoryItemStyle :: Boolean -> String
categoryItemStyle isActive =
  "width: 100%; display: flex; align-items: center; gap: var(--lattice-space-2); " <>
  "padding: var(--lattice-space-2) var(--lattice-space-3); " <>
  "border-radius: var(--lattice-radius-md); border: none; cursor: pointer; " <>
  "text-align: left; margin-bottom: var(--lattice-space-1); " <>
  "background: " <> (if isActive then "var(--lattice-accent-muted)" else "transparent") <> "; " <>
  "color: " <> (if isActive then "var(--lattice-accent)" else "var(--lattice-text-secondary)") <> "; " <>
  "font-weight: " <> (if isActive then "var(--lattice-font-medium)" else "var(--lattice-font-normal)") <> ";"

categoryCountStyle :: String
categoryCountStyle =
  "margin-left: auto; font-size: var(--lattice-text-xs); opacity: 0.6;"

gridContainerStyle :: String
gridContainerStyle =
  "flex: 1; overflow-y: auto; padding: var(--lattice-space-4);"

gridStyle :: String
gridStyle =
  "display: grid; grid-template-columns: repeat(auto-fill, minmax(160px, 1fr)); " <>
  "gap: var(--lattice-space-3);"

emptyStateStyle :: String
emptyStateStyle =
  "display: flex; flex-direction: column; align-items: center; justify-content: center; " <>
  "height: 100%; text-align: center; padding: var(--lattice-space-8);"

emptyIconStyle :: String
emptyIconStyle =
  "font-size: 64px; margin-bottom: var(--lattice-space-4); opacity: 0.5;"

emptyTitleStyle :: String
emptyTitleStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-lg); " <>
  "margin: 0 0 var(--lattice-space-2);"

emptyTextStyle :: String
emptyTextStyle =
  "color: var(--lattice-text-muted); margin: 0 0 var(--lattice-space-4);"

assetCardStyle :: Boolean -> String
assetCardStyle isSelected =
  "background: var(--lattice-surface-1); border-radius: var(--lattice-radius-lg); " <>
  "overflow: hidden; cursor: pointer; transition: all var(--lattice-transition-fast); " <>
  "border: 2px solid " <> (if isSelected then "var(--lattice-accent)" else "transparent") <> ";"

assetThumbStyle :: String
assetThumbStyle =
  "aspect-ratio: 16/9; background: var(--lattice-surface-0); " <>
  "display: flex; align-items: center; justify-content: center; font-size: 32px;"

assetNameStyle :: String
assetNameStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-sm); " <>
  "font-weight: var(--lattice-font-medium); display: block; " <>
  "padding: var(--lattice-space-2) var(--lattice-space-2) 0; " <>
  "white-space: nowrap; overflow: hidden; text-overflow: ellipsis;"

assetMetaStyle :: String
assetMetaStyle =
  "color: var(--lattice-text-muted); font-size: var(--lattice-text-xs); " <>
  "display: block; padding: 0 var(--lattice-space-2) var(--lattice-space-2);"
