-- | Font Picker Dialog
-- |
-- | Dialog for selecting fonts from web-safe, Google Fonts, and system fonts.
-- | Features category-based organization, search, and live preview.
-- |
-- | System F/Omega: FontPicker = Categories × Search × Preview → FontFamily
module Lattice.UI.Components.FontPicker
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..), contains, toLower)
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

type Font =
  { family :: String
  , source :: String  -- "web-safe", "google", "system"
  }

type FontCategory =
  { name :: String
  , fonts :: Array Font
  }

type Input =
  { visible :: Boolean
  , currentFont :: String
  }

data Output
  = Selected String  -- Font family
  | Cancelled

data Query a
  = Close a
  | Open a

type Slot id = H.Slot Query Output id

type State =
  { visible :: Boolean
  , currentFont :: String
  , selectedFont :: String
  , searchQuery :: String
  , expandedCategories :: Set String
  , previewText :: String
  }

data Action
  = Initialize
  | Receive Input
  | HandleKeyDown KeyboardEvent
  | UpdateSearch String
  | ToggleCategory String
  | SelectFont String
  | UpdatePreviewText String
  | Confirm
  | Cancel

-- ═══════════════════════════════════════════════════════════════════════════
--                                                            // font // data
-- ═══════════════════════════════════════════════════════════════════════════

fontCategories :: Array FontCategory
fontCategories =
  [ { name: "Web Safe"
    , fonts:
        [ { family: "Arial", source: "web-safe" }
        , { family: "Helvetica", source: "web-safe" }
        , { family: "Georgia", source: "web-safe" }
        , { family: "Times New Roman", source: "web-safe" }
        , { family: "Courier New", source: "web-safe" }
        , { family: "Verdana", source: "web-safe" }
        , { family: "Tahoma", source: "web-safe" }
        , { family: "Trebuchet MS", source: "web-safe" }
        , { family: "Impact", source: "web-safe" }
        , { family: "Comic Sans MS", source: "web-safe" }
        ]
    }
  , { name: "Sans Serif"
    , fonts:
        [ { family: "Roboto", source: "google" }
        , { family: "Open Sans", source: "google" }
        , { family: "Lato", source: "google" }
        , { family: "Montserrat", source: "google" }
        , { family: "Poppins", source: "google" }
        , { family: "Inter", source: "google" }
        , { family: "Nunito", source: "google" }
        , { family: "Raleway", source: "google" }
        , { family: "Work Sans", source: "google" }
        , { family: "Outfit", source: "google" }
        ]
    }
  , { name: "Serif"
    , fonts:
        [ { family: "Playfair Display", source: "google" }
        , { family: "Merriweather", source: "google" }
        , { family: "Lora", source: "google" }
        , { family: "PT Serif", source: "google" }
        , { family: "Libre Baskerville", source: "google" }
        , { family: "Source Serif Pro", source: "google" }
        , { family: "Crimson Text", source: "google" }
        , { family: "Cormorant Garamond", source: "google" }
        ]
    }
  , { name: "Display"
    , fonts:
        [ { family: "Bebas Neue", source: "google" }
        , { family: "Oswald", source: "google" }
        , { family: "Anton", source: "google" }
        , { family: "Righteous", source: "google" }
        , { family: "Staatliches", source: "google" }
        , { family: "Abril Fatface", source: "google" }
        , { family: "Alfa Slab One", source: "google" }
        , { family: "Bungee", source: "google" }
        ]
    }
  , { name: "Monospace"
    , fonts:
        [ { family: "Fira Code", source: "google" }
        , { family: "JetBrains Mono", source: "google" }
        , { family: "Source Code Pro", source: "google" }
        , { family: "Roboto Mono", source: "google" }
        , { family: "IBM Plex Mono", source: "google" }
        , { family: "Space Mono", source: "google" }
        ]
    }
  , { name: "Handwriting"
    , fonts:
        [ { family: "Dancing Script", source: "google" }
        , { family: "Pacifico", source: "google" }
        , { family: "Great Vibes", source: "google" }
        , { family: "Satisfy", source: "google" }
        , { family: "Sacramento", source: "google" }
        , { family: "Caveat", source: "google" }
        ]
    }
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
  , currentFont: input.currentFont
  , selectedFont: input.currentFont
  , searchQuery: ""
  , expandedCategories: Set.singleton "Web Safe"
  , previewText: "The quick brown fox jumps over the lazy dog"
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                   // render
-- ═══════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state
  | not state.visible = HH.text ""
  | otherwise =
      HH.div
        [ cls [ "lattice-fontpicker-overlay" ]
        , HP.attr (HH.AttrName "style") overlayStyle
        , ARIA.role "dialog"
        , ARIA.modal "true"
        , ARIA.labelledBy "fontpicker-title"
        , HE.onKeyDown HandleKeyDown
        , HP.tabIndex 0
        ]
        [ HH.div
            [ cls [ "lattice-fontpicker-container" ]
            , HP.attr (HH.AttrName "style") containerStyle
            ]
            [ renderHeader
            , renderSearchBar state
            , renderCategories state
            , renderPreview state
            , renderFooter state
            ]
        ]

renderHeader :: forall m. H.ComponentHTML Action () m
renderHeader =
  HH.div
    [ cls [ "picker-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.h3
        [ HP.id "fontpicker-title"
        , HP.attr (HH.AttrName "style") titleStyle
        ]
        [ HH.text "Select Font" ]
    , HH.button
        [ cls [ "close-btn" ]
        , HP.attr (HH.AttrName "style") closeButtonStyle
        , HP.title "Close"
        , ARIA.label "Close"
        , HE.onClick \_ -> Cancel
        ]
        [ HH.text "×" ]
    ]

renderSearchBar :: forall m. State -> H.ComponentHTML Action () m
renderSearchBar state =
  HH.div
    [ cls [ "search-row" ]
    , HP.attr (HH.AttrName "style") searchRowStyle
    ]
    [ HH.span
        [ cls [ "search-icon" ]
        , HP.attr (HH.AttrName "style") searchIconStyle
        ]
        [ HH.text "🔍" ]
    , HH.input
        [ cls [ "search-input" ]
        , HP.type_ HP.InputText
        , HP.placeholder "Search fonts..."
        , HP.value state.searchQuery
        , HP.autofocus true
        , HP.attr (HH.AttrName "style") searchInputStyle
        , HE.onValueInput UpdateSearch
        ]
    ]

renderCategories :: forall m. State -> H.ComponentHTML Action () m
renderCategories state =
  HH.div
    [ cls [ "font-categories" ]
    , HP.attr (HH.AttrName "style") categoriesStyle
    ]
    (map (renderCategory state) filteredCategories)
  where
    filteredCategories = filterCategories state.searchQuery fontCategories

renderCategory :: forall m. State -> FontCategory -> H.ComponentHTML Action () m
renderCategory state category =
  HH.div
    [ cls [ "font-category" ]
    , HP.attr (HH.AttrName "style") categoryStyle
    ]
    [ -- Category header
      HH.div
        [ cls [ "category-header" ]
        , HP.attr (HH.AttrName "style") categoryHeaderStyle
        , HE.onClick \_ -> ToggleCategory category.name
        ]
        [ HH.span
            [ HP.attr (HH.AttrName "style") chevronStyle ]
            [ HH.text (if isExpanded then "▼" else "▶") ]
        , HH.span [] [ HH.text category.name ]
        , HH.span
            [ cls [ "font-count" ]
            , HP.attr (HH.AttrName "style") fontCountStyle
            ]
            [ HH.text (show (Array.length category.fonts)) ]
        ]
    
    -- Fonts list (if expanded)
    , if isExpanded
        then HH.div
          [ cls [ "category-fonts" ]
          , HP.attr (HH.AttrName "style") categoryFontsStyle
          ]
          (map (renderFont state) category.fonts)
        else HH.text ""
    ]
  where
    isExpanded = Set.member category.name state.expandedCategories

renderFont :: forall m. State -> Font -> H.ComponentHTML Action () m
renderFont state font =
  HH.div
    [ cls [ "font-item" ]
    , HP.attr (HH.AttrName "style") (fontItemStyle isSelected)
    , HE.onClick \_ -> SelectFont font.family
    ]
    [ HH.span
        [ cls [ "font-preview" ]
        , HP.attr (HH.AttrName "style") (fontPreviewStyle font.family)
        ]
        [ HH.text font.family ]
    , HH.span
        [ cls [ "font-source" ]
        , HP.attr (HH.AttrName "style") fontSourceStyle
        ]
        [ HH.text font.source ]
    ]
  where
    isSelected = state.selectedFont == font.family

renderPreview :: forall m. State -> H.ComponentHTML Action () m
renderPreview state =
  HH.div
    [ cls [ "preview-section" ]
    , HP.attr (HH.AttrName "style") previewSectionStyle
    ]
    [ HH.label
        [ HP.attr (HH.AttrName "style") previewLabelStyle ]
        [ HH.text "Preview:" ]
    , HH.div
        [ cls [ "preview-text" ]
        , HP.attr (HH.AttrName "style") (previewTextStyle state.selectedFont)
        ]
        [ HH.text state.previewText ]
    , HH.input
        [ cls [ "preview-input" ]
        , HP.type_ HP.InputText
        , HP.value state.previewText
        , HP.placeholder "Type preview text..."
        , HP.attr (HH.AttrName "style") previewInputStyle
        , HE.onValueInput UpdatePreviewText
        ]
    ]

renderFooter :: forall m. State -> H.ComponentHTML Action () m
renderFooter state =
  HH.div
    [ cls [ "picker-actions" ]
    , HP.attr (HH.AttrName "style") footerStyle
    ]
    [ HH.button
        [ cls [ "cancel-btn" ]
        , HP.attr (HH.AttrName "style") cancelButtonStyle
        , HE.onClick \_ -> Cancel
        ]
        [ HH.text "Cancel" ]
    , HH.button
        [ cls [ "select-btn" ]
        , HP.attr (HH.AttrName "style") (selectButtonStyle hasSelection)
        , HP.disabled (not hasSelection)
        , HE.onClick \_ -> Confirm
        ]
        [ HH.text "Select" ]
    ]
  where
    hasSelection = state.selectedFont /= ""

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ═══════════════════════════════════════════════════════════════════════════

filterCategories :: String -> Array FontCategory -> Array FontCategory
filterCategories query categories
  | query == "" = categories
  | otherwise = Array.filter hasMatches (map filterCategory categories)
  where
    lowerQuery = toLower query
    
    filterCategory :: FontCategory -> FontCategory
    filterCategory cat =
      cat { fonts = Array.filter matchesFont cat.fonts }
    
    matchesFont :: Font -> Boolean
    matchesFont f = contains (Pattern lowerQuery) (toLower f.family)
    
    hasMatches :: FontCategory -> Boolean
    hasMatches cat = not (Array.null cat.fonts)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                         // inline // styles
-- ═══════════════════════════════════════════════════════════════════════════

overlayStyle :: String
overlayStyle =
  "position: fixed; inset: 0; " <>
  "background: rgba(0, 0, 0, 0.6); " <>
  "display: flex; align-items: center; justify-content: center; " <>
  "z-index: 1000;"

containerStyle :: String
containerStyle =
  "width: 480px; max-height: 80vh; " <>
  "background: #2a2a2a; border-radius: 8px; " <>
  "box-shadow: 0 8px 32px rgba(0, 0, 0, 0.4); " <>
  "display: flex; flex-direction: column;"

headerStyle :: String
headerStyle =
  "display: flex; align-items: center; justify-content: space-between; " <>
  "padding: 12px 16px; border-bottom: 1px solid #3d3d3d;"

titleStyle :: String
titleStyle =
  "margin: 0; font-size: 14px; font-weight: 500; color: #e0e0e0;"

closeButtonStyle :: String
closeButtonStyle =
  "padding: 4px 8px; border: none; background: transparent; " <>
  "color: #888; cursor: pointer; font-size: 18px;"

searchRowStyle :: String
searchRowStyle =
  "display: flex; align-items: center; padding: 12px 16px; " <>
  "border-bottom: 1px solid #3d3d3d; gap: 8px;"

searchIconStyle :: String
searchIconStyle =
  "color: #666; font-size: 14px;"

searchInputStyle :: String
searchInputStyle =
  "flex: 1; padding: 6px 8px; " <>
  "border: 1px solid #3d3d3d; background: #1e1e1e; " <>
  "color: #e0e0e0; border-radius: 4px; font-size: 13px;"

categoriesStyle :: String
categoriesStyle =
  "flex: 1; overflow-y: auto; min-height: 200px; max-height: 300px;"

categoryStyle :: String
categoryStyle =
  "border-bottom: 1px solid #333;"

categoryHeaderStyle :: String
categoryHeaderStyle =
  "display: flex; align-items: center; gap: 8px; " <>
  "padding: 8px 16px; cursor: pointer; " <>
  "background: #2d2d2d; font-size: 12px; font-weight: 500; color: #aaa;"

chevronStyle :: String
chevronStyle =
  "font-size: 10px; width: 16px;"

fontCountStyle :: String
fontCountStyle =
  "margin-left: auto; font-size: 12px; color: #666;"

categoryFontsStyle :: String
categoryFontsStyle =
  "background: #252525;"

fontItemStyle :: Boolean -> String
fontItemStyle isSelected =
  "display: flex; align-items: center; justify-content: space-between; " <>
  "padding: 8px 16px 8px 32px; cursor: pointer; " <>
  "transition: background 0.1s; " <>
  "background: " <> (if isSelected then "rgba(74, 144, 217, 0.2)" else "transparent") <> ";"

fontPreviewStyle :: String -> String
fontPreviewStyle fontFamily =
  "font-size: 14px; color: #e0e0e0; " <>
  "font-family: '" <> fontFamily <> "', sans-serif;"

fontSourceStyle :: String
fontSourceStyle =
  "font-size: 11px; color: #666; text-transform: uppercase; " <>
  "padding: 2px 4px; background: #333; border-radius: 2px;"

previewSectionStyle :: String
previewSectionStyle =
  "padding: 12px 16px; border-top: 1px solid #3d3d3d;"

previewLabelStyle :: String
previewLabelStyle =
  "display: block; font-size: 13px; color: #888; margin-bottom: 8px;"

previewTextStyle :: String -> String
previewTextStyle fontFamily =
  "font-size: 18px; color: #e0e0e0; " <>
  "padding: 12px; background: #1e1e1e; border-radius: 4px; " <>
  "margin-bottom: 8px; min-height: 48px; word-break: break-word; " <>
  "font-family: '" <> fontFamily <> "', sans-serif;"

previewInputStyle :: String
previewInputStyle =
  "width: 100%; padding: 6px 8px; " <>
  "border: 1px solid #3d3d3d; background: #1e1e1e; " <>
  "color: #e0e0e0; border-radius: 4px; font-size: 12px; " <>
  "box-sizing: border-box;"

footerStyle :: String
footerStyle =
  "display: flex; align-items: center; gap: 8px; " <>
  "padding: 12px 16px; border-top: 1px solid #3d3d3d; " <>
  "justify-content: flex-end;"

cancelButtonStyle :: String
cancelButtonStyle =
  "padding: 6px 16px; border: 1px solid #3d3d3d; " <>
  "background: transparent; color: #aaa; border-radius: 4px; " <>
  "font-size: 12px; cursor: pointer;"

selectButtonStyle :: Boolean -> String
selectButtonStyle enabled =
  "padding: 6px 16px; border: none; border-radius: 4px; " <>
  "font-size: 12px; " <>
  "background: " <> (if enabled then "#4a90d9" else "#333") <> "; " <>
  "color: " <> (if enabled then "#fff" else "#666") <> "; " <>
  "cursor: " <> (if enabled then "pointer" else "not-allowed") <> ";"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // actions
-- ═══════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    state <- H.get
    when (input.visible && not state.visible) do
      H.modify_ _
        { selectedFont = input.currentFont
        , searchQuery = ""
        , expandedCategories = Set.singleton "Web Safe"
        }
    H.modify_ _
      { visible = input.visible
      , currentFont = input.currentFont
      }
  
  HandleKeyDown event -> do
    let key = KE.key event
    when (key == "Escape") do
      H.raise Cancelled
    when (key == "Enter") do
      handleAction Confirm
  
  UpdateSearch query -> do
    H.modify_ _ { searchQuery = query }
  
  ToggleCategory name -> do
    state <- H.get
    let newExpanded =
          if Set.member name state.expandedCategories
            then Set.delete name state.expandedCategories
            else Set.insert name state.expandedCategories
    H.modify_ _ { expandedCategories = newExpanded }
  
  SelectFont family -> do
    H.modify_ _ { selectedFont = family }
  
  UpdatePreviewText text -> do
    H.modify_ _ { previewText = text }
  
  Confirm -> do
    state <- H.get
    when (state.selectedFont /= "") do
      H.raise (Selected state.selectedFont)
  
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
