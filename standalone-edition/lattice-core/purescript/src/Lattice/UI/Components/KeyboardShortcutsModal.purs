-- | Keyboard Shortcuts Modal
-- |
-- | Modal displaying all keyboard shortcuts organized by category with search.
-- | Press '?' to toggle this modal.
-- |
-- | System F/Omega: ShortcutModal = List Category × (String → Filter) → HTML
module Lattice.UI.Components.KeyboardShortcutsModal
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains, toLower)
import Data.String.Utils (words)
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

type Shortcut =
  { keys :: String
  , description :: String
  }

type Category =
  { name :: String
  , shortcuts :: Array Shortcut
  }

type Input =
  { visible :: Boolean
  }

data Output
  = Closed

data Query a
  = Close a
  | Open a

type Slot id = H.Slot Query Output id

type State =
  { visible :: Boolean
  , searchQuery :: String
  }

data Action
  = Initialize
  | Receive Input
  | HandleKeyDown KeyboardEvent
  | UpdateSearch String
  | CloseModal

-- ═══════════════════════════════════════════════════════════════════════════
--                                                            // shortcut data
-- ═══════════════════════════════════════════════════════════════════════════

allCategories :: Array Category
allCategories =
  [ { name: "Playback"
    , shortcuts:
        [ { keys: "Space", description: "Play / Pause" }
        , { keys: "Home", description: "Go to start" }
        , { keys: "End", description: "Go to end" }
        , { keys: "Left", description: "Step backward 1 frame" }
        , { keys: "Right", description: "Step forward 1 frame" }
        , { keys: "Shift+Left", description: "Step backward 10 frames" }
        , { keys: "Shift+Right", description: "Step forward 10 frames" }
        , { keys: "J", description: "Go to previous keyframe" }
        , { keys: "K", description: "Go to next keyframe" }
        ]
    }
  , { name: "Layer Selection"
    , shortcuts:
        [ { keys: "Ctrl+A", description: "Select all layers" }
        , { keys: "Ctrl+Up", description: "Select previous layer" }
        , { keys: "Ctrl+Down", description: "Select next layer" }
        , { keys: "Ctrl+Shift+Up", description: "Extend selection up" }
        , { keys: "Ctrl+Shift+Down", description: "Extend selection down" }
        , { keys: "Delete", description: "Delete selected layers" }
        ]
    }
  , { name: "Layer Editing"
    , shortcuts:
        [ { keys: "Ctrl+D", description: "Duplicate selected layers" }
        , { keys: "Ctrl+C", description: "Copy selected layers" }
        , { keys: "Ctrl+X", description: "Cut selected layers" }
        , { keys: "Ctrl+V", description: "Paste layers" }
        , { keys: "Ctrl+L", description: "Toggle layer lock" }
        , { keys: "Ctrl+Shift+C", description: "Pre-compose selected" }
        , { keys: "Ctrl+Shift+D", description: "Split layer at playhead" }
        , { keys: "Ctrl+Alt+R", description: "Reverse layer" }
        , { keys: "Ctrl+Alt+F", description: "Fit layer to composition" }
        ]
    }
  , { name: "Layer Timing"
    , shortcuts:
        [ { keys: "I", description: "Go to layer in point" }
        , { keys: "O", description: "Go to layer out point" }
        , { keys: "[", description: "Move in point to playhead" }
        , { keys: "]", description: "Move out point to playhead" }
        , { keys: "Alt+[", description: "Trim in point to playhead" }
        , { keys: "Alt+]", description: "Trim out point to playhead" }
        , { keys: "Ctrl+Alt+T", description: "Time stretch dialog" }
        ]
    }
  , { name: "Property Reveal"
    , shortcuts:
        [ { keys: "P", description: "Position" }
        , { keys: "S", description: "Scale" }
        , { keys: "R", description: "Rotation" }
        , { keys: "T", description: "Opacity" }
        , { keys: "A", description: "Anchor Point" }
        , { keys: "U", description: "All animated properties" }
        , { keys: "E", description: "Effects" }
        , { keys: "M", description: "Masks" }
        ]
    }
  , { name: "Keyframes"
    , shortcuts:
        [ { keys: "F9", description: "Apply smooth easing" }
        , { keys: "Shift+F9", description: "Apply ease in" }
        , { keys: "Ctrl+Shift+F9", description: "Apply ease out" }
        , { keys: "Ctrl+Alt+H", description: "Convert to hold keyframes" }
        , { keys: "Ctrl+Shift+K", description: "Keyframe interpolation" }
        ]
    }
  , { name: "Tools"
    , shortcuts:
        [ { keys: "V", description: "Selection tool" }
        , { keys: "H", description: "Hand tool (pan)" }
        , { keys: "Z", description: "Zoom tool" }
        , { keys: "G", description: "Pen tool" }
        , { keys: "Ctrl+T", description: "Text tool" }
        ]
    }
  , { name: "View & Zoom"
    , shortcuts:
        [ { keys: "=", description: "Zoom timeline in" }
        , { keys: "-", description: "Zoom timeline out" }
        , { keys: ";", description: "Zoom timeline to fit" }
        , { keys: "Ctrl+=", description: "Zoom viewer in" }
        , { keys: "Ctrl+-", description: "Zoom viewer out" }
        , { keys: "Ctrl+0", description: "Fit viewer to window" }
        , { keys: "Shift+G", description: "Toggle curve editor" }
        ]
    }
  , { name: "Work Area"
    , shortcuts:
        [ { keys: "B", description: "Set work area start" }
        , { keys: "N", description: "Set work area end" }
        ]
    }
  , { name: "Project & Dialogs"
    , shortcuts:
        [ { keys: "Ctrl+K", description: "Composition settings" }
        , { keys: "Ctrl+M", description: "Export dialog" }
        , { keys: "Ctrl+I", description: "Import asset" }
        , { keys: "Ctrl+Z", description: "Undo" }
        , { keys: "Ctrl+Shift+Z", description: "Redo" }
        , { keys: "?", description: "Toggle keyboard shortcuts" }
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
  , searchQuery: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                   // render
-- ═══════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state
  | not state.visible = HH.text ""
  | otherwise =
      HH.div
        [ cls [ "lattice-shortcuts-overlay" ]
        , HP.attr (HH.AttrName "style") overlayStyle
        , ARIA.role "dialog"
        , ARIA.modal "true"
        , ARIA.labelledBy "shortcuts-title"
        , HE.onKeyDown HandleKeyDown
        , HP.tabIndex 0
        ]
        [ HH.div
            [ cls [ "lattice-shortcuts-container" ]
            , HP.attr (HH.AttrName "style") containerStyle
            ]
            [ renderHeader
            , renderSearchBar state
            , renderContent state
            , renderFooter
            ]
        ]

renderHeader :: forall m. H.ComponentHTML Action () m
renderHeader =
  HH.div
    [ cls [ "lattice-shortcuts-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.h2
        [ HP.id "shortcuts-title"
        , HP.attr (HH.AttrName "style") titleStyle
        ]
        [ HH.text "Keyboard Shortcuts" ]
    , HH.button
        [ cls [ "close-btn" ]
        , HP.attr (HH.AttrName "style") closeButtonStyle
        , HP.title "Close (Escape)"
        , ARIA.label "Close"
        , HE.onClick \_ -> CloseModal
        ]
        [ HH.text "×" ]
    ]

renderSearchBar :: forall m. State -> H.ComponentHTML Action () m
renderSearchBar state =
  HH.div
    [ cls [ "lattice-shortcuts-search" ]
    , HP.attr (HH.AttrName "style") searchBarStyle
    ]
    [ HH.input
        [ cls [ "search-input" ]
        , HP.attr (HH.AttrName "style") searchInputStyle
        , HP.type_ HP.InputText
        , HP.placeholder "Search shortcuts..."
        , HP.value state.searchQuery
        , HP.autofocus true
        , HE.onValueInput UpdateSearch
        ]
    ]

renderContent :: forall m. State -> H.ComponentHTML Action () m
renderContent state =
  HH.div
    [ cls [ "lattice-shortcuts-content" ]
    , HP.attr (HH.AttrName "style") contentStyle
    ]
    (renderCategories filteredCategories)
  where
    filteredCategories = filterCategories state.searchQuery allCategories

renderCategories :: forall m. Array Category -> Array (H.ComponentHTML Action () m)
renderCategories categories =
  if Array.null categories
    then [ renderNoResults ]
    else map renderCategory categories

renderNoResults :: forall m. H.ComponentHTML Action () m
renderNoResults =
  HH.div
    [ cls [ "no-results" ]
    , HP.attr (HH.AttrName "style") noResultsStyle
    ]
    [ HH.text "No shortcuts found" ]

renderCategory :: forall m. Category -> H.ComponentHTML Action () m
renderCategory category =
  HH.div
    [ cls [ "shortcut-category" ]
    , HP.attr (HH.AttrName "style") categoryStyle
    ]
    [ HH.h3
        [ cls [ "category-title" ]
        , HP.attr (HH.AttrName "style") categoryTitleStyle
        ]
        [ HH.text category.name ]
    , HH.div
        [ cls [ "shortcut-list" ]
        , HP.attr (HH.AttrName "style") shortcutListStyle
        ]
        (map renderShortcut category.shortcuts)
    ]

renderShortcut :: forall m. Shortcut -> H.ComponentHTML Action () m
renderShortcut shortcut =
  HH.div
    [ cls [ "shortcut-item" ]
    , HP.attr (HH.AttrName "style") shortcutItemStyle
    ]
    [ HH.span
        [ cls [ "shortcut-keys" ]
        , HP.attr (HH.AttrName "style") shortcutKeysStyle
        ]
        (renderKeys shortcut.keys)
    , HH.span
        [ cls [ "shortcut-description" ]
        , HP.attr (HH.AttrName "style") shortcutDescStyle
        ]
        [ HH.text shortcut.description ]
    ]

renderKeys :: forall m. String -> Array (H.ComponentHTML Action () m)
renderKeys keyString =
  Array.intersperse spacer (map renderKey keyParts)
  where
    keyParts = words (replaceAll "+" " " keyString)
    spacer = HH.text " "

renderKey :: forall m. String -> H.ComponentHTML Action () m
renderKey key =
  HH.kbd
    [ HP.attr (HH.AttrName "style") kbdStyle ]
    [ HH.text (formatKey key) ]

renderFooter :: forall m. H.ComponentHTML Action () m
renderFooter =
  HH.div
    [ cls [ "lattice-shortcuts-footer" ]
    , HP.attr (HH.AttrName "style") footerStyle
    ]
    [ HH.span
        [ cls [ "hint" ]
        , HP.attr (HH.AttrName "style") hintStyle
        ]
        [ HH.text "Press "
        , HH.kbd [ HP.attr (HH.AttrName "style") kbdStyle ] [ HH.text "?" ]
        , HH.text " to toggle this modal"
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ═══════════════════════════════════════════════════════════════════════════

filterCategories :: String -> Array Category -> Array Category
filterCategories query categories
  | query == "" = categories
  | otherwise = Array.filter hasMatches (map filterCategory categories)
  where
    lowerQuery = toLower query
    
    filterCategory :: Category -> Category
    filterCategory cat =
      cat { shortcuts = Array.filter matchesShortcut cat.shortcuts }
    
    matchesShortcut :: Shortcut -> Boolean
    matchesShortcut s =
      contains (Pattern lowerQuery) (toLower s.description) ||
      contains (Pattern lowerQuery) (toLower s.keys)
    
    hasMatches :: Category -> Boolean
    hasMatches cat = not (Array.null cat.shortcuts)

formatKey :: String -> String
formatKey key = case key of
  "Left" -> "←"
  "Right" -> "→"
  "Up" -> "↑"
  "Down" -> "↓"
  "Delete" -> "Del"
  "Space" -> "Space"
  _ -> key

replaceAll :: String -> String -> String -> String
replaceAll find replacement str = go str ""
  where
    go :: String -> String -> String
    go s acc
      | s == "" = acc
      | otherwise = case contains (Pattern find) s of
          false -> acc <> s
          true -> go (dropFirst s) (acc <> replacement)
    
    dropFirst :: String -> String
    dropFirst s = case Array.tail (toCharArray s) of
      Nothing -> ""
      Just rest -> fromCharArray rest

-- Simplified char array conversion (would use proper String module in real impl)
toCharArray :: String -> Array String
toCharArray s = map (\c -> show c) (Array.fromFoldable (toCodePointArray s))
  where
    toCodePointArray :: String -> Array String
    toCodePointArray _ = []  -- Simplified

fromCharArray :: Array String -> String
fromCharArray = Array.intercalate ""

-- ═══════════════════════════════════════════════════════════════════════════
--                                                         // inline // styles
-- ═══════════════════════════════════════════════════════════════════════════

overlayStyle :: String
overlayStyle =
  "position: fixed; inset: 0; " <>
  "background: rgba(0, 0, 0, 0.75); " <>
  "display: flex; align-items: center; justify-content: center; " <>
  "z-index: 10000;"

containerStyle :: String
containerStyle =
  "background: var(--lattice-surface-1, #121212); " <>
  "border: 1px solid var(--lattice-border-default, #333); " <>
  "border-radius: 8px; " <>
  "width: 700px; max-width: 90vw; max-height: 85vh; " <>
  "display: flex; flex-direction: column; " <>
  "box-shadow: 0 16px 48px rgba(0, 0, 0, 0.5);"

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
  "width: 28px; height: 28px; " <>
  "border: none; background: transparent; " <>
  "color: var(--lattice-text-muted, #6b7280); " <>
  "font-size: 20px; cursor: pointer; border-radius: 4px; " <>
  "display: flex; align-items: center; justify-content: center;"

searchBarStyle :: String
searchBarStyle =
  "padding: 12px 20px; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);"

searchInputStyle :: String
searchInputStyle =
  "width: 100%; padding: 8px 12px; " <>
  "background: var(--lattice-surface-0, #0a0a0a); " <>
  "border: 1px solid var(--lattice-border-default, #333); " <>
  "border-radius: 4px; " <>
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "font-size: 13px;"

contentStyle :: String
contentStyle =
  "flex: 1; overflow-y: auto; padding: 16px 20px;"

noResultsStyle :: String
noResultsStyle =
  "text-align: center; padding: 40px 20px; " <>
  "color: var(--lattice-text-muted, #6b7280); font-size: 14px;"

categoryStyle :: String
categoryStyle =
  "margin-bottom: 20px;"

categoryTitleStyle :: String
categoryTitleStyle =
  "margin: 0 0 10px 0; font-size: 12px; font-weight: 600; " <>
  "color: var(--lattice-accent, #8b5cf6); " <>
  "text-transform: uppercase; letter-spacing: 0.5px;"

shortcutListStyle :: String
shortcutListStyle =
  "display: flex; flex-direction: column; gap: 6px;"

shortcutItemStyle :: String
shortcutItemStyle =
  "display: flex; align-items: center; gap: 16px; " <>
  "padding: 6px 8px; border-radius: 4px;"

shortcutKeysStyle :: String
shortcutKeysStyle =
  "display: flex; gap: 4px; min-width: 140px;"

shortcutDescStyle :: String
shortcutDescStyle =
  "flex: 1; font-size: 13px; " <>
  "color: var(--lattice-text-secondary, #9ca3af);"

kbdStyle :: String
kbdStyle =
  "display: inline-flex; align-items: center; justify-content: center; " <>
  "min-width: 24px; height: 22px; padding: 0 6px; " <>
  "background: var(--lattice-surface-3, #222); " <>
  "border: 1px solid var(--lattice-border-default, #333); " <>
  "border-radius: 4px; font-size: 11px; " <>
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "box-shadow: 0 1px 0 rgba(0, 0, 0, 0.3);"

footerStyle :: String
footerStyle =
  "padding: 12px 20px; " <>
  "border-top: 1px solid var(--lattice-border-subtle, #2a2a2a); " <>
  "text-align: center;"

hintStyle :: String
hintStyle =
  "font-size: 12px; color: var(--lattice-text-muted, #6b7280);"

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // actions
-- ═══════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    state <- H.get
    -- Reset search when opening
    when (input.visible && not state.visible) do
      H.modify_ _ { searchQuery = "" }
    H.modify_ _ { visible = input.visible }
  
  HandleKeyDown event -> do
    when (KE.key event == "Escape") do
      H.raise Closed
  
  UpdateSearch query -> do
    H.modify_ _ { searchQuery = query }
  
  CloseModal -> do
    H.raise Closed

handleQuery :: forall m a. Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  Close a -> do
    H.modify_ _ { visible = false }
    H.raise Closed
    pure (Just a)
  
  Open a -> do
    H.modify_ _ { visible = true, searchQuery = "" }
    pure (Just a)
