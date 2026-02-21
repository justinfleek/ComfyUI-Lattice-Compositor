-- | Lattice UI Core Primitives
-- |
-- | Core UI helper functions and component primitives that match
-- | the Lattice Compositor visual design system.
-- |
-- | Re-exports Hydrogen.UI.* for loading states, error states, and layout.
-- |
-- | IMPORTANT: This module uses CSS classes that correspond to design-tokens.css.
-- | Components should use the `lattice-*` class naming convention.
module Lattice.UI.Core
  ( -- Re-exports from Hydrogen
    module Hydrogen.UI.Loading
  , module Hydrogen.UI.Error
  , module Hydrogen.Data.RemoteData
    -- Class utilities
  , cls
  , classes
  , svgCls
    -- Lattice layout primitives
  , panel
  , surface
  , btn
  , btnPrimary
  , btnGhost
  , input
  , toolBtn
  , menu
  , menuItem
  , collapsibleHeader
  , slider
  , flex
  , row
  , column
  , grid
  , spacer
  , divider
  , icon
  , text
  , textMuted
  , textSecondary
  , label
  , heading
    -- Theming
  , Theme(..)
  , setTheme
  ) where

import Prelude

import Data.Array (filter, intercalate)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.Data.RemoteData (RemoteData(..), fromEither, fromMaybe, toEither, toMaybe, fold, withDefault, isNotAsked, isLoading, isFailure, isSuccess, mapError, map2, map3, map4, sequence, traverse)
import Hydrogen.UI.Error (errorState, errorCard, errorBadge, errorInline, emptyState)
import Hydrogen.UI.Loading (spinner, spinnerSm, spinnerMd, spinnerLg, loadingState, loadingInline, loadingCard, loadingCardLarge, skeletonText, skeletonRow)
import Web.DOM.Element as Element
import Web.HTML as HTML
import Web.HTML.HTMLDocument as HTMLDocument
import Web.HTML.HTMLHtmlElement as HTMLHtmlElement
import Web.HTML.Window as Window

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // utility // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Combine class names, filtering empty strings
classes :: Array String -> String
classes = intercalate " " <<< filter (_ /= "")

-- | Create HP.class_ from array of class strings
cls :: forall r i. Array String -> HH.IProp (class :: String | r) i
cls = HP.class_ <<< HH.ClassName <<< classes

-- | Create class attribute for SVG elements
-- | SVG elements have `className` as a read-only SVGAnimatedString, so we must
-- | use the `class` attribute instead of the `className` property.
svgCls :: forall r i. Array String -> HH.IProp r i
svgCls arr = HP.attr (HH.AttrName "class") (classes arr)

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // layout // primitives
-- ════════════════════════════════════════════════════════════════════════════

-- | Flex container with direction
flex :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
flex className = HH.div [ cls [ "lattice-flex", className ] ]

-- | Horizontal flex row
row :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
row className = HH.div [ cls [ "lattice-flex lattice-row", className ] ]

-- | Vertical flex column
column :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
column className = HH.div [ cls [ "lattice-flex lattice-column", className ] ]

-- | CSS Grid container
grid :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
grid className = HH.div [ cls [ "lattice-grid", className ] ]

-- | Flexible spacer
spacer :: forall w i. HH.HTML w i
spacer = HH.div [ cls [ "lattice-spacer" ] ] []

-- | Horizontal divider
divider :: forall w i. HH.HTML w i
divider = HH.hr [ cls [ "lattice-divider" ] ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // surface // components
-- ════════════════════════════════════════════════════════════════════════════

-- | Panel container (surface-1 background, rounded)
panel :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
panel className = HH.div [ cls [ "lattice-panel", className ] ]

-- | Surface container with level
surface :: forall w i. Int -> String -> Array (HH.HTML w i) -> HH.HTML w i
surface level className = 
  HH.div [ cls [ "lattice-surface-" <> show level, className ] ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // button // components
-- ════════════════════════════════════════════════════════════════════════════

-- | Base button
btn :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
btn className = HH.button [ cls [ "lattice-btn", className ] ]

-- | Primary accent button
btnPrimary :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
btnPrimary className = HH.button [ cls [ "lattice-btn lattice-btn-primary", className ] ]

-- | Ghost/transparent button
btnGhost :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
btnGhost className = HH.button [ cls [ "lattice-btn lattice-btn-ghost", className ] ]

-- | Tool button (for toolbars)
toolBtn :: forall w i. String -> Boolean -> Array (HH.HTML w i) -> HH.HTML w i
toolBtn className active = 
  HH.button 
    [ cls [ "lattice-tool-btn", className ]
    , HP.attr (HH.AttrName "data-state") (if active then "active" else "inactive")
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // input // components
-- ════════════════════════════════════════════════════════════════════════════

-- | Text input
input :: forall w i. String -> HH.HTML w i
input placeholder = 
  HH.input 
    [ cls [ "lattice-input" ]
    , HP.placeholder placeholder
    ]

-- | Slider track
slider :: forall w i. Number -> HH.HTML w i
slider value =
  HH.div [ cls [ "lattice-slider" ] ]
    [ HH.div [ cls [ "lattice-slider-track" ] ]
        [ HH.div 
            [ cls [ "lattice-slider-fill" ]
            , HP.attr (HH.AttrName "style") ("width: " <> show (value * 100.0) <> "%")
            ] 
            []
        , HH.div 
            [ cls [ "lattice-slider-thumb" ]
            , HP.attr (HH.AttrName "style") ("left: " <> show (value * 100.0) <> "%")
            ]
            []
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // menu // components
-- ════════════════════════════════════════════════════════════════════════════

-- | Menu container
menu :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
menu = HH.div [ cls [ "lattice-menu" ] ]

-- | Menu item with optional shortcut
menuItem :: forall w i. String -> String -> HH.HTML w i
menuItem labelText shortcut =
  HH.div [ cls [ "lattice-menu-item" ] ]
    [ HH.span_ [ HH.text labelText ]
    , if shortcut == "" 
        then HH.text ""
        else HH.span [ cls [ "lattice-menu-shortcut" ] ] [ HH.text shortcut ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                        // collapsible // panel // components
-- ════════════════════════════════════════════════════════════════════════════

-- | Collapsible section header
collapsibleHeader :: forall w i. String -> Boolean -> HH.HTML w i
collapsibleHeader title expanded =
  HH.div 
    [ cls [ "lattice-collapsible-header" ]
    , HP.attr (HH.AttrName "data-state") (if expanded then "open" else "closed")
    ]
    [ HH.span [ cls [ "lattice-collapsible-icon" ] ] 
        [ HH.text (if expanded then "▼" else "►") ]
    , HH.span [ cls [ "lattice-collapsible-title" ] ] 
        [ HH.text title ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                // typography
-- ════════════════════════════════════════════════════════════════════════════

-- | Primary text
text :: forall w i. String -> HH.HTML w i
text content = HH.span [ cls [ "lattice-text" ] ] [ HH.text content ]

-- | Muted text
textMuted :: forall w i. String -> HH.HTML w i
textMuted content = HH.span [ cls [ "lattice-text-muted" ] ] [ HH.text content ]

-- | Secondary text
textSecondary :: forall w i. String -> HH.HTML w i
textSecondary content = HH.span [ cls [ "lattice-text-secondary" ] ] [ HH.text content ]

-- | Label text
label :: forall w i. String -> HH.HTML w i
label content = HH.label [ cls [ "lattice-label" ] ] [ HH.text content ]

-- | Heading
heading :: forall w i. Int -> String -> HH.HTML w i
heading level content = case level of
  1 -> HH.h1 [ cls [ "lattice-heading lattice-h1" ] ] [ HH.text content ]
  2 -> HH.h2 [ cls [ "lattice-heading lattice-h2" ] ] [ HH.text content ]
  3 -> HH.h3 [ cls [ "lattice-heading lattice-h3" ] ] [ HH.text content ]
  4 -> HH.h4 [ cls [ "lattice-heading lattice-h4" ] ] [ HH.text content ]
  _ -> HH.h5 [ cls [ "lattice-heading lattice-h5" ] ] [ HH.text content ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // icons
-- ════════════════════════════════════════════════════════════════════════════

-- | Icon placeholder (replace with actual icon library)
icon :: forall w i. String -> String -> HH.HTML w i
icon name size = 
  HH.span 
    [ cls [ "lattice-icon", "lattice-icon-" <> size ]
    , HP.attr (HH.AttrName "data-icon") name
    ] 
    []

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // theming
-- ════════════════════════════════════════════════════════════════════════════

data Theme
  = Violet
  | Ocean
  | Rose
  | Forest
  | Ember
  | Mono

derive instance eqTheme :: Eq Theme

-- | Set the current theme by updating the data-theme attribute on documentElement
setTheme :: Theme -> Effect Unit
setTheme theme = do
  win <- HTML.window
  doc <- Window.document win
  mDocEl <- HTMLDocument.documentElement doc
  case mDocEl of
    Just docEl -> do
      let themeName = case theme of
            Violet -> "violet"
            Ocean -> "ocean"
            Rose -> "rose"
            Forest -> "forest"
            Ember -> "ember"
            Mono -> "mono"
      Element.setAttribute "data-theme" themeName (HTMLHtmlElement.toElement docEl)
    Nothing -> pure unit
