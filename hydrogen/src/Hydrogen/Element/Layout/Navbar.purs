-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // layout // nav-bar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Navbar — Pure Element navigation bar component.
-- |
-- | ## Design Philosophy
-- |
-- | Responsive navigation bar with brand, nav items, and actions.
-- | Uses Schema atoms for dimensions and breakpoints.
-- | No Halogen dependency — pure Element composition.

module Hydrogen.Element.Layout.Navbar
  ( -- * Component
    navbar
    
  -- * Types
  , NavbarVariant(DefaultVariant, Transparent, Blurred, Bordered)
  , NavbarSlots
  , NavbarProps
  , NavbarProp
  , defaultProps
  
  -- * Prop Setters
  , variant
  , sticky
  , height
  , mobileBreakpoint
  , mobileMenuOpen
  , className
  
  -- * Icons
  , menuIcon
  , closeIcon
  ) where

import Prelude
  ( class Eq
  , class Show
  , (<>)
  , ($)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Render.Element (Element)
import Hydrogen.Render.Element as E
import Hydrogen.Schema.Geometry.Spacing (SpacingValue)
import Hydrogen.Schema.Geometry.Spacing as Spacing
import Hydrogen.Schema.Reactive.Viewport (Breakpoint(Xs, Sm, Md, Lg, Xl, Xxl))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // variant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Navbar visual variants.
data NavbarVariant
  = DefaultVariant   -- ^ Solid background with border
  | Transparent      -- ^ No background (for hero sections)
  | Blurred          -- ^ Semi-transparent with backdrop blur
  | Bordered         -- ^ Emphasized border

derive instance eqNavbarVariant :: Eq NavbarVariant

instance showNavbarVariant :: Show NavbarVariant where
  show DefaultVariant = "default"
  show Transparent = "transparent"
  show Blurred = "blurred"
  show Bordered = "bordered"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // slots
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content slots for navbar.
type NavbarSlots msg =
  { brand :: Maybe (Element msg)      -- ^ Logo/brand area
  , items :: Array (Element msg)      -- ^ Navigation items
  , actions :: Maybe (Element msg)    -- ^ Right-side actions (user menu, etc.)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Navbar configuration.
type NavbarProps =
  { variant :: NavbarVariant
  , sticky :: Boolean
  , height :: SpacingValue
  , mobileBreakpoint :: Breakpoint
  , mobileMenuOpen :: Boolean
  , className :: String
  }

-- | Property modifier.
type NavbarProp = NavbarProps -> NavbarProps

-- | Default navbar configuration.
defaultProps :: NavbarProps
defaultProps =
  { variant: DefaultVariant
  , sticky: false
  , height: Spacing.spacingValue 64.0
  , mobileBreakpoint: Md
  , mobileMenuOpen: false
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // prop setters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set visual variant.
variant :: NavbarVariant -> NavbarProp
variant v props = props { variant = v }

-- | Make navbar sticky (fixed to top).
sticky :: Boolean -> NavbarProp
sticky s props = props { sticky = s }

-- | Set navbar height.
height :: SpacingValue -> NavbarProp
height h props = props { height = h }

-- | Set mobile breakpoint (items collapse below this).
mobileBreakpoint :: Breakpoint -> NavbarProp
mobileBreakpoint b props = props { mobileBreakpoint = b }

-- | Set mobile menu open state.
mobileMenuOpen :: Boolean -> NavbarProp
mobileMenuOpen o props = props { mobileMenuOpen = o }

-- | Add custom CSS class.
className :: String -> NavbarProp
className c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Responsive navbar component.
-- |
-- | Provides brand, navigation items, and actions areas.
-- | Automatically collapses to mobile menu below breakpoint.
navbar :: forall msg. Array NavbarProp -> NavbarSlots msg -> Element msg
navbar propMods slots =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    bp = breakpointPrefix props.mobileBreakpoint
  in
    E.nav_
      [ E.class_ $ "w-full z-40 " <> variantClass props.variant
          <> (if props.sticky then " sticky top-0" else "")
          <> " " <> props.className
      , E.ariaLabel "Main navigation"
      ]
      [ -- Inner container
        E.div_
          [ E.class_ "mx-auto px-4 sm:px-6 lg:px-8 max-w-7xl"
          ]
          [ E.div_
              [ E.class_ "flex items-center justify-between"
              , E.style "height" (Spacing.toLegacyCss props.height)
              ]
              [ -- Brand area
                renderBrand slots.brand
                -- Desktop nav items
              , E.div_
                  [ E.class_ $ "hidden " <> bp <> "flex " <> bp <> "items-center " <> bp <> "space-x-4"
                  ]
                  slots.items
                -- Desktop actions
              , renderActions bp slots.actions
                -- Mobile menu button
              , renderMobileButton bp props.mobileMenuOpen
              ]
          ]
        -- Mobile menu panel
      , if props.mobileMenuOpen
          then renderMobileMenu bp slots
          else E.empty
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // render helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render brand area.
renderBrand :: forall msg. Maybe (Element msg) -> Element msg
renderBrand maybeBrand =
  case maybeBrand of
    Just brand -> E.div_ [ E.class_ "flex-shrink-0" ] [ brand ]
    Nothing -> E.empty

-- | Render actions area.
renderActions :: forall msg. String -> Maybe (Element msg) -> Element msg
renderActions bp maybeActions =
  case maybeActions of
    Just actions -> 
      E.div_ 
        [ E.class_ $ "hidden " <> bp <> "flex " <> bp <> "items-center " <> bp <> "space-x-4" ] 
        [ actions ]
    Nothing -> E.empty

-- | Render mobile menu toggle button.
renderMobileButton :: forall msg. String -> Boolean -> Element msg
renderMobileButton bp isOpen =
  E.button_
    [ E.class_ $ bp <> "hidden inline-flex items-center justify-center p-2 rounded-md text-muted-foreground hover:text-foreground hover:bg-accent"
    , E.type_ "button"
    , E.ariaLabel (if isOpen then "Close menu" else "Open menu")
    ]
    [ if isOpen then closeIcon else menuIcon ]

-- | Render mobile menu panel.
renderMobileMenu :: forall msg. String -> NavbarSlots msg -> Element msg
renderMobileMenu bp slots =
  E.div_
    [ E.class_ $ bp <> "hidden border-t bg-background"
    , E.id_ "mobile-menu"
    ]
    [ E.div_
        [ E.class_ "px-2 pt-2 pb-3 space-y-1" ]
        slots.items
    , case slots.actions of
        Just actions -> 
          E.div_ [ E.class_ "pt-4 pb-3 border-t" ] [ actions ]
        Nothing -> E.empty
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // css helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get variant CSS classes.
variantClass :: NavbarVariant -> String
variantClass DefaultVariant = "bg-background border-b border-border"
variantClass Transparent = "bg-transparent"
variantClass Blurred = "bg-background/80 backdrop-blur-md border-b border-border"
variantClass Bordered = "bg-background border-b-2 border-primary"

-- | Get breakpoint prefix for Tailwind classes.
breakpointPrefix :: Breakpoint -> String
breakpointPrefix Xs = ""
breakpointPrefix Sm = "sm:"
breakpointPrefix Md = "md:"
breakpointPrefix Lg = "lg:"
breakpointPrefix Xl = "xl:"
breakpointPrefix Xxl = "2xl:"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hamburger menu icon.
menuIcon :: forall msg. Element msg
menuIcon =
  E.svg_
    [ E.class_ "h-6 w-6"
    , E.attr "fill" "none"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.path_
        [ E.attr "stroke-linecap" "round"
        , E.attr "stroke-linejoin" "round"
        , E.attr "d" "M4 6h16M4 12h16M4 18h16"
        ]
    ]

-- | Close (X) icon.
closeIcon :: forall msg. Element msg
closeIcon =
  E.svg_
    [ E.class_ "h-6 w-6"
    , E.attr "fill" "none"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.path_
        [ E.attr "stroke-linecap" "round"
        , E.attr "stroke-linejoin" "round"
        , E.attr "d" "M6 18L18 6M6 6l12 12"
        ]
    ]
