-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // compound // breadcrumb
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen Breadcrumb Component
-- |
-- | Breadcrumb trails for hierarchical navigation.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Breadcrumb as Breadcrumb
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic breadcrumb
-- | Breadcrumb.breadcrumb []
-- |   [ Breadcrumb.breadcrumbItem [ Breadcrumb.itemHref "/" ] [ E.text "Home" ]
-- |   , Breadcrumb.breadcrumbItem [ Breadcrumb.itemHref "/products" ] [ E.text "Products" ]
-- |   , Breadcrumb.breadcrumbItem [ Breadcrumb.isCurrent true ] [ E.text "Widget" ]
-- |   ]
-- |
-- | -- With custom separator
-- | Breadcrumb.breadcrumb [ Breadcrumb.separator "/" ]
-- |   [ ... ]
-- |
-- | -- Collapsed mode (ellipsis for long paths)
-- | Breadcrumb.breadcrumb [ Breadcrumb.collapsed 2 ]
-- |   [ ... ]
-- | ```
module Hydrogen.Element.Compound.Breadcrumb
  ( -- * Breadcrumb Components
    breadcrumb
  , breadcrumbItem
  , breadcrumbSeparator
  , breadcrumbEllipsis
    -- * Props
  , BreadcrumbProps
  , BreadcrumbProp
  , ItemProps
  , ItemProp
  , defaultProps
  , defaultItemProps
    -- * Prop Builders
  , separator
  , collapsed
  , breadcrumbClassName
  , itemHref
  , isCurrent
  , itemClassName
  , onItemClick
  ) where

import Prelude
  ( (<>)
  , (>)
  , (+)
  , (-)
  , (*)
  )

import Data.Array (foldl, length, take, drop)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // breadcrumb props
-- ═════════════════════════════════════════════════════════════════════════════

type BreadcrumbProps =
  { separator :: String
  , collapsed :: Maybe Int  -- Show first N and last N items with ellipsis
  , className :: String
  }

type BreadcrumbProp = BreadcrumbProps -> BreadcrumbProps

defaultProps :: BreadcrumbProps
defaultProps =
  { separator: "›"
  , collapsed: Nothing
  , className: ""
  }

-- | Set custom separator character
separator :: String -> BreadcrumbProp
separator s props = props { separator = s }

-- | Collapse middle items when more than N items on each side
collapsed :: Int -> BreadcrumbProp
collapsed n props = props { collapsed = Just n }

-- | Add custom class to breadcrumb container
breadcrumbClassName :: String -> BreadcrumbProp
breadcrumbClassName c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // item props
-- ═════════════════════════════════════════════════════════════════════════════

type ItemProps msg =
  { href :: Maybe String
  , current :: Boolean
  , className :: String
  , onClick :: Maybe msg
  }

type ItemProp msg = ItemProps msg -> ItemProps msg

defaultItemProps :: forall msg. ItemProps msg
defaultItemProps =
  { href: Nothing
  , current: false
  , className: ""
  , onClick: Nothing
  }

-- | Set link href
itemHref :: forall msg. String -> ItemProp msg
itemHref h props = props { href = Just h }

-- | Mark as current page
isCurrent :: forall msg. Boolean -> ItemProp msg
isCurrent c props = props { current = c }

-- | Add custom class to item
itemClassName :: forall msg. String -> ItemProp msg
itemClassName c props = props { className = props.className <> " " <> c }

-- | Set click handler
onItemClick :: forall msg. msg -> ItemProp msg
onItemClick handler props = props { onClick = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Breadcrumb container
-- |
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
breadcrumb :: forall msg. Array BreadcrumbProp -> Array (E.Element msg) -> E.Element msg
breadcrumb propMods items =
  let 
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Handle collapsed mode
    displayItems = case props.collapsed of
      Just n | length items > (n * 2 + 1) ->
        let
          firstItems = take n items
          lastItems = drop (length items - n) items
        in
          firstItems <> [ breadcrumbEllipsis ] <> lastItems
      _ -> items
    
    -- Interleave items with separators
    withSeparators = interleaveSeparator props.separator displayItems
  in
    E.nav_
      [ E.classes [ "flex", props.className ]
      , E.ariaLabel "Breadcrumb"
      ]
      [ E.ol_
          [ E.class_ "flex items-center gap-1.5 flex-wrap" ]
          withSeparators
      ]

-- | Breadcrumb item
breadcrumbItem :: forall msg. Array (ItemProp msg) -> Array (E.Element msg) -> E.Element msg
breadcrumbItem propMods children =
  let
    props = foldl (\p f -> f p) defaultItemProps propMods
    
    linkClasses = 
      "text-sm font-medium text-muted-foreground hover:text-foreground transition-colors"
    
    currentClasses =
      "text-sm font-medium text-foreground"
    
    clickHandler = case props.onClick of
      Just h -> [ E.onClick h ]
      Nothing -> []
  in
    E.li_
      [ E.classes [ "inline-flex items-center", props.className ] ]
      [ if props.current
          then
            E.span_
              [ E.class_ currentClasses
              , E.attr "aria-current" "page"
              ]
              children
          else case props.href of
            Just h ->
              E.a_
                ([ E.class_ linkClasses
                , E.href h
                ] <> clickHandler)
                children
            Nothing ->
              E.span_
                ([ E.classes [ linkClasses, "cursor-pointer" ] ] <> clickHandler)
                children
      ]

-- | Breadcrumb separator
breadcrumbSeparator :: forall msg. String -> E.Element msg
breadcrumbSeparator sep =
  E.li_
    [ E.class_ "text-muted-foreground"
    , E.role "presentation"
    , E.ariaHidden true
    ]
    [ E.span_
        [ E.class_ "text-sm" ]
        [ E.text sep ]
    ]

-- | Breadcrumb ellipsis (for collapsed mode)
breadcrumbEllipsis :: forall msg. E.Element msg
breadcrumbEllipsis =
  E.li_
    [ E.class_ "inline-flex items-center"
    , E.role "presentation"
    ]
    [ E.span_
        [ E.class_ "flex h-9 w-9 items-center justify-center"
        , E.ariaLabel "More pages"
        ]
        [ E.svg_
            [ E.attr "xmlns" "http://www.w3.org/2000/svg"
            , E.attr "width" "16"
            , E.attr "height" "16"
            , E.attr "viewBox" "0 0 24 24"
            , E.attr "fill" "none"
            , E.attr "stroke" "currentColor"
            , E.attr "stroke-width" "2"
            , E.attr "stroke-linecap" "round"
            , E.attr "stroke-linejoin" "round"
            , E.class_ "text-muted-foreground"
            ]
            [ E.svgElement "circle"
                [ E.attr "cx" "12"
                , E.attr "cy" "12"
                , E.attr "r" "1"
                ]
                []
            , E.svgElement "circle"
                [ E.attr "cx" "19"
                , E.attr "cy" "12"
                , E.attr "r" "1"
                ]
                []
            , E.svgElement "circle"
                [ E.attr "cx" "5"
                , E.attr "cy" "12"
                , E.attr "r" "1"
                ]
                []
            ]
        ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interleave items with separators
interleaveSeparator :: forall msg. String -> Array (E.Element msg) -> Array (E.Element msg)
interleaveSeparator sep items = go items []
  where
    go :: Array (E.Element msg) -> Array (E.Element msg) -> Array (E.Element msg)
    go arr acc = case length arr of
      0 -> acc
      1 -> acc <> arr
      _ -> case take 1 arr of
        firstItem -> go (drop 1 arr) (acc <> firstItem <> [breadcrumbSeparator sep])
