-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // ui // breadcrumb
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Breadcrumb Component — Pure Element Version
-- |
-- | Navigation breadcrumbs showing page hierarchy.
module Hydrogen.UI.Breadcrumb
  ( breadcrumb
  , breadcrumbItem
  , breadcrumbLink
  , breadcrumbSeparator
  , breadcrumbPage
  , className
  ) where

import Prelude ((<>))

import Data.Array (foldl)
import Hydrogen.Render.Element as E

type BreadcrumbConfig = { className :: String }
type ConfigMod = BreadcrumbConfig -> BreadcrumbConfig

defaultConfig :: BreadcrumbConfig
defaultConfig = { className: "" }

className :: String -> ConfigMod
className c config = config { className = config.className <> " " <> c }

-- | Breadcrumb container
breadcrumb :: forall msg. Array ConfigMod -> Array (E.Element msg) -> E.Element msg
breadcrumb mods children =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    allClasses = "flex flex-wrap items-center gap-1.5 break-words text-sm text-muted-foreground sm:gap-2.5 " <> config.className
  in
    E.nav_ 
      [ E.ariaLabel "Breadcrumb" ]
      [ E.ol_ [ E.class_ allClasses ] children ]

-- | Single breadcrumb item wrapper
breadcrumbItem :: forall msg. Array (E.Element msg) -> E.Element msg
breadcrumbItem children =
  E.li_ 
    [ E.class_ "inline-flex items-center gap-1.5" ] 
    children

-- | Clickable breadcrumb link
breadcrumbLink :: forall msg. String -> String -> E.Element msg
breadcrumbLink href text =
  E.a_
    [ E.class_ "transition-colors hover:text-foreground"
    , E.href href
    ]
    [ E.text text ]

-- | Separator between breadcrumb items
breadcrumbSeparator :: forall msg. E.Element msg
breadcrumbSeparator =
  E.li_
    [ E.class_ "[&>svg]:size-3.5"
    , E.role "presentation"
    , E.ariaHidden true
    ]
    [ E.span_ [ E.class_ "text-muted-foreground" ] [ E.text "/" ] ]

-- | Current page (non-clickable)
breadcrumbPage :: forall msg. String -> E.Element msg
breadcrumbPage text =
  E.span_
    [ E.class_ "font-normal text-foreground"
    , E.role "link"
    , E.attr "aria-disabled" "true"
    , E.attr "aria-current" "page"
    ]
    [ E.text text ]
