-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // ui // pagination
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pagination Component — Pure Element Version
-- |
-- | Page navigation controls.
module Hydrogen.UI.Pagination
  ( pagination
  , paginationContent
  , paginationItem
  , paginationLink
  , paginationPrevious
  , paginationNext
  , paginationEllipsis
  , className
  ) where

import Prelude ((<>))

import Data.Array (foldl)
import Hydrogen.Render.Element as E

type PaginationConfig = { className :: String }
type ConfigMod = PaginationConfig -> PaginationConfig

defaultConfig :: PaginationConfig
defaultConfig = { className: "" }

className :: String -> ConfigMod
className c config = config { className = config.className <> " " <> c }

-- | Pagination container
pagination :: forall msg. Array ConfigMod -> Array (E.Element msg) -> E.Element msg
pagination mods children =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    allClasses = "mx-auto flex w-full justify-center " <> config.className
  in
    E.nav_ 
      [ E.class_ allClasses
      , E.role "navigation"
      , E.ariaLabel "pagination"
      ]
      children

-- | Pagination content list
paginationContent :: forall msg. Array (E.Element msg) -> E.Element msg
paginationContent children =
  E.ul_ [ E.class_ "flex flex-row items-center gap-1" ] children

-- | Pagination item wrapper
paginationItem :: forall msg. E.Element msg -> E.Element msg
paginationItem child =
  E.li_ [] [ child ]

-- | Page number link
paginationLink :: forall msg. Boolean -> msg -> String -> E.Element msg
paginationLink isActive onClickMsg label =
  let
    baseClasses = "inline-flex items-center justify-center whitespace-nowrap rounded-md text-sm font-medium ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50 h-10 w-10"
    activeClasses = if isActive 
      then "border border-input bg-background hover:bg-accent hover:text-accent-foreground"
      else "hover:bg-accent hover:text-accent-foreground"
  in
    E.button_
      [ E.class_ (baseClasses <> " " <> activeClasses)
      , E.onClick onClickMsg
      , E.attr "aria-current" (if isActive then "page" else "false")
      ]
      [ E.text label ]

-- | Previous page button
paginationPrevious :: forall msg. msg -> E.Element msg
paginationPrevious onClickMsg =
  E.button_
    [ E.class_ "inline-flex items-center justify-center whitespace-nowrap rounded-md text-sm font-medium ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50 hover:bg-accent hover:text-accent-foreground h-10 px-4 py-2 gap-1 pl-2.5"
    , E.onClick onClickMsg
    ]
    [ E.span_ [ E.class_ "sr-only" ] [ E.text "Go to previous page" ]
    , E.text "← Previous"
    ]

-- | Next page button  
paginationNext :: forall msg. msg -> E.Element msg
paginationNext onClickMsg =
  E.button_
    [ E.class_ "inline-flex items-center justify-center whitespace-nowrap rounded-md text-sm font-medium ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50 hover:bg-accent hover:text-accent-foreground h-10 px-4 py-2 gap-1 pr-2.5"
    , E.onClick onClickMsg
    ]
    [ E.span_ [ E.class_ "sr-only" ] [ E.text "Go to next page" ]
    , E.text "Next →"
    ]

-- | Ellipsis for skipped pages
paginationEllipsis :: forall msg. E.Element msg
paginationEllipsis =
  E.span_ 
    [ E.class_ "flex h-9 w-9 items-center justify-center"
    , E.ariaHidden true
    ]
    [ E.text "..." ]
