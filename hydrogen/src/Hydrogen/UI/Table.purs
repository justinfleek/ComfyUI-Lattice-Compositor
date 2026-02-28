-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // ui // table
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Table Component — Pure Element Version
-- |
-- | Styled data tables.
module Hydrogen.UI.Table
  ( table
  , tableHeader
  , tableBody
  , tableFooter
  , tableRow
  , tableHead
  , tableCell
  , tableCaption
  , className
  ) where

import Prelude ((<>))

import Data.Array (foldl)
import Hydrogen.Render.Element as E

type TableConfig = { className :: String }
type ConfigMod = TableConfig -> TableConfig

defaultConfig :: TableConfig
defaultConfig = { className: "" }

className :: String -> ConfigMod
className c config = config { className = config.className <> " " <> c }

-- | Table container
table :: forall msg. Array ConfigMod -> Array (E.Element msg) -> E.Element msg
table mods children =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    allClasses = "w-full caption-bottom text-sm " <> config.className
  in
    E.div_ 
      [ E.class_ "relative w-full overflow-auto" ]
      [ E.table_ [ E.class_ allClasses ] children ]

-- | Table header section
tableHeader :: forall msg. Array (E.Element msg) -> E.Element msg
tableHeader children =
  E.thead_ [ E.class_ "[&_tr]:border-b" ] children

-- | Table body section
tableBody :: forall msg. Array (E.Element msg) -> E.Element msg
tableBody children =
  E.tbody_ [ E.class_ "[&_tr:last-child]:border-0" ] children

-- | Table footer section
tableFooter :: forall msg. Array (E.Element msg) -> E.Element msg
tableFooter children =
  E.element "tfoot" 
    [ E.class_ "border-t bg-muted/50 font-medium [&>tr]:last:border-b-0" ] 
    children

-- | Table row
tableRow :: forall msg. Array (E.Attribute msg) -> Array (E.Element msg) -> E.Element msg
tableRow attrs children =
  E.tr_ 
    ([ E.class_ "border-b transition-colors hover:bg-muted/50 data-[state=selected]:bg-muted" ] <> attrs) 
    children

-- | Table header cell
tableHead :: forall msg. Array (E.Element msg) -> E.Element msg
tableHead children =
  E.th_ 
    [ E.class_ "h-12 px-4 text-left align-middle font-medium text-muted-foreground [&:has([role=checkbox])]:pr-0" ] 
    children

-- | Table data cell
tableCell :: forall msg. Array (E.Attribute msg) -> Array (E.Element msg) -> E.Element msg
tableCell attrs children =
  E.td_ 
    ([ E.class_ "p-4 align-middle [&:has([role=checkbox])]:pr-0" ] <> attrs)
    children

-- | Table caption
tableCaption :: forall msg. String -> E.Element msg
tableCaption text =
  E.element "caption" 
    [ E.class_ "mt-4 text-sm text-muted-foreground" ] 
    [ E.text text ]
