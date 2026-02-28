-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // table
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen Table Component
-- |
-- | Styled data table components for displaying structured data.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Table as Table
-- | import Hydrogen.Render.Element as E
-- |
-- | Table.table []
-- |   [ Table.tableHeader []
-- |       [ Table.tableRow []
-- |           [ Table.tableHead [] [ E.text "Name" ]
-- |           , Table.tableHead [] [ E.text "Status" ]
-- |           ]
-- |       ]
-- |   , Table.tableBody []
-- |       [ Table.tableRow []
-- |           [ Table.tableCell [] [ E.text "John" ]
-- |           , Table.tableCell [] [ E.text "Active" ]
-- |           ]
-- |       ]
-- |   ]
-- | ```
module Hydrogen.Element.Compound.Table
  ( -- * Table Components
    table
  , tableHeader
  , tableBody
  , tableFooter
  , tableRow
  , tableHead
  , tableCell
  , tableCaption
    -- * Props
  , TableProps
  , TableProp
  , className
  ) where

import Prelude
  ( (<>)
  )

import Data.Array (foldl)
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

type TableProps = { className :: String }
type TableProp = TableProps -> TableProps

defaultProps :: TableProps
defaultProps = { className: "" }

-- | Add custom class
className :: String -> TableProp
className c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Table container
-- |
-- | Wraps table in a scrollable container with styled table element.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
table :: forall msg. Array TableProp -> Array (E.Element msg) -> E.Element msg
table propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in E.div_
    [ E.class_ "relative w-full overflow-auto" ]
    [ E.table_
        [ E.classes [ "w-full caption-bottom text-sm", props.className ] ]
        children
    ]

-- | Table header section
-- |
-- | Container for header rows with bottom border styling.
tableHeader :: forall msg. Array TableProp -> Array (E.Element msg) -> E.Element msg
tableHeader propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in E.thead_
    [ E.classes [ "[&_tr]:border-b", props.className ] ]
    children

-- | Table body section
-- |
-- | Container for data rows with last-row border removal.
tableBody :: forall msg. Array TableProp -> Array (E.Element msg) -> E.Element msg
tableBody propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in E.tbody_
    [ E.classes [ "[&_tr:last-child]:border-0", props.className ] ]
    children

-- | Table footer section
-- |
-- | Container for footer rows with muted background.
tableFooter :: forall msg. Array TableProp -> Array (E.Element msg) -> E.Element msg
tableFooter propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in E.tfoot_
    [ E.classes [ "border-t bg-muted/50 font-medium [&>tr]:last:border-b-0", props.className ] ]
    children

-- | Table row
-- |
-- | A row within table header, body, or footer.
-- | Includes hover and selection states.
tableRow :: forall msg. Array TableProp -> Array (E.Element msg) -> E.Element msg
tableRow propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in E.tr_
    [ E.classes [ "border-b transition-colors hover:bg-muted/50 data-[state=selected]:bg-muted", props.className ] ]
    children

-- | Table header cell
-- |
-- | A header cell within a table row. Styled with muted foreground color.
tableHead :: forall msg. Array TableProp -> Array (E.Element msg) -> E.Element msg
tableHead propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in E.th_
    [ E.classes [ "h-12 px-4 text-left align-middle font-medium text-muted-foreground [&:has([role=checkbox])]:pr-0", props.className ] ]
    children

-- | Table data cell
-- |
-- | A data cell within a table row.
tableCell :: forall msg. Array TableProp -> Array (E.Element msg) -> E.Element msg
tableCell propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in E.td_
    [ E.classes [ "p-4 align-middle [&:has([role=checkbox])]:pr-0", props.className ] ]
    children

-- | Table caption
-- |
-- | A caption for the table, displayed below the table content.
tableCaption :: forall msg. Array TableProp -> Array (E.Element msg) -> E.Element msg
tableCaption propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in E.caption_
    [ E.classes [ "mt-4 text-sm text-muted-foreground", props.className ] ]
    children
