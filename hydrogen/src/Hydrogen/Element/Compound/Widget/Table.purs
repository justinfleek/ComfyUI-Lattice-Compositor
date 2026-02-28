-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // widget // table
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Table Widget — Tabular data display with sorting and pagination.
-- |
-- | ## Design Philosophy
-- |
-- | A Table widget displays data in rows and columns with:
-- | - Column definitions (type, label, alignment, width)
-- | - Row data as arrays of cell values
-- | - Pagination state and controls
-- | - Optional sorting by column
-- | - Optional row selection
-- | - Optional search filtering
-- |
-- | The widget accepts complete `TableData` — all data, column defs, and
-- | pagination state are provided upfront. Pure data in, Element out.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Widget.Table as Table
-- |
-- | Table.tableWidget []
-- |   { columns:
-- |       [ { key: "name", label: "Name", colType: Table.ColText, ... }
-- |       , { key: "amount", label: "Amount", colType: Table.ColCurrency, ... }
-- |       ]
-- |   , rows:
-- |       [ [ Table.TextCell "John Doe", Table.NumberCell 1234.56 ]
-- |       , [ Table.TextCell "Jane Smith", Table.NumberCell 5678.90 ]
-- |       ]
-- |   , pagination: Just { page: 1, pageSize: 10, total: 100, totalPages: 10 }
-- |   , ...
-- |   }
-- | ```

module Hydrogen.Element.Compound.Widget.Table
  ( -- * Widget Component
    tableWidget
  , tableWidgetSimple
  
  -- * Data Types
  , TableData
  , ColumnDef
  , CellValue
    ( TextCell
    , NumberCell
    , CurrencyCell
    , PercentCell
    , DateCell
    , BoolCell
    , BadgeCell
    , SparklineCell
    , ProgressCell
    , EmptyCell
    )
  , Pagination
  
  -- * Column Types
  , ColumnType
    ( ColText
    , ColNumber
    , ColCurrency
    , ColPercent
    , ColDate
    , ColDatetime
    , ColBoolean
    , ColBadge
    , ColSparkline
    , ColProgress
    )
  , columnTypeToString
  
  -- * Sort Direction
  , SortDirection
    ( SortAsc
    , SortDesc
    )
  , sortDirectionToString
  , toggleSort
  
  -- * Props
  , TableProps
  , TableProp
  , defaultProps
  
  -- * Prop Builders
  , selectable
  , searchable
  , striped
  , bordered
  , compact
  , className
  
  -- * Pagination Helpers
  , totalPages
  , hasNextPage
  , hasPrevPage
  , pageRange
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (==)
  , (&&)
  , (||)
  , (<>)
  , (<=)
  , (>=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , not
  )

import Data.Array (foldl, length, mapWithIndex, index)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Widget.Types (Percentage, unwrapPercentage)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // column types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Column data types.
-- |
-- | Determines how cell values are formatted and displayed.
data ColumnType
  = ColText
  | ColNumber
  | ColCurrency
  | ColPercent
  | ColDate
  | ColDatetime
  | ColBoolean
  | ColBadge
  | ColSparkline
  | ColProgress

derive instance eqColumnType :: Eq ColumnType

instance showColumnType :: Show ColumnType where
  show = columnTypeToString

-- | Convert column type to string.
columnTypeToString :: ColumnType -> String
columnTypeToString ct = case ct of
  ColText -> "text"
  ColNumber -> "number"
  ColCurrency -> "currency"
  ColPercent -> "percent"
  ColDate -> "date"
  ColDatetime -> "datetime"
  ColBoolean -> "boolean"
  ColBadge -> "badge"
  ColSparkline -> "sparkline"
  ColProgress -> "progress"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // sort direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sort direction.
data SortDirection
  = SortAsc
  | SortDesc

derive instance eqSortDirection :: Eq SortDirection

instance showSortDirection :: Show SortDirection where
  show = sortDirectionToString

-- | Convert sort direction to string.
sortDirectionToString :: SortDirection -> String
sortDirectionToString sd = case sd of
  SortAsc -> "asc"
  SortDesc -> "desc"

-- | Toggle sort direction.
toggleSort :: SortDirection -> SortDirection
toggleSort SortAsc = SortDesc
toggleSort SortDesc = SortAsc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // data types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Column definition.
type ColumnDef =
  { key :: String
  , label :: String
  , colType :: ColumnType
  , width :: Maybe Int      -- ^ Width in pixels
  , align :: Maybe String   -- ^ "left", "center", "right"
  , sortable :: Boolean
  , format :: Maybe String  -- ^ Custom format string
  }

-- | Cell value variants.
-- |
-- | Each variant corresponds to a column type and contains
-- | the appropriate data for rendering.
data CellValue
  = TextCell String
  | NumberCell Number
  | CurrencyCell Number String   -- ^ Value and currency code
  | PercentCell Number
  | DateCell String              -- ^ ISO date string
  | BoolCell Boolean
  | BadgeCell String String      -- ^ Text and variant (success, warning, error, etc.)
  | SparklineCell (Array Number)
  | ProgressCell Percentage
  | EmptyCell

derive instance eqCellValue :: Eq CellValue

instance showCellValue :: Show CellValue where
  show (TextCell s) = s
  show (NumberCell n) = show n
  show (CurrencyCell n code) = code <> " " <> show n
  show (PercentCell n) = show n <> "%"
  show (DateCell s) = s
  show (BoolCell b) = if b then "Yes" else "No"
  show (BadgeCell text _) = text
  show (SparklineCell _) = "[sparkline]"
  show (ProgressCell p) = show (unwrapPercentage p) <> "%"
  show EmptyCell = ""

-- | Pagination state.
type Pagination =
  { page :: Int
  , pageSize :: Int
  , total :: Int
  , totalPages :: Int
  }

-- | Complete table data payload.
type TableData =
  { columns :: Array ColumnDef
  , rows :: Array (Array CellValue)
  , pagination :: Maybe Pagination
  , sortBy :: Maybe String       -- ^ Column key currently sorting by
  , sortDir :: Maybe SortDirection
  , selectable :: Boolean
  , searchable :: Boolean
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Table widget properties.
type TableProps =
  { selectable :: Boolean
  , searchable :: Boolean
  , striped :: Boolean
  , bordered :: Boolean
  , compact :: Boolean
  , className :: String
  }

-- | Property modifier.
type TableProp = TableProps -> TableProps

-- | Default properties.
defaultProps :: TableProps
defaultProps =
  { selectable: false
  , searchable: false
  , striped: true
  , bordered: true
  , compact: false
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable/disable row selection.
selectable :: Boolean -> TableProp
selectable b props = props { selectable = b }

-- | Enable/disable search box.
searchable :: Boolean -> TableProp
searchable b props = props { searchable = b }

-- | Enable/disable striped rows.
striped :: Boolean -> TableProp
striped b props = props { striped = b }

-- | Enable/disable borders.
bordered :: Boolean -> TableProp
bordered b props = props { bordered = b }

-- | Use compact row spacing.
compact :: Boolean -> TableProp
compact b props = props { compact = b }

-- | Add custom CSS class.
className :: String -> TableProp
className c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // pagination helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate total pages from item count and page size.
totalPages :: Int -> Int -> Int
totalPages itemCount pageSize =
  if pageSize <= 0
    then 0
    else 
      let full = itemCount / pageSize
          remainder = itemCount - (full * pageSize)
      in if remainder > 0 then full + 1 else full

-- | Check if there's a next page.
hasNextPage :: Pagination -> Boolean
hasNextPage p = p.page < p.totalPages

-- | Check if there's a previous page.
hasPrevPage :: Pagination -> Boolean
hasPrevPage p = p.page > 1

-- | Get page range for pagination display.
-- |
-- | Returns array of page numbers to display, with -1 for ellipsis.
pageRange :: Pagination -> Int -> Array Int
pageRange p maxVisible =
  let
    total = p.totalPages
    current = p.page
    half = maxVisible / 2
    
    start = if current - half < 1 then 1 else current - half
    end = if start + maxVisible - 1 > total then total else start + maxVisible - 1
    adjustedStart = if end - start + 1 < maxVisible && start > 1
                      then if end - maxVisible + 1 < 1 then 1 else end - maxVisible + 1
                      else start
  in
    range adjustedStart end

-- | Generate integer range.
range :: Int -> Int -> Array Int
range start end = range' start end []
  where
    range' :: Int -> Int -> Array Int -> Array Int
    range' s e acc
      | s > e = acc
      | otherwise = range' (s + 1) e (acc <> [s])

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a table widget.
-- |
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
tableWidget :: forall msg. Array TableProp -> TableData -> E.Element msg
tableWidget propMods tableData =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    containerCls = "rounded-lg border bg-card text-card-foreground overflow-hidden" <> 
                   " " <> props.className
    
    tableCls = "w-full" <>
               (if props.bordered then " divide-y" else "") <>
               (if props.compact then " text-sm" else "")
  in
    E.div_
      [ E.class_ containerCls ]
      [ -- Search box
        if tableData.searchable || props.searchable
          then renderSearchBox
          else E.text ""
      
      -- Table
      , E.div_
          [ E.class_ "overflow-x-auto" ]
          [ E.table_
              [ E.class_ tableCls ]
              [ renderTableHeader tableData.columns tableData.sortBy tableData.sortDir
              , renderTableBody props tableData.columns tableData.rows
              ]
          ]
      
      -- Pagination
      , case tableData.pagination of
          Just p -> renderPagination p
          Nothing -> E.text ""
      ]

-- | Simple table widget (minimal configuration).
tableWidgetSimple :: forall msg. 
  Array String ->          -- ^ Column labels
  Array (Array String) ->  -- ^ Row data as strings
  E.Element msg
tableWidgetSimple headers rows =
  let
    columns = mapWithIndex (\idx label ->
      { key: "col" <> show idx
      , label: label
      , colType: ColText
      , width: Nothing
      , align: Nothing
      , sortable: false
      , format: Nothing
      }
    ) headers
    
    tableRows = mapWithIndex (\_ row ->
      mapWithIndex (\_ cell -> TextCell cell) row
    ) rows
    
    tableData :: TableData
    tableData =
      { columns: columns
      , rows: tableRows
      , pagination: Nothing
      , sortBy: Nothing
      , sortDir: Nothing
      , selectable: false
      , searchable: false
      }
  in
    tableWidget [] tableData

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // render helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render search box.
renderSearchBox :: forall msg. E.Element msg
renderSearchBox =
  E.div_
    [ E.class_ "p-4 border-b" ]
    [ E.input_
        [ E.attr "type" "search"
        , E.attr "placeholder" "Search..."
        , E.class_ "w-full px-3 py-2 border rounded-md text-sm bg-background"
        ]
    ]

-- | Render table header.
renderTableHeader :: forall msg. 
  Array ColumnDef -> 
  Maybe String -> 
  Maybe SortDirection -> 
  E.Element msg
renderTableHeader columns sortBy sortDir =
  E.thead_
    [ E.class_ "bg-muted/50" ]
    [ E.tr_
        []
        (mapWithIndex (\_ col -> renderHeaderCell col sortBy sortDir) columns)
    ]

-- | Render header cell.
renderHeaderCell :: forall msg. 
  ColumnDef -> 
  Maybe String -> 
  Maybe SortDirection -> 
  E.Element msg
renderHeaderCell col sortBy sortDir =
  let
    isSorted = sortBy == Just col.key
    sortIcon = if isSorted
                 then case sortDir of
                   Just SortAsc -> " ↑"
                   Just SortDesc -> " ↓"
                   Nothing -> ""
                 else ""
    
    alignCls = case col.align of
      Just "center" -> "text-center"
      Just "right" -> "text-right"
      _ -> "text-left"
    
    widthStyle = case col.width of
      Just w -> [ E.style "width" (show w <> "px") ]
      Nothing -> []
    
    cellCls = "px-4 py-3 font-medium text-sm " <> alignCls <>
              (if col.sortable then " cursor-pointer hover:bg-muted" else "")
  in
    E.th_
      ([ E.class_ cellCls ] <> widthStyle)
      [ E.text (col.label <> sortIcon) ]

-- | Render table body.
renderTableBody :: forall msg. TableProps -> Array ColumnDef -> Array (Array CellValue) -> E.Element msg
renderTableBody props columns rows =
  E.tbody_
    [ E.class_ (if props.striped then "divide-y" else "") ]
    (mapWithIndex (\idx row -> renderTableRow props columns idx row) rows)

-- | Render table row.
renderTableRow :: forall msg. TableProps -> Array ColumnDef -> Int -> Array CellValue -> E.Element msg
renderTableRow props columns idx cells =
  let
    rowCls = (if props.striped && idx `mod` 2 == 1 then "bg-muted/30" else "") <>
             " hover:bg-muted/50 transition-colors"
  in
    E.tr_
      [ E.class_ rowCls ]
      (mapWithIndex (\colIdx cell ->
        let col = fromMaybe defaultColumn (index columns colIdx)
        in renderTableCell props col cell
      ) cells)

-- | Default column definition.
defaultColumn :: ColumnDef
defaultColumn =
  { key: ""
  , label: ""
  , colType: ColText
  , width: Nothing
  , align: Nothing
  , sortable: false
  , format: Nothing
  }

-- | Render table cell.
renderTableCell :: forall msg. TableProps -> ColumnDef -> CellValue -> E.Element msg
renderTableCell props col cell =
  let
    alignCls = case col.align of
      Just "center" -> "text-center"
      Just "right" -> "text-right"
      _ -> "text-left"
    
    paddingCls = if props.compact then "px-3 py-2" else "px-4 py-3"
    cellCls = paddingCls <> " " <> alignCls
  in
    E.td_
      [ E.class_ cellCls ]
      [ renderCellContent cell ]

-- | Render cell content based on type.
renderCellContent :: forall msg. CellValue -> E.Element msg
renderCellContent cell = case cell of
  TextCell s -> E.text s
  
  NumberCell n -> 
    E.span_ [ E.class_ "tabular-nums" ] [ E.text (formatNumber n) ]
  
  CurrencyCell n code ->
    E.span_ [ E.class_ "tabular-nums" ] 
      [ E.text (code <> " " <> formatNumber n) ]
  
  PercentCell n ->
    E.span_ [ E.class_ "tabular-nums" ] [ E.text (show n <> "%") ]
  
  DateCell s -> E.text s
  
  BoolCell b ->
    if b
      then E.span_ [ E.class_ "text-green-500" ] [ E.text "Yes" ]
      else E.span_ [ E.class_ "text-muted-foreground" ] [ E.text "No" ]
  
  BadgeCell text variant ->
    let
      variantCls = case variant of
        "success" -> "bg-green-100 text-green-800"
        "warning" -> "bg-yellow-100 text-yellow-800"
        "error" -> "bg-red-100 text-red-800"
        "info" -> "bg-blue-100 text-blue-800"
        _ -> "bg-gray-100 text-gray-800"
    in
      E.span_
        [ E.class_ ("px-2 py-1 rounded-full text-xs font-medium " <> variantCls) ]
        [ E.text text ]
  
  SparklineCell points ->
    renderMiniSparkline points
  
  ProgressCell pct ->
    let
      width = show (unwrapPercentage pct) <> "%"
    in
      E.div_
        [ E.class_ "w-24 h-2 bg-muted rounded-full overflow-hidden" ]
        [ E.div_
            [ E.class_ "h-full bg-primary rounded-full"
            , E.style "width" width
            ]
            []
        ]
  
  EmptyCell -> E.text "—"

-- | Render mini sparkline for table cell.
renderMiniSparkline :: forall msg. Array Number -> E.Element msg
renderMiniSparkline points =
  if length points <= 1
    then E.text "—"
    else
      let
        minVal = arrayMin points
        maxVal = arrayMax points
        range = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
        width = 60.0
        height = 20.0
        
        pathData = generateSparklinePath points width height minVal range
      in
        E.svg_
          [ E.attr "viewBox" ("0 0 " <> show width <> " " <> show height)
          , E.class_ "w-16 h-5"
          ]
          [ E.path_
              [ E.attr "d" pathData
              , E.attr "fill" "none"
              , E.attr "stroke" "currentColor"
              , E.attr "stroke-width" "1.5"
              , E.class_ "text-primary"
              ]
          ]

-- | Generate sparkline path.
generateSparklinePath :: Array Number -> Number -> Number -> Number -> Number -> String
generateSparklinePath points width height minVal range =
  let
    numPoints = length points
    step = if numPoints <= 1 then width else width / toNumber (numPoints - 1)
    
    pathParts = mapWithIndex (\idx val ->
      let x = toNumber idx * step
          y = height - ((val - minVal) / range * height)
      in if idx == 0
           then "M " <> show x <> " " <> show y
           else "L " <> show x <> " " <> show y
    ) points
  in
    foldl (\acc part -> acc <> " " <> part) "" pathParts

-- | Render pagination controls.
renderPagination :: forall msg. Pagination -> E.Element msg
renderPagination p =
  E.div_
    [ E.class_ "flex items-center justify-between px-4 py-3 border-t text-sm" ]
    [ -- Info text
      E.span_
        [ E.class_ "text-muted-foreground" ]
        [ E.text ("Page " <> show p.page <> " of " <> show p.totalPages <> 
                  " (" <> show p.total <> " items)") ]
    
    -- Navigation buttons
    , E.div_
        [ E.class_ "flex items-center gap-2" ]
        [ -- Previous button
          E.button_
            [ E.class_ ("px-3 py-1 rounded border " <>
                       if hasPrevPage p then "hover:bg-muted" else "opacity-50 cursor-not-allowed")
            , E.attr "disabled" (if hasPrevPage p then "false" else "true")
            ]
            [ E.text "Previous" ]
        
        -- Page numbers
        , E.div_
            [ E.class_ "flex items-center gap-1" ]
            (mapWithIndex (\_ pageNum ->
              E.button_
                [ E.class_ ("w-8 h-8 rounded " <>
                           if pageNum == p.page 
                             then "bg-primary text-primary-foreground"
                             else "hover:bg-muted")
                ]
                [ E.text (show pageNum) ]
            ) (pageRange p 5))
        
        -- Next button
        , E.button_
            [ E.class_ ("px-3 py-1 rounded border " <>
                       if hasNextPage p then "hover:bg-muted" else "opacity-50 cursor-not-allowed")
            , E.attr "disabled" (if hasNextPage p then "false" else "true")
            ]
            [ E.text "Next" ]
        ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // math helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get minimum value from array.
arrayMin :: Array Number -> Number
arrayMin arr = foldl min' (1.0 / 0.0) arr
  where
    min' a b = if a < b then a else b

-- | Get maximum value from array.
arrayMax :: Array Number -> Number
arrayMax arr = foldl max' (negate (1.0 / 0.0)) arr
  where
    max' a b = if a > b then a else b
    negate n = 0.0 - n

-- | Format number for display.
formatNumber :: Number -> String
formatNumber n = show n

-- | Convert Int to Number.
foreign import toNumber :: Int -> Number

-- | Integer modulo.
foreign import mod :: Int -> Int -> Int

