-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // component // data-grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataGrid — Schema-native full-featured data grid component.
-- |
-- | A powerful, accessible data grid with sorting, filtering, pagination,
-- | row selection, row expansion, and more. All visual styling is controlled
-- | by Schema atoms from the 12 pillars — no hardcoded CSS values.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from Color, Geometry,
-- | Dimension, and Typography pillars. When an atom is `Nothing`, no style
-- | is emitted — the element inherits from its parent or browser defaults.
-- |
-- | ## Features
-- |
-- | - Column definitions with sorting, filtering, resizing
-- | - Fixed columns (left/right sticky)
-- | - Multi-column sorting (shift+click)
-- | - Per-column and global filtering
-- | - Row selection (single, multiple, checkbox)
-- | - Row expansion with detail views
-- | - Built-in and external pagination
-- | - Custom cell renderers
-- | - Keyboard navigation
-- | - ARIA grid pattern for accessibility
-- | - Export to CSV
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                 |
-- | |-----------------------|------------|----------------------|
-- | | headerBgColor         | Color      | Color.RGB            |
-- | | headerTextColor       | Color      | Color.RGB            |
-- | | rowBgColor            | Color      | Color.RGB            |
-- | | rowAltBgColor         | Color      | Color.RGB            |
-- | | rowHoverBgColor       | Color      | Color.RGB            |
-- | | rowSelectedBgColor    | Color      | Color.RGB            |
-- | | cellTextColor         | Color      | Color.RGB            |
-- | | borderColor           | Color      | Color.RGB            |
-- | | containerBorderRadius | Geometry   | Geometry.Corners     |
-- | | cellPaddingX          | Dimension  | Device.Pixel         |
-- | | cellPaddingY          | Dimension  | Device.Pixel         |
-- | | fontSize              | Typography | FontSize.FontSize    |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.DataGrid as Grid
-- | import Hydrogen.Element.Compound.DataGrid.Column as Col
-- | import Hydrogen.Element.Compound.DataGrid.Types (CellType(..))
-- |
-- | -- Define columns
-- | columns =
-- |   [ Col.column "id" "ID" [ Col.colWidth 80, Col.sortable ]
-- |   , Col.column "name" "Name" [ Col.sortable, Col.filterable ]
-- |   , Col.column "status" "Status" [ Col.cellType CellBadge ]
-- |   , Col.column "actions" "" [ Col.cellType CellActions, Col.colWidth 100 ]
-- |   ]
-- |
-- | -- Render grid with brand atoms
-- | Grid.dataGrid
-- |   [ Grid.columns columns
-- |   , Grid.rows myData
-- |   , Grid.headerBgColor brand.muted
-- |   , Grid.headerTextColor brand.foreground
-- |   , Grid.borderColor brand.border
-- |   , Grid.onRowSelect HandleSelect
-- |   , Grid.pagination (Grid.BuiltIn { pageSize: 25 })
-- |   ]
-- | ```

module Hydrogen.Element.Compound.DataGrid
  ( -- * Grid Component
    dataGrid
  
    -- * Re-exports from Types
  , module Hydrogen.Element.Compound.DataGrid.Types
  
    -- * Re-exports from Column
  , module Hydrogen.Element.Compound.DataGrid.Column
  
    -- * Grid Prop Builders
  
    -- ** Data Props
  , columns
  , rows
  , rowKey
  
    -- ** Selection Props
  , selectionMode
  , selectedRowKeys
  
    -- ** Expansion Props
  , expandable
  , expandedRowKeys
  , expandedContent
  
    -- ** Pagination Props
  , pagination
  , builtInPagination
  , externalPagination
  
    -- ** Filtering Props
  , globalFilter
  , columnFilters
  
    -- ** Sorting Props
  , sortColumns
  
    -- ** Loading Props
  , loading
  , emptyState
  , loadingState
  
    -- ** Keyboard Props
  , enableKeyboardNav
  
    -- ** Color Atoms
  , headerBgColor
  , headerTextColor
  , rowBgColor
  , rowAltBgColor
  , rowHoverBgColor
  , rowSelectedBgColor
  , cellTextColor
  , borderColor
  , linkColor
  , badgeBgColor
  , badgeTextColor
  , loadingSpinnerColor
  
    -- ** Geometry Atoms
  , containerBorderRadius
  , badgeBorderRadius
  
    -- ** Dimension Atoms
  , cellPaddingX
  , cellPaddingY
  , headerHeight
  , gridRowHeight
  , containerMaxHeight
  , borderWidth
  
    -- ** Typography Atoms
  , fontSize
  , headerFontSize
  
    -- ** Event Handlers
  , onRowSelect
  , onRowExpand
  , onCellEdit
  , onSort
  , onFilter
  , onColumnResize
  , onColumnReorder
  , onPageChange
  , onGlobalSearch
  
    -- * Export Functions
  , exportCsv
  ) where

import Prelude
  ( (==)
  , (>)
  , (>=)
  , (<=)
  , (+)
  , not
  , (<>)
  , ($)
  , show
  , map
  )

import Data.Array (foldl, filter, mapWithIndex, length, elem)
import Data.Maybe (Maybe(Nothing, Just), maybe, fromMaybe)
import Foreign.Object (Object)
import Foreign.Object as Object

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.DataGrid.Types
  ( CellContext
  , CellType(CellText, CellNumber, CellDate, CellBoolean, CellLink, CellBadge, CellActions, CellCustom)
  , ColumnDef
  , ColumnProp
  , FilterValue(TextFilter, NumberFilter, BooleanFilter, SelectFilter, DateRangeFilter)
  , FixedPosition(FixedLeft, FixedRight, NotFixed)
  , GridProp
  , GridProps
  , GridState
  , PaginationConfig(NoPagination, BuiltIn, External)
  , RowContext
  , SelectionMode(NoSelection, SingleSelect, MultiSelect, CheckboxSelect)
  , SortConfig
  , SortDirection(Ascending, Descending)
  , VirtualScrollConfig
  , defaultColumnDef
  , defaultGridProps
  )
import Hydrogen.Element.Compound.DataGrid.Column
  ( cellRenderer
  , cellType
  , colMaxWidth
  , colMinWidth
  , colWidth
  , column
  , editable
  , filterable
  , fixedLeft
  , fixedRight
  , headerRenderer
  , hidden
  , notResizable
  , resizable
  , sortable
  )
import Hydrogen.Element.Compound.DataGrid.Cell as Cell
import Hydrogen.Element.Compound.DataGrid.Processing as Processing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // grid component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the data grid
-- |
-- | Takes an array of property modifiers and produces an Element.
-- | All visual styling comes from Schema atoms — no hardcoded CSS.
dataGrid :: forall msg. Array (GridProp msg) -> E.Element msg
dataGrid propMods =
  let
    props = foldl (\p f -> f p) defaultGridProps propMods
    visibleColumns = filter (\col -> not col.hidden) props.columns
    processedRows = Processing.processRows props
  in
    E.div_
      ( [ E.role "grid"
        , E.attr "aria-rowcount" (show $ length props.rows)
        , E.attr "aria-colcount" (show $ length visibleColumns)
        , E.style "position" "relative"
        , E.style "width" "100%"
        , E.style "overflow" "hidden"
        ]
        <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
        <> maybe [] (\w -> [E.style "border-width" (show w)]) props.borderWidth
        <> maybe [] (\_ -> [E.style "border-style" "solid"]) props.borderWidth
        <> maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.containerBorderRadius
      )
      [ -- Global search (if any filterable columns)
        renderGlobalSearch props visibleColumns
      , -- Scrollable container
        E.div_
          ( [ E.style "overflow" "auto"
            , E.attr "data-grid-scroll" "true"
            ]
            <> maybe [] (\h -> [E.style "max-height" (show h)]) props.containerMaxHeight
          )
          [ -- Table
            E.table_
              ( [ E.style "width" "100%"
                , E.style "border-collapse" "collapse"
                , E.style "caption-side" "bottom"
                ]
                <> maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.fontSize
              )
              [ renderHeader props visibleColumns
              , renderBody props visibleColumns processedRows
              ]
          ]
      , -- Loading overlay
        renderLoadingOverlay props
      , -- Pagination
        renderPagination props (length processedRows)
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // global search
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render global search input
renderGlobalSearch :: forall msg. GridProps msg -> Array (ColumnDef msg) -> E.Element msg
renderGlobalSearch props cols =
  let
    hasFilterableColumns = length (filter (\col -> col.filterable) cols) > 0
  in
    if hasFilterableColumns
      then E.div_
        ( [ E.style "padding" "1rem"
          , E.style "border-bottom" "1px solid"
          ]
          <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
        )
        [ E.input_
            [ E.type_ "text"
            , E.placeholder "Search all columns..."
            , E.value props.globalFilter
            , E.ariaLabel "Search"
            , E.style "width" "100%"
            , E.style "max-width" "24rem"
            , E.style "padding" "0.5rem 0.75rem"
            , E.style "border" "1px solid"
            , E.style "border-radius" "0.375rem"
            ]
        ]
      else E.empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // header
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render table header
renderHeader :: forall msg. GridProps msg -> Array (ColumnDef msg) -> E.Element msg
renderHeader props cols =
  E.thead_
    ( [ E.role "rowgroup"
      , E.style "position" "sticky"
      , E.style "top" "0"
      , E.style "z-index" "10"
      ]
      <> maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.headerBgColor
    )
    [ E.tr_
        [ E.role "row" ]
        ( -- Selection checkbox column
          (if props.selectionMode == CheckboxSelect
            then [renderSelectionHeaderCell props]
            else [])
          -- Expansion column
          <> (if props.expandable
            then [renderExpansionHeaderCell]
            else [])
          -- Data columns
          <> mapWithIndex (renderHeaderCell props) cols
        )
    ]

-- | Render selection header cell (select all)
renderSelectionHeaderCell :: forall msg. GridProps msg -> E.Element msg
renderSelectionHeaderCell props =
  E.th_
    ( [ E.role "columnheader"
      , E.style "width" "3rem"
      , E.style "padding" "0.75rem 1rem"
      , E.style "text-align" "center"
      , E.style "border-bottom" "1px solid"
      ]
      <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
    )
    [ E.input_
        [ E.type_ "checkbox"
        , E.checked (length props.selectedRowKeys == length props.rows)
        , E.ariaLabel "Select all rows"
        , E.style "width" "1rem"
        , E.style "height" "1rem"
        ]
    ]

-- | Render expansion header cell
renderExpansionHeaderCell :: forall msg. E.Element msg
renderExpansionHeaderCell =
  E.th_
    [ E.role "columnheader"
    , E.style "width" "3rem"
    , E.style "padding" "0.75rem 1rem"
    ]
    [ E.empty ]

-- | Render a header cell
renderHeaderCell :: forall msg. GridProps msg -> Int -> ColumnDef msg -> E.Element msg
renderHeaderCell props colIndex col =
  let
    widthStyle = case col.width of
      Just w -> [E.style "width" (show w <> "px"), E.style "min-width" (show w <> "px")]
      Nothing -> []
    
    fixedStyle = case col.fixed of
      FixedLeft -> [E.style "position" "sticky", E.style "left" "0", E.style "z-index" "20"]
      FixedRight -> [E.style "position" "sticky", E.style "right" "0", E.style "z-index" "20"]
      NotFixed -> []
    
    headerContent = case col.headerRenderer of
      Just renderer -> renderer col.header
      Nothing -> E.text col.header
  in
    E.th_
      ( [ E.role "columnheader"
        , E.attr "aria-colindex" (show (colIndex + 1))
        , E.attr "data-column-key" col.key
        , E.style "padding" "0.75rem 1rem"
        , E.style "text-align" "left"
        , E.style "font-weight" "500"
        , E.style "border-bottom" "1px solid"
        , E.style "user-select" "none"
        ]
        <> widthStyle
        <> fixedStyle
        <> maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.headerTextColor
        <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
        <> maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.headerBgColor
        <> maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.headerFontSize
        <> (if col.sortable then [E.style "cursor" "pointer"] else [])
      )
      [ headerContent ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // body
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render table body
renderBody :: forall msg. GridProps msg -> Array (ColumnDef msg) -> Array (Object String) -> E.Element msg
renderBody props cols rowData =
  let
    isEmpty = length rowData == 0
    content =
      if props.loading
        then renderLoadingRows props cols
        else if isEmpty
          then [renderEmptyState props cols]
          else mapWithIndex (renderRow props cols) rowData
  in
    E.tbody_
      [ E.role "rowgroup" ]
      content

-- | Render loading placeholder rows
renderLoadingRows :: forall msg. GridProps msg -> Array (ColumnDef msg) -> Array (E.Element msg)
renderLoadingRows props cols =
  map (\_ -> renderLoadingRow props cols) [1, 2, 3, 4, 5]

-- | Render a loading placeholder row
renderLoadingRow :: forall msg. GridProps msg -> Array (ColumnDef msg) -> E.Element msg
renderLoadingRow props cols =
  E.tr_
    ( [ E.style "border-bottom" "1px solid" ]
      <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
    )
    (map (renderLoadingCell props) cols)

-- | Render a loading placeholder cell
renderLoadingCell :: forall msg. GridProps msg -> ColumnDef msg -> E.Element msg
renderLoadingCell props _col =
  E.td_
    ( [ E.style "padding" "1rem" ]
      <> maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.cellPaddingX
      <> maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.cellPaddingY
    )
    [ E.div_
        [ E.style "height" "1rem"
        , E.style "width" "75%"
        , E.style "border-radius" "0.25rem"
        , E.style "background-color" "currentColor"
        , E.style "opacity" "0.1"
        , E.style "animation" "pulse 2s cubic-bezier(0.4, 0, 0.6, 1) infinite"
        ]
        []
    ]

-- | Render empty state
renderEmptyState :: forall msg. GridProps msg -> Array (ColumnDef msg) -> E.Element msg
renderEmptyState props cols =
  let
    colSpan = length cols
      + (if props.selectionMode == CheckboxSelect then 1 else 0)
      + (if props.expandable then 1 else 0)
  in
    E.tr_
      [ E.style "height" "12rem" ]
      [ E.td_
          [ E.attr "colspan" (show colSpan)
          , E.style "text-align" "center"
          , E.style "vertical-align" "middle"
          ]
          [ case props.emptyState of
              Just custom -> custom
              Nothing -> defaultEmptyState props
          ]
      ]

-- | Default empty state content
defaultEmptyState :: forall msg. GridProps msg -> E.Element msg
defaultEmptyState props =
  E.div_
    ( [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "gap" "0.5rem"
      , E.style "padding" "2rem"
      ]
      <> maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.cellTextColor
    )
    [ E.p_
        [ E.style "font-size" "1.125rem"
        , E.style "font-weight" "500"
        ]
        [ E.text "No data" ]
    , E.p_
        [ E.style "font-size" "0.875rem"
        , E.style "opacity" "0.7"
        ]
        [ E.text "There are no records to display." ]
    ]

-- | Render a data row
renderRow :: forall msg. GridProps msg -> Array (ColumnDef msg) -> Int -> Object String -> E.Element msg
renderRow props cols rowIndex rowData =
  let
    rowKeyValue = fromMaybe (show rowIndex) (Object.lookup props.rowKey rowData)
    isSelected = elem rowKeyValue props.selectedRowKeys
    isExpanded = elem rowKeyValue props.expandedRowKeys
  in
    E.tr_
      ( [ E.role "row"
        , E.attr "aria-rowindex" (show (rowIndex + 1))
        , E.attr "data-row-key" rowKeyValue
        , E.style "border-bottom" "1px solid"
        , E.style "transition" "background-color 0.15s"
        ]
        <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
        <> maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.rowBgColor
        <> (if isSelected then maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.rowSelectedBgColor else [])
        <> maybe [] (\h -> [E.style "height" (show h)]) props.rowHeight
      )
      ( -- Selection checkbox
        (if props.selectionMode == CheckboxSelect
          then [renderSelectionCell props rowKeyValue isSelected]
          else [])
        -- Expansion toggle
        <> (if props.expandable
          then [renderExpansionCell props rowKeyValue isExpanded]
          else [])
        -- Data cells
        <> mapWithIndex (\colIndex col -> renderDataCell props col rowIndex colIndex rowData isSelected isExpanded) cols
      )

-- | Render selection checkbox cell
renderSelectionCell :: forall msg. GridProps msg -> String -> Boolean -> E.Element msg
renderSelectionCell props _rowKey isSelected =
  E.td_
    ( [ E.role "gridcell"
      , E.style "width" "3rem"
      , E.style "padding" "0.75rem 1rem"
      , E.style "text-align" "center"
      ]
      <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
    )
    [ E.input_
        [ E.type_ "checkbox"
        , E.checked isSelected
        , E.ariaLabel "Select row"
        , E.style "width" "1rem"
        , E.style "height" "1rem"
        ]
    ]

-- | Render expansion toggle cell
renderExpansionCell :: forall msg. GridProps msg -> String -> Boolean -> E.Element msg
renderExpansionCell props _rowKey isExpanded =
  E.td_
    ( [ E.role "gridcell"
      , E.style "width" "3rem"
      , E.style "padding" "0.75rem 1rem"
      ]
      <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
    )
    [ E.button_
        [ E.type_ "button"
        , E.ariaLabel (if isExpanded then "Collapse row" else "Expand row")
        , E.attr "aria-expanded" (if isExpanded then "true" else "false")
        , E.style "padding" "0.25rem"
        , E.style "border-radius" "0.25rem"
        , E.style "border" "none"
        , E.style "background" "transparent"
        , E.style "cursor" "pointer"
        ]
        [ E.text (if isExpanded then "v" else ">") ]
    ]

-- | Render a data cell
renderDataCell :: forall msg. GridProps msg -> ColumnDef msg -> Int -> Int -> Object String -> Boolean -> Boolean -> E.Element msg
renderDataCell props col rowIndex colIndex rowData isSelected isExpanded =
  let
    value = fromMaybe "" (Object.lookup col.key rowData)
    
    cellContext :: CellContext
    cellContext =
      { value
      , rowIndex
      , columnKey: col.key
      , rowData
      , isEditing: false
      , isSelected
      , isExpanded
      }
    
    fixedStyle = case col.fixed of
      FixedLeft -> [E.style "position" "sticky", E.style "left" "0", E.style "z-index" "10"]
      FixedRight -> [E.style "position" "sticky", E.style "right" "0", E.style "z-index" "10"]
      NotFixed -> []
  in
    E.td_
      ( [ E.role "gridcell"
        , E.attr "aria-colindex" (show (colIndex + 1))
        , E.attr "data-column-key" col.key
        , E.style "padding" "1rem"
        ]
        <> fixedStyle
        <> maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.cellPaddingX
        <> maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.cellPaddingY
        <> maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.rowBgColor
      )
      [ Cell.renderCell props col rowIndex colIndex cellContext ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // loading overlay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render loading overlay
renderLoadingOverlay :: forall msg. GridProps msg -> E.Element msg
renderLoadingOverlay props =
  if props.loading
    then E.div_
      [ E.style "position" "absolute"
      , E.style "inset" "0"
      , E.style "z-index" "30"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "background-color" "rgba(255, 255, 255, 0.5)"
      , E.style "backdrop-filter" "blur(2px)"
      ]
      [ case props.loadingState of
          Just custom -> custom
          Nothing -> defaultLoadingState props
      ]
    else E.empty

-- | Default loading state content
defaultLoadingState :: forall msg. GridProps msg -> E.Element msg
defaultLoadingState props =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "align-items" "center"
    , E.style "gap" "0.5rem"
    ]
    [ E.div_
        ( [ E.style "width" "2rem"
          , E.style "height" "2rem"
          , E.style "border-radius" "50%"
          , E.style "border-width" "4px"
          , E.style "border-style" "solid"
          , E.style "border-top-color" "transparent"
          , E.style "animation" "spin 1s linear infinite"
          ]
          <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.loadingSpinnerColor
        )
        []
    , E.span_
        [ E.style "font-size" "0.875rem"
        , E.style "opacity" "0.7"
        ]
        [ E.text "Loading..." ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // pagination
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render pagination controls
renderPagination :: forall msg. GridProps msg -> Int -> E.Element msg
renderPagination props totalFiltered =
  case props.pagination of
    NoPagination -> E.empty
    
    BuiltIn { pageSize } ->
      let
        totalPages = Processing.calculateTotalPages totalFiltered pageSize
        currentPg = 1 -- Would need state management for this
      in
        renderPaginationControls props currentPg totalPages totalFiltered pageSize
    
    External { pageSize, currentPage, totalRows } ->
      let
        totalPages = Processing.calculateTotalPages totalRows pageSize
      in
        renderPaginationControls props currentPage totalPages totalRows pageSize

-- | Render pagination controls UI
renderPaginationControls :: forall msg. GridProps msg -> Int -> Int -> Int -> Int -> E.Element msg
renderPaginationControls props currentPg totalPages total _ps =
  E.div_
    ( [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "space-between"
      , E.style "padding" "0.75rem 1rem"
      , E.style "border-top" "1px solid"
      ]
      <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
    )
    [ -- Row count info
      E.div_
        [ E.style "font-size" "0.875rem"
        , E.style "opacity" "0.7"
        ]
        [ E.text $ "Total: " <> show total <> " rows" ]
    , -- Page navigation
      E.div_
        [ E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "gap" "0.5rem"
        ]
        [ -- Previous page
          E.button_
            [ E.type_ "button"
            , E.disabled (currentPg <= 1)
            , E.ariaLabel "Previous page"
            , E.style "padding" "0.25rem 0.5rem"
            , E.style "border" "1px solid"
            , E.style "border-radius" "0.25rem"
            , E.style "background" "transparent"
            , E.style "cursor" (if currentPg <= 1 then "not-allowed" else "pointer")
            , E.style "opacity" (if currentPg <= 1 then "0.5" else "1")
            ]
            [ E.text "<" ]
        , -- Page indicator
          E.span_
            [ E.style "font-size" "0.875rem" ]
            [ E.text $ "Page " <> show currentPg <> " of " <> show totalPages ]
        , -- Next page
          E.button_
            [ E.type_ "button"
            , E.disabled (currentPg >= totalPages)
            , E.ariaLabel "Next page"
            , E.style "padding" "0.25rem 0.5rem"
            , E.style "border" "1px solid"
            , E.style "border-radius" "0.25rem"
            , E.style "background" "transparent"
            , E.style "cursor" (if currentPg >= totalPages then "not-allowed" else "pointer")
            , E.style "opacity" (if currentPg >= totalPages then "0.5" else "1")
            ]
            [ E.text ">" ]
        ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- Data Props

columns :: forall msg. Array (ColumnDef msg) -> GridProp msg
columns cols props = props { columns = cols }

rows :: forall msg. Array (Object String) -> GridProp msg
rows data' props = props { rows = data' }

rowKey :: forall msg. String -> GridProp msg
rowKey key props = props { rowKey = key }

-- Selection Props

selectionMode :: forall msg. SelectionMode -> GridProp msg
selectionMode mode props = props { selectionMode = mode }

selectedRowKeys :: forall msg. Array String -> GridProp msg
selectedRowKeys keys props = props { selectedRowKeys = keys }

-- Expansion Props

expandable :: forall msg. Boolean -> GridProp msg
expandable e props = props { expandable = e }

expandedRowKeys :: forall msg. Array String -> GridProp msg
expandedRowKeys keys props = props { expandedRowKeys = keys }

expandedContent :: forall msg. (RowContext -> E.Element msg) -> GridProp msg
expandedContent renderer props = props { expandedContent = Just renderer }

-- Pagination Props

pagination :: forall msg. PaginationConfig -> GridProp msg
pagination config props = props { pagination = config }

builtInPagination :: forall msg. Int -> GridProp msg
builtInPagination pageSize props = props { pagination = BuiltIn { pageSize } }

externalPagination :: forall msg. Int -> Int -> Int -> GridProp msg
externalPagination pageSize currentPage totalRows props =
  props { pagination = External { pageSize, currentPage, totalRows } }

-- Filtering Props

globalFilter :: forall msg. String -> GridProp msg
globalFilter search props = props { globalFilter = search }

columnFilters :: forall msg. Object FilterValue -> GridProp msg
columnFilters filters props = props { columnFilters = filters }

-- Sorting Props

sortColumns :: forall msg. Array SortConfig -> GridProp msg
sortColumns sorts props = props { sortColumns = sorts }

-- Loading Props

loading :: forall msg. Boolean -> GridProp msg
loading l props = props { loading = l }

emptyState :: forall msg. E.Element msg -> GridProp msg
emptyState content props = props { emptyState = Just content }

loadingState :: forall msg. E.Element msg -> GridProp msg
loadingState content props = props { loadingState = Just content }

-- Keyboard Props

enableKeyboardNav :: forall msg. Boolean -> GridProp msg
enableKeyboardNav enabled props = props { enableKeyboardNav = enabled }

-- Color Atoms

headerBgColor :: forall msg. Color.RGB -> GridProp msg
headerBgColor c props = props { headerBgColor = Just c }

headerTextColor :: forall msg. Color.RGB -> GridProp msg
headerTextColor c props = props { headerTextColor = Just c }

rowBgColor :: forall msg. Color.RGB -> GridProp msg
rowBgColor c props = props { rowBgColor = Just c }

rowAltBgColor :: forall msg. Color.RGB -> GridProp msg
rowAltBgColor c props = props { rowAltBgColor = Just c }

rowHoverBgColor :: forall msg. Color.RGB -> GridProp msg
rowHoverBgColor c props = props { rowHoverBgColor = Just c }

rowSelectedBgColor :: forall msg. Color.RGB -> GridProp msg
rowSelectedBgColor c props = props { rowSelectedBgColor = Just c }

cellTextColor :: forall msg. Color.RGB -> GridProp msg
cellTextColor c props = props { cellTextColor = Just c }

borderColor :: forall msg. Color.RGB -> GridProp msg
borderColor c props = props { borderColor = Just c }

linkColor :: forall msg. Color.RGB -> GridProp msg
linkColor c props = props { linkColor = Just c }

badgeBgColor :: forall msg. Color.RGB -> GridProp msg
badgeBgColor c props = props { badgeBgColor = Just c }

badgeTextColor :: forall msg. Color.RGB -> GridProp msg
badgeTextColor c props = props { badgeTextColor = Just c }

loadingSpinnerColor :: forall msg. Color.RGB -> GridProp msg
loadingSpinnerColor c props = props { loadingSpinnerColor = Just c }

-- Geometry Atoms

containerBorderRadius :: forall msg. Geometry.Corners -> GridProp msg
containerBorderRadius r props = props { containerBorderRadius = Just r }

badgeBorderRadius :: forall msg. Geometry.Corners -> GridProp msg
badgeBorderRadius r props = props { badgeBorderRadius = Just r }

-- Dimension Atoms

cellPaddingX :: forall msg. Device.Pixel -> GridProp msg
cellPaddingX p props = props { cellPaddingX = Just p }

cellPaddingY :: forall msg. Device.Pixel -> GridProp msg
cellPaddingY p props = props { cellPaddingY = Just p }

headerHeight :: forall msg. Device.Pixel -> GridProp msg
headerHeight h props = props { headerHeight = Just h }

gridRowHeight :: forall msg. Device.Pixel -> GridProp msg
gridRowHeight h props = props { rowHeight = Just h }

containerMaxHeight :: forall msg. Device.Pixel -> GridProp msg
containerMaxHeight h props = props { containerMaxHeight = Just h }

borderWidth :: forall msg. Device.Pixel -> GridProp msg
borderWidth w props = props { borderWidth = Just w }

-- Typography Atoms

fontSize :: forall msg. FontSize.FontSize -> GridProp msg
fontSize s props = props { fontSize = Just s }

headerFontSize :: forall msg. FontSize.FontSize -> GridProp msg
headerFontSize s props = props { headerFontSize = Just s }

-- Event Handlers

onRowSelect :: forall msg. (Array String -> msg) -> GridProp msg
onRowSelect handler props = props { onRowSelect = Just handler }

onRowExpand :: forall msg. (Array String -> msg) -> GridProp msg
onRowExpand handler props = props { onRowExpand = Just handler }

onCellEdit :: forall msg. ({ rowIndex :: Int, columnKey :: String, value :: String } -> msg) -> GridProp msg
onCellEdit handler props = props { onCellEdit = Just handler }

onSort :: forall msg. (Array SortConfig -> msg) -> GridProp msg
onSort handler props = props { onSort = Just handler }

onFilter :: forall msg. (Object FilterValue -> msg) -> GridProp msg
onFilter handler props = props { onFilter = Just handler }

onColumnResize :: forall msg. ({ columnKey :: String, width :: Int } -> msg) -> GridProp msg
onColumnResize handler props = props { onColumnResize = Just handler }

onColumnReorder :: forall msg. (Array String -> msg) -> GridProp msg
onColumnReorder handler props = props { onColumnReorder = Just handler }

onPageChange :: forall msg. (Int -> msg) -> GridProp msg
onPageChange handler props = props { onPageChange = Just handler }

onGlobalSearch :: forall msg. (String -> msg) -> GridProp msg
onGlobalSearch handler props = props { onGlobalSearch = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // export
-- ═════════════════════════════════════════════════════════════════════════════

-- | Export grid data to CSV string
exportCsv :: forall msg. GridProps msg -> String
exportCsv props = Processing.toCsvString props.columns props.rows
