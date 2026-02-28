-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // datagrid // column
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataGrid Column — Column definition and prop builders.
-- |
-- | This module provides the column constructor and property modifier functions
-- | for defining DataGrid columns. Each modifier follows the standard Hydrogen
-- | pattern: a function that transforms ColumnDef.
-- |
-- | ## Usage
-- |
-- | ```purescript
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
-- | ```

module Hydrogen.Element.Compound.DataGrid.Column
  ( -- * Column Constructor
    column
  
    -- * Dimension Props
  , colWidth
  , colMinWidth
  , colMaxWidth
  
    -- * Behavior Props
  , sortable
  , filterable
  , resizable
  , notResizable
  , editable
  , hidden
  
    -- * Position Props
  , fixedLeft
  , fixedRight
  
    -- * Rendering Props
  , cellType
  , cellRenderer
  , headerRenderer
  ) where

import Data.Array (foldl)
import Data.Maybe (Maybe(Just))

import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.DataGrid.Types
  ( CellType
  , CellContext
  , ColumnDef
  , ColumnProp
  , FixedPosition(FixedLeft, FixedRight)
  , defaultColumnDef
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // column constructor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a column definition
-- |
-- | Takes a key (matching row data), header text, and array of property modifiers.
-- | The key is used to extract cell values from row data objects.
-- |
-- | ```purescript
-- | Col.column "email" "Email Address"
-- |   [ Col.sortable
-- |   , Col.filterable
-- |   , Col.colMinWidth 200
-- |   ]
-- | ```
column :: forall msg. String -> String -> Array (ColumnProp msg) -> ColumnDef msg
column key header props = foldl (\c f -> f c) (defaultColumnDef key header) props

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // dimension props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set fixed column width in pixels
-- |
-- | When set, the column will not auto-size and will maintain this exact width.
colWidth :: forall msg. Int -> ColumnProp msg
colWidth w col = col { width = Just w }

-- | Set minimum column width in pixels
-- |
-- | Used during column resizing to prevent columns from becoming too narrow.
colMinWidth :: forall msg. Int -> ColumnProp msg
colMinWidth w col = col { minWidth = Just w }

-- | Set maximum column width in pixels
-- |
-- | Used during column resizing to prevent columns from becoming too wide.
colMaxWidth :: forall msg. Int -> ColumnProp msg
colMaxWidth w col = col { maxWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // behavior props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Make column sortable
-- |
-- | Sortable columns show sort indicators in the header and respond to clicks.
-- | Shift+click enables multi-column sorting.
sortable :: forall msg. ColumnProp msg
sortable col = col { sortable = true }

-- | Make column filterable
-- |
-- | Filterable columns show a filter input in the header and participate
-- | in global search filtering.
filterable :: forall msg. ColumnProp msg
filterable col = col { filterable = true }

-- | Make column resizable (enabled by default)
-- |
-- | Resizable columns show a drag handle for width adjustment.
resizable :: forall msg. ColumnProp msg
resizable col = col { resizable = true }

-- | Disable column resizing
-- |
-- | Use this to prevent users from resizing specific columns.
notResizable :: forall msg. ColumnProp msg
notResizable col = col { resizable = false }

-- | Make cells editable
-- |
-- | Editable cells can be clicked to enter edit mode. The grid will emit
-- | onCellEdit events when values change.
editable :: forall msg. ColumnProp msg
editable col = col { editable = true }

-- | Hide column
-- |
-- | Hidden columns are not rendered but their data remains available
-- | for filtering, sorting, and export operations.
hidden :: forall msg. ColumnProp msg
hidden col = col { hidden = true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // position props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fix column to left edge
-- |
-- | Fixed left columns remain visible during horizontal scrolling,
-- | staying pinned to the left edge of the grid viewport.
fixedLeft :: forall msg. ColumnProp msg
fixedLeft col = col { fixed = FixedLeft }

-- | Fix column to right edge
-- |
-- | Fixed right columns remain visible during horizontal scrolling,
-- | staying pinned to the right edge of the grid viewport.
fixedRight :: forall msg. ColumnProp msg
fixedRight col = col { fixed = FixedRight }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // rendering props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set cell type for built-in rendering
-- |
-- | The cell type determines how cell values are displayed:
-- | - CellText: Plain text (default)
-- | - CellNumber: Right-aligned, tabular figures
-- | - CellDate: Date formatting
-- | - CellBoolean: Checkbox (read-only)
-- | - CellLink: Clickable hyperlink
-- | - CellBadge: Badge/tag display
-- | - CellActions: Edit/delete action buttons
-- | - CellCustom: Requires cellRenderer
cellType :: forall msg. CellType -> ColumnProp msg
cellType t col = col { cellType = t }

-- | Set custom cell renderer
-- |
-- | Overrides the built-in cell type rendering with a custom function.
-- | The renderer receives CellContext with value, row data, and state.
-- |
-- | ```purescript
-- | Col.cellRenderer \ctx ->
-- |   E.span_
-- |     [ E.style "font-weight" "bold" ]
-- |     [ E.text ctx.value ]
-- | ```
cellRenderer :: forall msg. (CellContext -> E.Element msg) -> ColumnProp msg
cellRenderer r col = col { cellRenderer = Just r }

-- | Set custom header renderer
-- |
-- | Overrides the default header text rendering with a custom function.
-- | The renderer receives the header text string.
-- |
-- | ```purescript
-- | Col.headerRenderer \headerText ->
-- |   E.div_
-- |     [ E.class_ "flex items-center gap-2" ]
-- |     [ icon, E.text headerText ]
-- | ```
headerRenderer :: forall msg. (String -> E.Element msg) -> ColumnProp msg
headerRenderer r col = col { headerRenderer = Just r }
