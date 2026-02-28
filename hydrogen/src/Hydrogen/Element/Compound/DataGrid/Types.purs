-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // datagrid // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataGrid Types — Type definitions for the Schema-native data grid.
-- |
-- | This module contains all type definitions used by the DataGrid component
-- | and its submodules. Types are designed to be Schema-native:
-- |
-- | - All visual properties accept concrete Schema atoms
-- | - No hardcoded CSS values anywhere
-- | - `Maybe` indicates optional properties (Nothing = inherit from context)
-- |
-- | ## Type Categories
-- |
-- | - **Enums**: CellType, FixedPosition, SortDirection, SelectionMode
-- | - **Configs**: SortConfig, VirtualScrollConfig, PaginationConfig
-- | - **Contexts**: CellContext, RowContext (passed to custom renderers)
-- | - **Column**: ColumnDef, ColumnProp
-- | - **Grid**: GridProps, GridProp, GridState

module Hydrogen.Element.Compound.DataGrid.Types
  ( -- * Cell Type Enum
    CellType(CellText, CellNumber, CellDate, CellBoolean, CellLink, CellBadge, CellActions, CellCustom)
  
    -- * Fixed Position Enum
  , FixedPosition(FixedLeft, FixedRight, NotFixed)
  
    -- * Sort Direction Enum
  , SortDirection(Ascending, Descending)
  
    -- * Selection Mode Enum
  , SelectionMode(NoSelection, SingleSelect, MultiSelect, CheckboxSelect)
  
    -- * Filter Value ADT
  , FilterValue(TextFilter, NumberFilter, BooleanFilter, SelectFilter, DateRangeFilter)
  
    -- * Sort Configuration
  , SortConfig
  
    -- * Virtual Scroll Configuration
  , VirtualScrollConfig
  
    -- * Pagination Configuration
  , PaginationConfig(NoPagination, BuiltIn, External)
  
    -- * Cell Context
  , CellContext
  
    -- * Row Context
  , RowContext
  
    -- * Grid State
  , GridState
  
    -- * Column Definition
  , ColumnDef
  , ColumnProp
  , defaultColumnDef
  
    -- * Grid Properties
  , GridProps
  , GridProp
  , defaultGridProps
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing))
import Foreign.Object (Object)
import Foreign.Object as Object

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // cell types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Built-in cell type renderers
-- |
-- | Each cell type has a default renderer that converts the cell value
-- | to appropriate Element output. Custom renderers can override these.
data CellType
  = CellText       -- ^ Plain text display
  | CellNumber     -- ^ Numeric with tabular figures
  | CellDate       -- ^ Date/time display
  | CellBoolean    -- ^ Checkbox display (read-only)
  | CellLink       -- ^ Clickable link
  | CellBadge      -- ^ Badge/tag display
  | CellActions    -- ^ Action buttons (edit, delete)
  | CellCustom     -- ^ Fully custom renderer required

derive instance eqCellType :: Eq CellType

instance showCellType :: Show CellType where
  show CellText = "CellText"
  show CellNumber = "CellNumber"
  show CellDate = "CellDate"
  show CellBoolean = "CellBoolean"
  show CellLink = "CellLink"
  show CellBadge = "CellBadge"
  show CellActions = "CellActions"
  show CellCustom = "CellCustom"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // fixed position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fixed column position
-- |
-- | Columns can be fixed (sticky) to the left or right edge of the grid,
-- | remaining visible during horizontal scrolling.
data FixedPosition
  = FixedLeft      -- ^ Sticky to left edge
  | FixedRight     -- ^ Sticky to right edge
  | NotFixed       -- ^ Normal scrolling behavior

derive instance eqFixedPosition :: Eq FixedPosition

instance showFixedPosition :: Show FixedPosition where
  show FixedLeft = "FixedLeft"
  show FixedRight = "FixedRight"
  show NotFixed = "NotFixed"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // sort direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sort direction for column sorting
data SortDirection
  = Ascending      -- ^ A-Z, 0-9, oldest first
  | Descending     -- ^ Z-A, 9-0, newest first

derive instance eqSortDirection :: Eq SortDirection

instance showSortDirection :: Show SortDirection where
  show Ascending = "Ascending"
  show Descending = "Descending"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // selection mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Row selection mode
-- |
-- | Determines how rows can be selected in the grid.
data SelectionMode
  = NoSelection       -- ^ Selection disabled
  | SingleSelect      -- ^ Click to select one row (deselects others)
  | MultiSelect       -- ^ Click to toggle selection (multiple rows)
  | CheckboxSelect    -- ^ Checkbox column for selection

derive instance eqSelectionMode :: Eq SelectionMode

instance showSelectionMode :: Show SelectionMode where
  show NoSelection = "NoSelection"
  show SingleSelect = "SingleSelect"
  show MultiSelect = "MultiSelect"
  show CheckboxSelect = "CheckboxSelect"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // filter value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter value types for column filtering
-- |
-- | Each filter type corresponds to how the column data should be filtered.
data FilterValue
  = TextFilter String
      -- ^ Text contains search string (case-insensitive)
  | NumberFilter { min :: Maybe Number, max :: Maybe Number }
      -- ^ Numeric range filter (inclusive)
  | BooleanFilter Boolean
      -- ^ Exact boolean match
  | SelectFilter (Array String)
      -- ^ Value must be one of the allowed values
  | DateRangeFilter { start :: Maybe String, end :: Maybe String }
      -- ^ Date range filter (ISO string format)

instance showFilterValue :: Show FilterValue where
  show (TextFilter s) = "TextFilter " <> show s
  show (NumberFilter r) = "NumberFilter { min: " <> show r.min <> ", max: " <> show r.max <> " }"
  show (BooleanFilter b) = "BooleanFilter " <> show b
  show (SelectFilter arr) = "SelectFilter " <> show arr
  show (DateRangeFilter r) = "DateRangeFilter { start: " <> show r.start <> ", end: " <> show r.end <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // sort config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sort configuration for a single column
-- |
-- | Multiple SortConfig entries enable multi-column sorting (shift+click).
type SortConfig =
  { column :: String           -- ^ Column key to sort by
  , direction :: SortDirection -- ^ Sort direction
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // virtual scroll config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Virtual scroll configuration for large datasets
-- |
-- | When enabled, only visible rows are rendered to the DOM, dramatically
-- | improving performance for datasets with 100k+ rows.
type VirtualScrollConfig =
  { rowHeight :: Int       -- ^ Fixed row height in pixels (required for virtual scroll)
  , overscan :: Int        -- ^ Extra rows to render above/below viewport
  , containerHeight :: Int -- ^ Viewport height in pixels
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // pagination config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pagination configuration
-- |
-- | The grid supports three pagination modes:
-- | - NoPagination: All rows visible (with optional virtual scroll)
-- | - BuiltIn: Grid manages pagination state internally
-- | - External: Parent manages pagination (for server-side pagination)
data PaginationConfig
  = NoPagination
      -- ^ No pagination, all rows displayed
  | BuiltIn { pageSize :: Int }
      -- ^ Grid manages pagination internally
  | External
      { pageSize :: Int
      , currentPage :: Int
      , totalRows :: Int
      }
      -- ^ External pagination (server-side)

derive instance eqPaginationConfig :: Eq PaginationConfig

instance showPaginationConfig :: Show PaginationConfig where
  show NoPagination = "NoPagination"
  show (BuiltIn { pageSize }) = "BuiltIn { pageSize: " <> show pageSize <> " }"
  show (External { pageSize, currentPage, totalRows }) = 
    "External { pageSize: " <> show pageSize 
    <> ", currentPage: " <> show currentPage 
    <> ", totalRows: " <> show totalRows <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cell context
-- ═════════════════════════════════════════════════════════════════════════════

-- | Context passed to cell renderers
-- |
-- | Contains all information needed for custom cell rendering, including
-- | the cell value, position, full row data, and current interaction state.
type CellContext =
  { value :: String           -- ^ Cell value as string
  , rowIndex :: Int           -- ^ Zero-based row index
  , columnKey :: String       -- ^ Column key
  , rowData :: Object String  -- ^ Full row data (all columns)
  , isEditing :: Boolean      -- ^ Cell is in edit mode
  , isSelected :: Boolean     -- ^ Row is selected
  , isExpanded :: Boolean     -- ^ Row is expanded
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // row context
-- ═════════════════════════════════════════════════════════════════════════════

-- | Context for row-level operations
-- |
-- | Used for expanded content renderers and row-level customization.
type RowContext =
  { rowIndex :: Int           -- ^ Zero-based row index
  , rowData :: Object String  -- ^ Full row data (all columns)
  , isSelected :: Boolean     -- ^ Row is selected
  , isExpanded :: Boolean     -- ^ Row is expanded
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // grid state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Internal grid state
-- |
-- | Exposed for advanced usage patterns where external state management
-- | is required (e.g., persisting grid state to localStorage).
type GridState =
  { sortColumns :: Array SortConfig       -- ^ Current sort configuration
  , filters :: Object FilterValue         -- ^ Column filters by key
  , globalFilter :: String                -- ^ Global search filter
  , selectedRowKeys :: Array String       -- ^ Selected row keys
  , expandedRowKeys :: Array String       -- ^ Expanded row keys
  , editingCell :: Maybe { rowIndex :: Int, columnKey :: String }
  , currentPage :: Int                    -- ^ Current page (1-indexed)
  , pageSize :: Int                       -- ^ Rows per page
  , columnWidths :: Object Int            -- ^ Column widths by key
  , columnOrder :: Array String           -- ^ Column order (keys)
  , scrollTop :: Int                      -- ^ Scroll position
  , focusedCell :: Maybe { rowIndex :: Int, colIndex :: Int }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // column definition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Column definition
-- |
-- | Defines a single column in the grid, including its key, header,
-- | dimensions, behavior, and optional custom renderers.
-- |
-- | All visual properties accept Schema atoms via GridProps (not column-level).
-- | Column-level properties control behavior and structure.
type ColumnDef msg =
  { key :: String                -- ^ Unique column identifier (matches row data key)
  , header :: String             -- ^ Display header text
  , width :: Maybe Int           -- ^ Fixed width in pixels
  , minWidth :: Maybe Int        -- ^ Minimum width for resizing
  , maxWidth :: Maybe Int        -- ^ Maximum width for resizing
  , sortable :: Boolean          -- ^ Column can be sorted
  , filterable :: Boolean        -- ^ Column can be filtered
  , resizable :: Boolean         -- ^ Column width can be changed
  , fixed :: FixedPosition       -- ^ Sticky position
  , hidden :: Boolean            -- ^ Column is hidden
  , cellType :: CellType         -- ^ Cell rendering type
  , cellRenderer :: Maybe (CellContext -> E.Element msg)
      -- ^ Custom cell renderer (overrides cellType)
  , headerRenderer :: Maybe (String -> E.Element msg)
      -- ^ Custom header renderer
  , editable :: Boolean          -- ^ Cells can be edited inline
  }

-- | Column property modifier
type ColumnProp msg = ColumnDef msg -> ColumnDef msg

-- | Default column definition
-- |
-- | Creates a column with sensible defaults:
-- | - No fixed width (auto-sized)
-- | - Resizable enabled
-- | - Not sortable, not filterable
-- | - Text cell type
-- | - No custom renderers
defaultColumnDef :: forall msg. String -> String -> ColumnDef msg
defaultColumnDef key header =
  { key
  , header
  , width: Nothing
  , minWidth: Nothing
  , maxWidth: Nothing
  , sortable: false
  , filterable: false
  , resizable: true
  , fixed: NotFixed
  , hidden: false
  , cellType: CellText
  , cellRenderer: Nothing
  , headerRenderer: Nothing
  , editable: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // grid props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid properties
-- |
-- | All visual properties accept concrete Schema atoms from the 12 pillars.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.
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
-- | | headerBorderRadius    | Geometry   | Geometry.Corners     |
-- | | cellPaddingX          | Dimension  | Device.Pixel         |
-- | | cellPaddingY          | Dimension  | Device.Pixel         |
-- | | headerHeight          | Dimension  | Device.Pixel         |
-- | | rowHeight             | Dimension  | Device.Pixel         |
-- | | fontSize              | Typography | FontSize.FontSize    |
-- | | headerFontSize        | Typography | FontSize.FontSize    |
type GridProps msg =
  { -- Data
    columns :: Array (ColumnDef msg)
  , rows :: Array (Object String)
  , rowKey :: String                   -- ^ Key field for row identity
  
  -- Selection
  , selectionMode :: SelectionMode
  , selectedRowKeys :: Array String
  
  -- Expansion
  , expandable :: Boolean
  , expandedRowKeys :: Array String
  , expandedContent :: Maybe (RowContext -> E.Element msg)
  
  -- Pagination
  , pagination :: PaginationConfig
  
  -- Virtual Scroll
  , virtualScroll :: Maybe VirtualScrollConfig
  
  -- Filtering
  , globalFilter :: String
  , columnFilters :: Object FilterValue
  
  -- Sorting
  , sortColumns :: Array SortConfig
  
  -- Loading State
  , loading :: Boolean
  , emptyState :: Maybe (E.Element msg)
  , loadingState :: Maybe (E.Element msg)
  
  -- Keyboard Navigation
  , enableKeyboardNav :: Boolean
  
  -- Color Atoms
  , headerBgColor :: Maybe Color.RGB
  , headerTextColor :: Maybe Color.RGB
  , rowBgColor :: Maybe Color.RGB
  , rowAltBgColor :: Maybe Color.RGB
  , rowHoverBgColor :: Maybe Color.RGB
  , rowSelectedBgColor :: Maybe Color.RGB
  , cellTextColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , linkColor :: Maybe Color.RGB
  , badgeBgColor :: Maybe Color.RGB
  , badgeTextColor :: Maybe Color.RGB
  , loadingSpinnerColor :: Maybe Color.RGB
  
  -- Geometry Atoms
  , containerBorderRadius :: Maybe Geometry.Corners
  , badgeBorderRadius :: Maybe Geometry.Corners
  
  -- Dimension Atoms
  , cellPaddingX :: Maybe Device.Pixel
  , cellPaddingY :: Maybe Device.Pixel
  , headerHeight :: Maybe Device.Pixel
  , rowHeight :: Maybe Device.Pixel
  , containerMaxHeight :: Maybe Device.Pixel
  , borderWidth :: Maybe Device.Pixel
  
  -- Typography Atoms
  , fontSize :: Maybe FontSize.FontSize
  , headerFontSize :: Maybe FontSize.FontSize
  
  -- Event Handlers
  , onRowSelect :: Maybe (Array String -> msg)
  , onRowExpand :: Maybe (Array String -> msg)
  , onCellEdit :: Maybe ({ rowIndex :: Int, columnKey :: String, value :: String } -> msg)
  , onSort :: Maybe (Array SortConfig -> msg)
  , onFilter :: Maybe (Object FilterValue -> msg)
  , onColumnResize :: Maybe ({ columnKey :: String, width :: Int } -> msg)
  , onColumnReorder :: Maybe (Array String -> msg)
  , onPageChange :: Maybe (Int -> msg)
  , onGlobalSearch :: Maybe (String -> msg)
  }

-- | Grid property modifier
type GridProp msg = GridProps msg -> GridProps msg

-- | Default grid properties
-- |
-- | All visual atoms default to `Nothing` (inherit from context/brand).
-- | Behavior defaults are sensible for most use cases.
defaultGridProps :: forall msg. GridProps msg
defaultGridProps =
  { -- Data
    columns: []
  , rows: []
  , rowKey: "id"
  
  -- Selection
  , selectionMode: NoSelection
  , selectedRowKeys: []
  
  -- Expansion
  , expandable: false
  , expandedRowKeys: []
  , expandedContent: Nothing
  
  -- Pagination
  , pagination: NoPagination
  
  -- Virtual Scroll
  , virtualScroll: Nothing
  
  -- Filtering
  , globalFilter: ""
  , columnFilters: Object.empty
  
  -- Sorting
  , sortColumns: []
  
  -- Loading State
  , loading: false
  , emptyState: Nothing
  , loadingState: Nothing
  
  -- Keyboard Navigation
  , enableKeyboardNav: true
  
  -- Color Atoms (all inherit)
  , headerBgColor: Nothing
  , headerTextColor: Nothing
  , rowBgColor: Nothing
  , rowAltBgColor: Nothing
  , rowHoverBgColor: Nothing
  , rowSelectedBgColor: Nothing
  , cellTextColor: Nothing
  , borderColor: Nothing
  , linkColor: Nothing
  , badgeBgColor: Nothing
  , badgeTextColor: Nothing
  , loadingSpinnerColor: Nothing
  
  -- Geometry Atoms (all inherit)
  , containerBorderRadius: Nothing
  , badgeBorderRadius: Nothing
  
  -- Dimension Atoms (all inherit)
  , cellPaddingX: Nothing
  , cellPaddingY: Nothing
  , headerHeight: Nothing
  , rowHeight: Nothing
  , containerMaxHeight: Nothing
  , borderWidth: Nothing
  
  -- Typography Atoms (all inherit)
  , fontSize: Nothing
  , headerFontSize: Nothing
  
  -- Event Handlers (all optional)
  , onRowSelect: Nothing
  , onRowExpand: Nothing
  , onCellEdit: Nothing
  , onSort: Nothing
  , onFilter: Nothing
  , onColumnResize: Nothing
  , onColumnReorder: Nothing
  , onPageChange: Nothing
  , onGlobalSearch: Nothing
  }
