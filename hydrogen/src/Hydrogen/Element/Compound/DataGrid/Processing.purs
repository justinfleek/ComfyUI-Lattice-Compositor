-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // datagrid // processing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataGrid Processing — Filtering, sorting, and pagination logic.
-- |
-- | This module contains pure functions for data processing operations
-- | on grid row data. All functions are deterministic and side-effect free.
-- |
-- | ## Operations
-- |
-- | - **Filtering**: Global search and per-column filters
-- | - **Sorting**: Single and multi-column sorting
-- | - **Pagination**: Built-in and external pagination support
-- | - **Selection**: Row selection state management
-- |
-- | ## Design Philosophy
-- |
-- | Processing functions operate on `Array (Object String)` row data.
-- | They compose together: filter -> sort -> paginate.

module Hydrogen.Element.Compound.DataGrid.Processing
  ( -- * Data Processing Pipeline
    processRows
  
    -- * Filtering
  , applyGlobalFilter
  , applyColumnFilters
  , matchesGlobalFilter
  , matchesColumnFilter
  
    -- * Sorting
  , applySorting
  , applySingleSort
  
    -- * Pagination
  , applyPagination
  , calculateTotalPages
  
    -- * Selection Helpers
  , toggleSelection
  , selectAll
  , deselectAll
  , isRowSelected
  
    -- * Export
  , toCsvString
  , rowToCsv
  , escapeCsv
  ) where

import Prelude
  ( not
  , (==)
  , (>=)
  , (<=)
  , (&&)
  , (||)
  , (<>)
  , (-)
  , (+)
  , (/)
  , (*)
  )

import Data.Array (filter, foldl, sortBy, take, drop, reverse, elem, mapMaybe, any)
import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Number (fromString) as Number
import Data.Ord (comparing)
import Data.String (Pattern(Pattern), contains, toLower, null)
import Data.String as String
import Data.Tuple (Tuple(Tuple))
import Foreign.Object (Object)
import Foreign.Object as Object

import Hydrogen.Element.Compound.DataGrid.Types
  ( ColumnDef
  , FilterValue
      ( TextFilter
      , NumberFilter
      , BooleanFilter
      , SelectFilter
      , DateRangeFilter
      )
  , GridProps
  , PaginationConfig(NoPagination, BuiltIn, External)
  , SelectionMode(SingleSelect, MultiSelect, CheckboxSelect, NoSelection)
  , SortConfig
  , SortDirection(Ascending, Descending)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // processing pipeline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Process rows through the full pipeline: filter -> sort -> paginate
-- |
-- | This is the main entry point for data processing. It applies all
-- | configured filters, sorting, and pagination in the correct order.
processRows :: forall msg. GridProps msg -> Array (Object String)
processRows props =
  let
    -- Apply global filter
    globalFiltered = applyGlobalFilter props.globalFilter props.columns props.rows
    
    -- Apply column filters
    columnFiltered = applyColumnFilters props.columnFilters globalFiltered
    
    -- Apply sorting
    sorted = applySorting props.sortColumns columnFiltered
    
    -- Apply pagination
    paginated = applyPagination props.pagination sorted
  in
    paginated

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // filtering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply global filter to rows
-- |
-- | Searches across all filterable columns for the search string.
-- | Returns all rows if search string is empty.
applyGlobalFilter
  :: forall msg
   . String
  -> Array (ColumnDef msg)
  -> Array (Object String)
  -> Array (Object String)
applyGlobalFilter search cols rows =
  if null search
    then rows
    else filter (matchesGlobalFilter search cols) rows

-- | Check if a row matches the global filter
-- |
-- | A row matches if any filterable column contains the search string
-- | (case-insensitive).
matchesGlobalFilter :: forall msg. String -> Array (ColumnDef msg) -> Object String -> Boolean
matchesGlobalFilter search cols rowData =
  let
    searchLower = toLower search
    filterableCols = filter (\col -> col.filterable) cols
    values = mapMaybe (\col -> Object.lookup col.key rowData) filterableCols
  in
    any (\v -> contains (Pattern searchLower) (toLower v)) values

-- | Apply column filters to rows
-- |
-- | Each column filter is applied in sequence (AND logic).
applyColumnFilters :: Object FilterValue -> Array (Object String) -> Array (Object String)
applyColumnFilters filters rows =
  let
    filterPairs :: Array (Tuple String FilterValue)
    filterPairs = Object.toUnfoldable filters
  in
    foldl applyColumnFilter rows filterPairs

-- | Apply a single column filter
applyColumnFilter :: Array (Object String) -> Tuple String FilterValue -> Array (Object String)
applyColumnFilter rows (Tuple colKey filterVal) =
  filter (matchesColumnFilter colKey filterVal) rows

-- | Check if a row matches a column filter
matchesColumnFilter :: String -> FilterValue -> Object String -> Boolean
matchesColumnFilter colKey filterVal rowData =
  case Object.lookup colKey rowData of
    Nothing -> false
    Just cellValue ->
      case filterVal of
        TextFilter searchText ->
          contains (Pattern (toLower searchText)) (toLower cellValue)
        
        NumberFilter { min: minVal, max: maxVal } ->
          case Number.fromString cellValue of
            Nothing -> false
            Just num ->
              let
                aboveMin = case minVal of
                  Nothing -> true
                  Just m -> num >= m
                belowMax = case maxVal of
                  Nothing -> true
                  Just m -> num <= m
              in
                aboveMin && belowMax
        
        BooleanFilter expected ->
          let
            isTruthy = cellValue == "true" || cellValue == "1" || cellValue == "yes"
          in
            isTruthy == expected
        
        SelectFilter allowedValues ->
          elem cellValue allowedValues
        
        DateRangeFilter { start: startDate, end: endDate } ->
          let
            afterStart = case startDate of
              Nothing -> true
              Just s -> cellValue >= s
            beforeEnd = case endDate of
              Nothing -> true
              Just e -> cellValue <= e
          in
            afterStart && beforeEnd

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // sorting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply sorting to rows
-- |
-- | Supports multi-column sorting. Later sorts in the array have lower
-- | priority (stable sort behavior). We reverse and apply in sequence.
applySorting :: Array SortConfig -> Array (Object String) -> Array (Object String)
applySorting sortConfigs rows =
  foldl applySingleSort rows (reverse sortConfigs)

-- | Apply a single sort configuration
-- |
-- | Sorts rows by the specified column in the specified direction.
applySingleSort :: Array (Object String) -> SortConfig -> Array (Object String)
applySingleSort rows { column: col, direction } =
  let
    compareFn = comparing (\row -> fromMaybe "" (Object.lookup col row))
    sorted = sortBy compareFn rows
  in
    case direction of
      Ascending -> sorted
      Descending -> reverse sorted

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // pagination
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply pagination to rows
-- |
-- | For NoPagination, returns all rows.
-- | For BuiltIn, returns first page.
-- | For External, returns the specified page.
applyPagination :: PaginationConfig -> Array (Object String) -> Array (Object String)
applyPagination config rows =
  case config of
    NoPagination -> rows
    BuiltIn { pageSize } -> take pageSize rows
    External { pageSize, currentPage } ->
      take pageSize (drop ((currentPage - 1) * pageSize) rows)

-- | Calculate total pages from row count and page size
calculateTotalPages :: Int -> Int -> Int
calculateTotalPages totalRows pageSize =
  if pageSize <= 0
    then 1
    else (totalRows + pageSize - 1) / pageSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // selection helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toggle selection of a row
-- |
-- | Behavior depends on selection mode:
-- | - SingleSelect: Replaces selection with clicked row
-- | - MultiSelect/CheckboxSelect: Toggles clicked row in selection
-- | - NoSelection: Returns unchanged
toggleSelection :: SelectionMode -> Array String -> String -> Array String
toggleSelection mode current key =
  case mode of
    SingleSelect ->
      if elem key current
        then []
        else [key]
    MultiSelect ->
      if elem key current
        then filter (\k -> not (k == key)) current
        else Array.cons key current
    CheckboxSelect ->
      if elem key current
        then filter (\k -> not (k == key)) current
        else Array.cons key current
    NoSelection -> current

-- | Select all rows
-- |
-- | Returns array of all row keys.
selectAll :: Array (Object String) -> String -> Array String
selectAll rows rowKeyField =
  mapMaybe (\row -> Object.lookup rowKeyField row) rows

-- | Deselect all rows
-- |
-- | Returns empty array.
deselectAll :: Array String
deselectAll = []

-- | Check if a row is selected
isRowSelected :: Array String -> String -> Boolean
isRowSelected selectedKeys key = elem key selectedKeys

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // export
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert grid data to CSV string
-- |
-- | Generates CSV with headers from visible columns and data from rows.
toCsvString :: forall msg. Array (ColumnDef msg) -> Array (Object String) -> String
toCsvString cols rows =
  let
    visibleCols = filter (\col -> not col.hidden) cols
    headerRow = String.joinWith "," (Array.fromFoldable (mapHeader visibleCols))
    dataRows = Array.fromFoldable (mapRows visibleCols rows)
  in
    String.joinWith "\n" (Array.cons headerRow dataRows)
  where
    mapHeader :: Array (ColumnDef msg) -> Array String
    mapHeader columns = mapMaybe (\col -> Just (escapeCsv col.header)) columns
    
    mapRows :: Array (ColumnDef msg) -> Array (Object String) -> Array String
    mapRows columns rowData = mapMaybe (\row -> Just (rowToCsv columns row)) rowData

-- | Convert a single row to CSV
rowToCsv :: forall msg. Array (ColumnDef msg) -> Object String -> String
rowToCsv cols rowData =
  let
    values = mapMaybe (\col -> Just (escapeCsv (fromMaybe "" (Object.lookup col.key rowData)))) cols
  in
    String.joinWith "," values

-- | Escape a value for CSV
-- |
-- | Wraps in quotes and escapes internal quotes if the value contains
-- | commas, quotes, or newlines.
escapeCsv :: String -> String
escapeCsv value =
  if contains (Pattern ",") value || contains (Pattern "\"") value || contains (Pattern "\n") value
    then "\"" <> String.replaceAll (Pattern "\"") (String.Replacement "\"\"") value <> "\""
    else value
