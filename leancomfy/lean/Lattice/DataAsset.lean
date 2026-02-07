/-
  Lattice.DataAsset - Data asset types for expressions

  Max 500 lines.

  Source: ui/src/types/dataAsset.ts (296 lines)

  Key types:
  - JSONValue: Recursive JSON value type
  - DataAsset: Base for all data assets
  - JSONDataAsset: JSON data with parsed value
  - CSVDataAsset: CSV/TSV data with rows/columns
  - ChartSeries: For data visualization
-/

import Lattice.Primitives

namespace Lattice.DataAsset

open Lattice.Primitives

/-! ## JSON Value -/

/-- Recursive JSON value type (no null - use Option at call site) -/
inductive JSONValue where
  | bool : Bool → JSONValue
  | number : Float → JSONValue
  | string : String → JSONValue
  | array : Array JSONValue → JSONValue
  | object : Array (String × JSONValue) → JSONValue
  deriving Repr

/-! ## Data Asset Type -/

/-- Type of data asset -/
inductive DataAssetType where
  | json
  | csv
  | tsv
  | mgjson  -- Motion Graphics JSON
  deriving Repr, BEq, DecidableEq

/-! ## CSV Column Type -/

/-- Detected column type for CSV -/
inductive CSVColumnType where
  | text
  | number
  | boolean
  | date
  | datetime
  | empty
  deriving Repr, BEq, DecidableEq

/-! ## CSV Column Info -/

/-- Information about a CSV column -/
structure CSVColumnInfo where
  name : NonEmptyString
  index : Nat
  detectedType : CSVColumnType
  sampleValues : Array String
  uniqueCount : Nat
  nullCount : Nat
  deriving Repr

/-! ## Data Asset Base -/

/-- Base data asset fields (common to all types) -/
structure DataAssetBase where
  id : NonEmptyString
  name : NonEmptyString
  assetType : DataAssetType
  rawContent : String
  sizeBytes : Nat
  lastModified : Nat  -- Unix timestamp
  deriving Repr

/-! ## JSON Data Asset -/

/-- JSON data asset with parsed value -/
structure JSONDataAsset extends DataAssetBase where
  parsedValue : JSONValue
  rootType : String  -- "object", "array", "primitive"
  keyCount : Option Nat  -- For objects
  arrayLength : Option Nat  -- For arrays
  deriving Repr

/-! ## CSV Data Asset -/

/-- CSV data asset with rows and columns -/
structure CSVDataAsset extends DataAssetBase where
  headers : Array String
  rows : Array (Array String)
  columns : Array CSVColumnInfo
  rowCount : Nat
  columnCount : Nat
  hasHeaderRow : Bool
  delimiter : String  -- "," or "\t"
  rowCount_positive : rowCount > 0 ∨ rowCount = 0
  columnCount_positive : columnCount > 0 ∨ columnCount = 0
  deriving Repr

/-! ## MGJSON Types -/

/-- MGJSON data source type -/
inductive MGJSONDataSourceType where
  | filePath
  | csvData
  | jsonData
  | tsvData
  deriving Repr, BEq, DecidableEq

/-- MGJSON property type -/
inductive MGJSONPropertyType where
  | spatial2D
  | spatial3D
  | color
  | text
  | number
  | boolean
  deriving Repr, BEq, DecidableEq

/-- MGJSON keyframe value -/
structure MGJSONKeyframeValue where
  time : Float  -- Seconds
  value : JSONValue
  time_finite : time.isFinite
  time_ge_0 : time ≥ 0
  deriving Repr

/-- MGJSON dynamic property (animated) -/
structure MGJSONDynamicProperty where
  matchName : NonEmptyString
  displayName : NonEmptyString
  propertyType : MGJSONPropertyType
  keyframes : Array MGJSONKeyframeValue
  deriving Repr

/-- MGJSON static property -/
structure MGJSONStaticProperty where
  matchName : NonEmptyString
  displayName : NonEmptyString
  value : JSONValue
  deriving Repr

/-- MGJSON data outlet (data group) -/
structure MGJSONDataOutlet where
  displayName : NonEmptyString
  matchName : NonEmptyString
  dynamicProperties : Array MGJSONDynamicProperty
  staticProperties : Array MGJSONStaticProperty
  deriving Repr

/-- MGJSON data source -/
structure MGJSONDataSource where
  displayName : NonEmptyString
  sourceType : MGJSONDataSourceType
  dataOutlets : Array MGJSONDataOutlet
  deriving Repr

/-- MGJSON data asset -/
structure MGJSONDataAsset extends DataAssetBase where
  version : NonEmptyString
  dataSources : Array MGJSONDataSource
  deriving Repr

/-! ## Chart Types -/

/-- Chart type -/
inductive ChartType where
  | line
  | bar
  | scatter
  | area
  | pie
  | donut
  deriving Repr, BEq, DecidableEq

/-- Chart data point -/
structure ChartDataPoint where
  x : Float
  y : Float
  label : Option String
  x_finite : x.isFinite
  y_finite : y.isFinite
  deriving Repr

/-- Chart series -/
structure ChartSeries where
  name : NonEmptyString
  data : Array ChartDataPoint
  color : Option HexColor
  chartType : ChartType
  yAxisIndex : Nat  -- 0 = primary, 1 = secondary
  deriving Repr

/-- Chart configuration -/
structure ChartConfig where
  title : Option String
  xAxisLabel : Option String
  yAxisLabel : Option String
  y2AxisLabel : Option String  -- Secondary axis
  showLegend : Bool
  showGrid : Bool
  series : Array ChartSeries
  deriving Repr

/-! ## Data Binding -/

/-- Data binding target type -/
inductive DataBindingTarget where
  | property    -- Bind to AnimatableProperty
  | text        -- Bind to text content
  | visibility  -- Bind to layer visibility
  | color       -- Bind to color value
  deriving Repr, BEq, DecidableEq

/-- Data binding (connects data asset to layer property) -/
structure DataBinding where
  id : NonEmptyString
  dataAssetId : NonEmptyString
  -- For CSV: column name or index
  columnName : Option String
  columnIndex : Option Nat
  -- For JSON: JSON path (e.g., "data.values[0].x")
  jsonPath : Option NonEmptyString
  -- Target
  targetLayerId : NonEmptyString
  targetType : DataBindingTarget
  targetPropertyPath : Option NonEmptyString  -- e.g., "transform.position.x"
  -- Row selection (for CSV)
  rowExpression : Option String  -- e.g., "frame % rowCount"
  -- Value transformation
  valueExpression : Option String  -- e.g., "value * 100"
  deriving Repr

/-! ## Default Values -/

/-- Default chart config -/
def defaultChartConfig : ChartConfig :=
  { title := none
  , xAxisLabel := none
  , yAxisLabel := none
  , y2AxisLabel := none
  , showLegend := true
  , showGrid := true
  , series := #[]
  }

end Lattice.DataAsset
