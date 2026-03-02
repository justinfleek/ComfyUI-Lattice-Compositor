/-
  Lattice.Schemas.DataAsset.DataAssetSchema - Data asset type enums

  Data asset types for data-driven animation support.

  Source: ui/src/schemas/dataAsset/dataAsset-schema.ts
-/

namespace Lattice.Schemas.DataAsset.DataAssetSchema

--------------------------------------------------------------------------------
-- Data File Type
--------------------------------------------------------------------------------

/-- Data file types -/
inductive DataFileType where
  | json
  | csv
  | tsv
  | mgjson
  deriving Repr, DecidableEq, Inhabited

def DataFileType.fromString : String → Option DataFileType
  | "json" => some DataFileType.json
  | "csv" => some DataFileType.csv
  | "tsv" => some DataFileType.tsv
  | "mgjson" => some DataFileType.mgjson
  | _ => none

def DataFileType.toString : DataFileType → String
  | DataFileType.json => "json"
  | DataFileType.csv => "csv"
  | DataFileType.tsv => "tsv"
  | DataFileType.mgjson => "mgjson"

/-- Check if data file type is JSON-like -/
def DataFileType.isJSON : DataFileType → Bool
  | DataFileType.json => true
  | DataFileType.mgjson => true
  | _ => false

/-- Check if data file type is tabular (CSV/TSV) -/
def DataFileType.isTabular : DataFileType → Bool
  | DataFileType.csv => true
  | DataFileType.tsv => true
  | _ => false

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def maxRawContentSize : Nat := 50 * 1024 * 1024  -- 50MB
def maxTimestamp : Nat := 2147483647000  -- Year 2038
def maxHeaders : Nat := 10000
def maxRows : Nat := 100000
def maxColumns : Nat := 10000
def maxDataPoints : Nat := 100000
def maxWarnings : Nat := 100
def maxDelimiterLength : Nat := 10

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- Base data asset info -/
structure DataAssetBase where
  id : String
  name : String
  type_ : DataFileType
  filePath : Option String
  lastModified : Nat
  rawContent : String
  deriving Repr, DecidableEq, Inhabited

/-- CSV parse options -/
structure CSVParseOptions where
  delimiter : Option String
  hasHeaders : Option Bool
  trimWhitespace : Option Bool
  skipEmptyRows : Option Bool
  deriving Repr, DecidableEq, Inhabited

/-- JSON parse options -/
structure JSONParseOptions where
  allowComments : Option Bool
  strict : Option Bool
  deriving Repr, DecidableEq, Inhabited

/-- Chart data point -/
structure ChartDataPoint where
  label : String
  value : Float
  deriving Repr, DecidableEq, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

def isValidDataAssetBase (d : DataAssetBase) : Bool :=
  d.id.length > 0 &&
  d.name.length > 0 &&
  d.lastModified <= maxTimestamp &&
  d.rawContent.length <= maxRawContentSize

def isValidCSVParseOptions (o : CSVParseOptions) : Bool :=
  match o.delimiter with
  | some d => d.length <= maxDelimiterLength
  | none => true

def isValidChartDataPoint (p : ChartDataPoint) : Bool :=
  p.label.length > 0 && p.value.isFinite

end Lattice.Schemas.DataAsset.DataAssetSchema
