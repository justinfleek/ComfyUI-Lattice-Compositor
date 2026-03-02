-- | Lattice.DataAsset - Data asset types for expressions
-- |
-- | Source: ui/src/types/dataAsset.ts (296 lines)
-- |
-- | Data asset types for JSON, CSV, and MGJSON data sources.
-- | Used for data-driven animation and expressions.

module Lattice.DataAsset
  ( JSONValue(..)
  , DataAssetType(..)
  , CSVColumnType(..)
  , MGJSONDataSourceType(..)
  , MGJSONPropertyType(..)
  , ChartType(..)
  , DataBindingTarget(..)
  , CSVColumnInfo
  , DataAssetBase
  , JSONDataAsset
  , CSVDataAsset
  , MGJSONKeyframeValue
  , MGJSONDynamicProperty
  , MGJSONStaticProperty
  , MGJSONDataOutlet
  , MGJSONDataSource
  , MGJSONDataAsset
  , ChartDataPoint
  , ChartSeries
  , ChartConfig
  , DataBinding
  , defaultChartConfig
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Foreign.Object (Object)
import Lattice.Primitives (NonEmptyString, FiniteFloat, NonNegativeFloat, HexColor)

-- | Recursive JSON value type (no null - use Maybe at call site)
data JSONValue
  = JBool Boolean
  | JNumber Number
  | JString String
  | JArray (Array JSONValue)
  | JObject (Array { key :: String, value :: JSONValue })

derive instance Eq JSONValue
derive instance Generic JSONValue _
instance Show JSONValue where
  show (JBool b) = "(JBool " <> show b <> ")"
  show (JNumber n) = "(JNumber " <> show n <> ")"
  show (JString s) = "(JString " <> show s <> ")"
  show (JArray arr) = "(JArray " <> show arr <> ")"
  show (JObject kvs) = "(JObject " <> show (map (\kv -> kv.key <> ": " <> show kv.value) kvs) <> ")"

-- | Type of data asset
data DataAssetType
  = DAJson
  | DACsv
  | DATsv
  | DAMgjson  -- ^ Motion Graphics JSON

derive instance Eq DataAssetType
derive instance Generic DataAssetType _
instance Show DataAssetType where show = genericShow

-- | Detected column type for CSV
data CSVColumnType
  = ColText
  | ColNumber
  | ColBoolean
  | ColDate
  | ColDatetime
  | ColEmpty

derive instance Eq CSVColumnType
derive instance Generic CSVColumnType _
instance Show CSVColumnType where show = genericShow

-- | Information about a CSV column
type CSVColumnInfo =
  { name         :: NonEmptyString
  , index        :: Int
  , detectedType :: CSVColumnType
  , sampleValues :: Array String
  , uniqueCount  :: Int
  , nullCount    :: Int
  }

-- | Base data asset fields (common to all types)
type DataAssetBase =
  { id           :: NonEmptyString
  , name         :: NonEmptyString
  , assetType    :: DataAssetType
  , rawContent   :: String
  , sizeBytes    :: Int
  , lastModified :: Int  -- ^ Unix timestamp
  }

-- | JSON data asset with parsed value
type JSONDataAsset =
  { base        :: DataAssetBase
  , parsedValue :: JSONValue
  , rootType    :: String  -- ^ "object", "array", "primitive"
  , keyCount    :: Maybe Int  -- ^ For objects
  , arrayLength :: Maybe Int  -- ^ For arrays
  }

-- | CSV data asset with rows and columns
type CSVDataAsset =
  { base         :: DataAssetBase
  , headers      :: Array String
  , rows         :: Array (Array String)
  , columns      :: Array CSVColumnInfo
  , rowCount     :: Int
  , columnCount  :: Int
  , hasHeaderRow :: Boolean
  , delimiter    :: String  -- ^ "," or "\t"
  }

--------------------------------------------------------------------------------
-- MGJSON Types
--------------------------------------------------------------------------------

-- | MGJSON data source type
data MGJSONDataSourceType
  = MGJSONFilePath
  | MGJSONCsvData
  | MGJSONJsonData
  | MGJSONTsvData

derive instance Eq MGJSONDataSourceType
derive instance Generic MGJSONDataSourceType _
instance Show MGJSONDataSourceType where show = genericShow

-- | MGJSON property type
data MGJSONPropertyType
  = MGJSONSpatial2D
  | MGJSONSpatial3D
  | MGJSONColor
  | MGJSONText
  | MGJSONNumber
  | MGJSONBoolean

derive instance Eq MGJSONPropertyType
derive instance Generic MGJSONPropertyType _
instance Show MGJSONPropertyType where show = genericShow

-- | MGJSON keyframe value
type MGJSONKeyframeValue =
  { time  :: NonNegativeFloat  -- ^ Seconds
  , value :: JSONValue
  }

-- | MGJSON dynamic property (animated)
type MGJSONDynamicProperty =
  { matchName    :: NonEmptyString
  , displayName  :: NonEmptyString
  , propertyType :: MGJSONPropertyType
  , keyframes    :: Array MGJSONKeyframeValue
  }

-- | MGJSON static property
type MGJSONStaticProperty =
  { matchName   :: NonEmptyString
  , displayName :: NonEmptyString
  , value       :: JSONValue
  }

-- | MGJSON data outlet (data group)
type MGJSONDataOutlet =
  { displayName       :: NonEmptyString
  , matchName         :: NonEmptyString
  , dynamicProperties :: Array MGJSONDynamicProperty
  , staticProperties  :: Array MGJSONStaticProperty
  }

-- | MGJSON data source
type MGJSONDataSource =
  { displayName :: NonEmptyString
  , sourceType  :: MGJSONDataSourceType
  , dataOutlets :: Array MGJSONDataOutlet
  }

-- | MGJSON data asset
type MGJSONDataAsset =
  { base        :: DataAssetBase
  , version     :: NonEmptyString
  , dataSources :: Array MGJSONDataSource
  }

--------------------------------------------------------------------------------
-- Chart Types
--------------------------------------------------------------------------------

-- | Chart type
data ChartType
  = ChartLine
  | ChartBar
  | ChartScatter
  | ChartArea
  | ChartPie
  | ChartDonut

derive instance Eq ChartType
derive instance Generic ChartType _
instance Show ChartType where show = genericShow

-- | Chart data point
type ChartDataPoint =
  { x     :: FiniteFloat
  , y     :: FiniteFloat
  , label :: Maybe String
  }

-- | Chart series
type ChartSeries =
  { name      :: NonEmptyString
  , seriesData :: Array ChartDataPoint
  , color     :: Maybe HexColor
  , chartType :: ChartType
  , yAxisIdx  :: Int  -- ^ 0 = primary, 1 = secondary
  }

-- | Chart configuration
type ChartConfig =
  { title       :: Maybe String
  , xAxisLabel  :: Maybe String
  , yAxisLabel  :: Maybe String
  , y2AxisLabel :: Maybe String  -- ^ Secondary axis
  , showLegend  :: Boolean
  , showGrid    :: Boolean
  , series      :: Array ChartSeries
  }

-- | Default chart configuration
defaultChartConfig :: ChartConfig
defaultChartConfig =
  { title: Nothing
  , xAxisLabel: Nothing
  , yAxisLabel: Nothing
  , y2AxisLabel: Nothing
  , showLegend: true
  , showGrid: true
  , series: []
  }

--------------------------------------------------------------------------------
-- Data Binding
--------------------------------------------------------------------------------

-- | Data binding target type
data DataBindingTarget
  = BindProperty    -- ^ Bind to AnimatableProperty
  | BindText        -- ^ Bind to text content
  | BindVisibility  -- ^ Bind to layer visibility
  | BindColor       -- ^ Bind to color value

derive instance Eq DataBindingTarget
derive instance Generic DataBindingTarget _
instance Show DataBindingTarget where show = genericShow

-- | Data binding (connects data asset to layer property)
type DataBinding =
  { id                 :: NonEmptyString
  , dataAssetId        :: NonEmptyString
  -- For CSV: column name or index
  , columnName         :: Maybe String
  , columnIndex        :: Maybe Int
  -- For JSON: JSON path (e.g., "data.values[0].x")
  , jsonPath           :: Maybe NonEmptyString
  -- Target
  , targetLayerId      :: NonEmptyString
  , targetType         :: DataBindingTarget
  , targetPropertyPath :: Maybe NonEmptyString  -- ^ e.g., "transform.position.x"
  -- Row selection (for CSV)
  , rowExpression      :: Maybe String  -- ^ e.g., "frame % rowCount"
  -- Value transformation
  , valueExpression    :: Maybe String  -- ^ e.g., "value * 100"
  }
