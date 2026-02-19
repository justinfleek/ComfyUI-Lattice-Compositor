{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Lattice.DataAsset
Description : Data asset types for expressions
Copyright   : (c) Lattice, 2026
License     : MIT

Data asset types for JSON, CSV, and MGJSON data sources.
Used for data-driven animation and expressions.

Source: ui/src/types/dataAsset.ts (296 lines)
-}

module Lattice.DataAsset
  ( -- * JSON Value
    JSONValue(..)
    -- * Enumerations
  , DataAssetType(..)
  , CSVColumnType(..)
  , MGJSONDataSourceType(..)
  , MGJSONPropertyType(..)
  , ChartType(..)
  , DataBindingTarget(..)
    -- * CSV Types
  , CSVColumnInfo(..)
    -- * Data Asset Types
  , DataAssetBase(..)
  , JSONDataAsset(..)
  , CSVDataAsset(..)
    -- * MGJSON Types
  , MGJSONKeyframeValue(..)
  , MGJSONDynamicProperty(..)
  , MGJSONStaticProperty(..)
  , MGJSONDataOutlet(..)
  , MGJSONDataSource(..)
  , MGJSONDataAsset(..)
    -- * Chart Types
  , ChartDataPoint(..)
  , ChartSeries(..)
  , ChartConfig(..)
  , defaultChartConfig
    -- * Data Binding
  , DataBinding(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives
  ( NonEmptyString
  , FiniteFloat
  , NonNegativeFloat
  , HexColor
  )

-- | Recursive JSON value type (no null - use Maybe at call site)
data JSONValue
  = JBool !Bool
  | JNumber !Double
  | JString !Text
  | JArray !(Vector JSONValue)
  | JObject !(Vector (Text, JSONValue))
  deriving stock (Eq, Show, Generic)

-- | Type of data asset
data DataAssetType
  = DAJson
  | DACsv
  | DATsv
  | DAMgjson  -- ^ Motion Graphics JSON
  deriving stock (Eq, Show, Generic)

-- | Detected column type for CSV
data CSVColumnType
  = ColText
  | ColNumber
  | ColBoolean
  | ColDate
  | ColDatetime
  | ColEmpty
  deriving stock (Eq, Show, Generic)

-- | Information about a CSV column
data CSVColumnInfo = CSVColumnInfo
  { csvColName         :: !NonEmptyString
  , csvColIndex        :: !Int
  , csvColDetectedType :: !CSVColumnType
  , csvColSampleValues :: !(Vector Text)
  , csvColUniqueCount  :: !Int
  , csvColNullCount    :: !Int
  } deriving stock (Eq, Show, Generic)

-- | Base data asset fields (common to all types)
data DataAssetBase = DataAssetBase
  { daBaseId           :: !NonEmptyString
  , daBaseName         :: !NonEmptyString
  , daBaseAssetType    :: !DataAssetType
  , daBaseRawContent   :: !Text
  , daBaseSizeBytes    :: !Int
  , daBaseLastModified :: !Int  -- ^ Unix timestamp
  } deriving stock (Eq, Show, Generic)

-- | JSON data asset with parsed value
data JSONDataAsset = JSONDataAsset
  { jsonDABase        :: !DataAssetBase
  , jsonDAParsedValue :: !JSONValue
  , jsonDARootType    :: !Text  -- ^ "object", "array", "primitive"
  , jsonDAKeyCount    :: !(Maybe Int)  -- ^ For objects
  , jsonDAArrayLength :: !(Maybe Int)  -- ^ For arrays
  } deriving stock (Eq, Show, Generic)

-- | CSV data asset with rows and columns
data CSVDataAsset = CSVDataAsset
  { csvDABase         :: !DataAssetBase
  , csvDAHeaders      :: !(Vector Text)
  , csvDARows         :: !(Vector (Vector Text))
  , csvDAColumns      :: !(Vector CSVColumnInfo)
  , csvDARowCount     :: !Int
  , csvDAColumnCount  :: !Int
  , csvDAHasHeaderRow :: !Bool
  , csvDADelimiter    :: !Text  -- ^ "," or "\t"
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- MGJSON Types
--------------------------------------------------------------------------------

-- | MGJSON data source type
data MGJSONDataSourceType
  = MGJSONFilePath
  | MGJSONCsvData
  | MGJSONJsonData
  | MGJSONTsvData
  deriving stock (Eq, Show, Generic)

-- | MGJSON property type
data MGJSONPropertyType
  = MGJSONSpatial2D
  | MGJSONSpatial3D
  | MGJSONColor
  | MGJSONText
  | MGJSONNumber
  | MGJSONBoolean
  deriving stock (Eq, Show, Generic)

-- | MGJSON keyframe value
data MGJSONKeyframeValue = MGJSONKeyframeValue
  { mgjsonKfTime  :: !NonNegativeFloat  -- ^ Seconds
  , mgjsonKfValue :: !JSONValue
  } deriving stock (Eq, Show, Generic)

-- | MGJSON dynamic property (animated)
data MGJSONDynamicProperty = MGJSONDynamicProperty
  { mgjsonDynMatchName    :: !NonEmptyString
  , mgjsonDynDisplayName  :: !NonEmptyString
  , mgjsonDynPropertyType :: !MGJSONPropertyType
  , mgjsonDynKeyframes    :: !(Vector MGJSONKeyframeValue)
  } deriving stock (Eq, Show, Generic)

-- | MGJSON static property
data MGJSONStaticProperty = MGJSONStaticProperty
  { mgjsonStatMatchName   :: !NonEmptyString
  , mgjsonStatDisplayName :: !NonEmptyString
  , mgjsonStatValue       :: !JSONValue
  } deriving stock (Eq, Show, Generic)

-- | MGJSON data outlet (data group)
data MGJSONDataOutlet = MGJSONDataOutlet
  { mgjsonOutletDisplayName :: !NonEmptyString
  , mgjsonOutletMatchName   :: !NonEmptyString
  , mgjsonOutletDynProps    :: !(Vector MGJSONDynamicProperty)
  , mgjsonOutletStatProps   :: !(Vector MGJSONStaticProperty)
  } deriving stock (Eq, Show, Generic)

-- | MGJSON data source
data MGJSONDataSource = MGJSONDataSource
  { mgjsonSrcDisplayName :: !NonEmptyString
  , mgjsonSrcSourceType  :: !MGJSONDataSourceType
  , mgjsonSrcDataOutlets :: !(Vector MGJSONDataOutlet)
  } deriving stock (Eq, Show, Generic)

-- | MGJSON data asset
data MGJSONDataAsset = MGJSONDataAsset
  { mgjsonDABase        :: !DataAssetBase
  , mgjsonDAVersion     :: !NonEmptyString
  , mgjsonDADataSources :: !(Vector MGJSONDataSource)
  } deriving stock (Eq, Show, Generic)

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
  deriving stock (Eq, Show, Generic)

-- | Chart data point
data ChartDataPoint = ChartDataPoint
  { chartPointX     :: !FiniteFloat
  , chartPointY     :: !FiniteFloat
  , chartPointLabel :: !(Maybe Text)
  } deriving stock (Eq, Show, Generic)

-- | Chart series
data ChartSeries = ChartSeries
  { chartSeriesName      :: !NonEmptyString
  , chartSeriesData      :: !(Vector ChartDataPoint)
  , chartSeriesColor     :: !(Maybe HexColor)
  , chartSeriesChartType :: !ChartType
  , chartSeriesYAxisIdx  :: !Int  -- ^ 0 = primary, 1 = secondary
  } deriving stock (Eq, Show, Generic)

-- | Chart configuration
data ChartConfig = ChartConfig
  { chartTitle       :: !(Maybe Text)
  , chartXAxisLabel  :: !(Maybe Text)
  , chartYAxisLabel  :: !(Maybe Text)
  , chartY2AxisLabel :: !(Maybe Text)  -- ^ Secondary axis
  , chartShowLegend  :: !Bool
  , chartShowGrid    :: !Bool
  , chartSeries      :: !(Vector ChartSeries)
  } deriving stock (Eq, Show, Generic)

-- | Default chart configuration
defaultChartConfig :: ChartConfig
defaultChartConfig = ChartConfig
  { chartTitle       = Nothing
  , chartXAxisLabel  = Nothing
  , chartYAxisLabel  = Nothing
  , chartY2AxisLabel = Nothing
  , chartShowLegend  = True
  , chartShowGrid    = True
  , chartSeries      = mempty
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
  deriving stock (Eq, Show, Generic)

-- | Data binding (connects data asset to layer property)
data DataBinding = DataBinding
  { bindingId                 :: !NonEmptyString
  , bindingDataAssetId        :: !NonEmptyString
  -- For CSV: column name or index
  , bindingColumnName         :: !(Maybe Text)
  , bindingColumnIndex        :: !(Maybe Int)
  -- For JSON: JSON path (e.g., "data.values[0].x")
  , bindingJsonPath           :: !(Maybe NonEmptyString)
  -- Target
  , bindingTargetLayerId      :: !NonEmptyString
  , bindingTargetType         :: !DataBindingTarget
  , bindingTargetPropertyPath :: !(Maybe NonEmptyString)  -- ^ e.g., "transform.position.x"
  -- Row selection (for CSV)
  , bindingRowExpression      :: !(Maybe Text)  -- ^ e.g., "frame % rowCount"
  -- Value transformation
  , bindingValueExpression    :: !(Maybe Text)  -- ^ e.g., "value * 100"
  } deriving stock (Eq, Show, Generic)
