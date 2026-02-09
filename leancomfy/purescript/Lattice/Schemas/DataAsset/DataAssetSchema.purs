-- | Lattice.Schemas.DataAsset.DataAssetSchema - Data asset type enums
-- |
-- | Data asset types for data-driven animation support.
-- |
-- | Source: ui/src/schemas/dataAsset/dataAsset-schema.ts

module Lattice.Schemas.DataAsset.DataAssetSchema
  ( -- Data File Type
    DataFileType(..)
  , dataFileTypeFromString
  , dataFileTypeToString
  , isJSONType
  , isTabularType
    -- Constants
  , maxRawContentSize
  , maxTimestamp
  , maxHeaders
  , maxRows
  , maxColumns
  , maxDataPoints
  , maxWarnings
  , maxDelimiterLength
    -- Structures
  , DataAssetBase
  , CSVParseOptions
  , JSONParseOptions
  , ChartDataPoint
    -- Validation
  , isValidDataAssetBase
  , isValidCSVParseOptions
  , isValidChartDataPoint
  ) where

import Prelude
import Data.Maybe (Maybe(..), maybe)
import Data.String (length) as S
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Int (toNumber) as Int
import Data.Number (isFinite)

--------------------------------------------------------------------------------
-- Data File Type
--------------------------------------------------------------------------------

-- | Data file types
data DataFileType
  = TypeJSON
  | TypeCSV
  | TypeTSV
  | TypeMGJSON

derive instance Eq DataFileType
derive instance Generic DataFileType _

instance Show DataFileType where
  show = genericShow

dataFileTypeFromString :: String -> Maybe DataFileType
dataFileTypeFromString = case _ of
  "json" -> Just TypeJSON
  "csv" -> Just TypeCSV
  "tsv" -> Just TypeTSV
  "mgjson" -> Just TypeMGJSON
  _ -> Nothing

dataFileTypeToString :: DataFileType -> String
dataFileTypeToString = case _ of
  TypeJSON -> "json"
  TypeCSV -> "csv"
  TypeTSV -> "tsv"
  TypeMGJSON -> "mgjson"

-- | Check if data file type is JSON-like
isJSONType :: DataFileType -> Boolean
isJSONType = case _ of
  TypeJSON -> true
  TypeMGJSON -> true
  _ -> false

-- | Check if data file type is tabular (CSV/TSV)
isTabularType :: DataFileType -> Boolean
isTabularType = case _ of
  TypeCSV -> true
  TypeTSV -> true
  _ -> false

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxRawContentSize :: Int
maxRawContentSize = 50 * 1024 * 1024  -- 50MB

maxTimestamp :: Number
maxTimestamp = 2147483647000.0  -- Year 2038

maxHeaders :: Int
maxHeaders = 10000

maxRows :: Int
maxRows = 100000

maxColumns :: Int
maxColumns = 10000

maxDataPoints :: Int
maxDataPoints = 100000

maxWarnings :: Int
maxWarnings = 100

maxDelimiterLength :: Int
maxDelimiterLength = 10

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | Base data asset info
type DataAssetBase =
  { id :: String
  , name :: String
  , type_ :: DataFileType
  , filePath :: Maybe String
  , lastModified :: Int
  , rawContent :: String
  }

-- | CSV parse options
type CSVParseOptions =
  { delimiter :: Maybe String
  , hasHeaders :: Maybe Boolean
  , trimWhitespace :: Maybe Boolean
  , skipEmptyRows :: Maybe Boolean
  }

-- | JSON parse options
type JSONParseOptions =
  { allowComments :: Maybe Boolean
  , strict :: Maybe Boolean
  }

-- | Chart data point
type ChartDataPoint =
  { label :: String
  , value :: Number
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if data asset base is valid
isValidDataAssetBase :: DataAssetBase -> Boolean
isValidDataAssetBase d =
  S.length d.id > 0 &&
  S.length d.name > 0 &&
  Int.toNumber d.lastModified <= maxTimestamp &&
  S.length d.rawContent <= maxRawContentSize

-- | Check if CSV parse options are valid
isValidCSVParseOptions :: CSVParseOptions -> Boolean
isValidCSVParseOptions o =
  maybe true (\delim -> S.length delim <= maxDelimiterLength) o.delimiter

-- | Check if chart data point is valid
isValidChartDataPoint :: ChartDataPoint -> Boolean
isValidChartDataPoint p =
  S.length p.label > 0 && isFinite p.value
