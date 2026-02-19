{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.DataAsset.DataAssetSchema
Description : Data asset type enums
Copyright   : (c) Lattice, 2026
License     : MIT

Data asset types for data-driven animation support.

Source: ui/src/schemas/dataAsset/dataAsset-schema.ts
-}

module Lattice.Schemas.DataAsset.DataAssetSchema
  ( -- * Data File Type
    DataFileType(..)
  , dataFileTypeFromText
  , dataFileTypeToText
  , isJSONType
  , isTabularType
    -- * Constants
  , maxRawContentSize
  , maxTimestamp
  , maxHeaders
  , maxRows
  , maxColumns
  , maxDataPoints
  , maxWarnings
  , maxDelimiterLength
    -- * Structures
  , DataAssetBase(..)
  , CSVParseOptions(..)
  , JSONParseOptions(..)
  , ChartDataPoint(..)
    -- * Validation
  , isValidDataAssetBase
  , isValidCSVParseOptions
  , isValidChartDataPoint
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T

--------------------------------------------------------------------------------
-- Data File Type
--------------------------------------------------------------------------------

-- | Data file types
data DataFileType
  = TypeJSON
  | TypeCSV
  | TypeTSV
  | TypeMGJSON
  deriving stock (Eq, Show, Generic, Enum, Bounded)

dataFileTypeFromText :: Text -> Maybe DataFileType
dataFileTypeFromText "json" = Just TypeJSON
dataFileTypeFromText "csv" = Just TypeCSV
dataFileTypeFromText "tsv" = Just TypeTSV
dataFileTypeFromText "mgjson" = Just TypeMGJSON
dataFileTypeFromText _ = Nothing

dataFileTypeToText :: DataFileType -> Text
dataFileTypeToText TypeJSON = "json"
dataFileTypeToText TypeCSV = "csv"
dataFileTypeToText TypeTSV = "tsv"
dataFileTypeToText TypeMGJSON = "mgjson"

-- | Check if data file type is JSON-like
isJSONType :: DataFileType -> Bool
isJSONType TypeJSON = True
isJSONType TypeMGJSON = True
isJSONType _ = False

-- | Check if data file type is tabular (CSV/TSV)
isTabularType :: DataFileType -> Bool
isTabularType TypeCSV = True
isTabularType TypeTSV = True
isTabularType _ = False

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxRawContentSize :: Int
maxRawContentSize = 50 * 1024 * 1024  -- 50MB

maxTimestamp :: Int
maxTimestamp = 2147483647000  -- Year 2038

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
data DataAssetBase = DataAssetBase
  { dabId :: !Text
  , dabName :: !Text
  , dabType :: !DataFileType
  , dabFilePath :: !(Maybe Text)
  , dabLastModified :: !Int
  , dabRawContent :: !Text
  }
  deriving stock (Eq, Show, Generic)

-- | CSV parse options
data CSVParseOptions = CSVParseOptions
  { cpoDelimiter :: !(Maybe Text)
  , cpoHasHeaders :: !(Maybe Bool)
  , cpoTrimWhitespace :: !(Maybe Bool)
  , cpoSkipEmptyRows :: !(Maybe Bool)
  }
  deriving stock (Eq, Show, Generic)

-- | JSON parse options
data JSONParseOptions = JSONParseOptions
  { jpoAllowComments :: !(Maybe Bool)
  , jpoStrict :: !(Maybe Bool)
  }
  deriving stock (Eq, Show, Generic)

-- | Chart data point
data ChartDataPoint = ChartDataPoint
  { cdpLabel :: !Text
  , cdpValue :: !Double
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if data asset base is valid
isValidDataAssetBase :: DataAssetBase -> Bool
isValidDataAssetBase d =
  T.length (dabId d) > 0 &&
  T.length (dabName d) > 0 &&
  dabLastModified d <= maxTimestamp &&
  T.length (dabRawContent d) <= maxRawContentSize

-- | Check if CSV parse options are valid
isValidCSVParseOptions :: CSVParseOptions -> Bool
isValidCSVParseOptions o =
  maybe True (\delim -> T.length delim <= maxDelimiterLength) (cpoDelimiter o)

-- | Check if chart data point is valid
isValidChartDataPoint :: ChartDataPoint -> Bool
isValidChartDataPoint p =
  T.length (cdpLabel p) > 0 &&
  not (isNaN (cdpValue p) || isInfinite (cdpValue p))
