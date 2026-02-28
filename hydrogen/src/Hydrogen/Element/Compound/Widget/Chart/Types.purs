-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // widget // chart // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chart Types — Data structures for chart widgets.
-- |
-- | Defines all types used by the Chart module:
-- | - ChartType enum for different visualizations
-- | - AxisType and AxisConfig for axis configuration
-- | - DataPoint, SeriesData, and ChartData for chart data
-- | - ChartProps and ChartProp for widget configuration

module Hydrogen.Element.Compound.Widget.Chart.Types
  ( -- * Chart Types
    ChartType
      ( Line
      , Area
      , Bar
      , Column
      , Pie
      , Donut
      , Scatter
      , Bubble
      , Radar
      , Polar
      )
  , chartTypeToString
  , isCartesian
  , isPolar
  , needsXAxis
  , needsYAxis
  
  -- * Axis Types
  , AxisType
      ( AxisNumeric
      , AxisCategory
      , AxisDatetime
      , AxisLogarithmic
      )
  , axisTypeToString
  , AxisConfig
  
  -- * Data Types
  , DataPoint
  , SeriesData
  , ChartData
  
  -- * Props
  , ChartProps
  , ChartProp
  , defaultProps
  
  -- * Prop Builders
  , showLegend
  , stacked
  , animated
  , aspectRatio
  , className
  ) where

import Prelude
  ( class Eq
  , class Show
  , (==)
  , (||)
  , (<>)
  )

import Data.Maybe (Maybe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // chart types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Types of chart visualizations.
data ChartType
  = Line
  | Area
  | Bar
  | Column
  | Pie
  | Donut
  | Scatter
  | Bubble
  | Radar
  | Polar

derive instance eqChartType :: Eq ChartType

instance showChartType :: Show ChartType where
  show = chartTypeToString

-- | Convert chart type to string.
chartTypeToString :: ChartType -> String
chartTypeToString ct = case ct of
  Line -> "line"
  Area -> "area"
  Bar -> "bar"
  Column -> "column"
  Pie -> "pie"
  Donut -> "donut"
  Scatter -> "scatter"
  Bubble -> "bubble"
  Radar -> "radar"
  Polar -> "polar"

-- | Check if chart type uses Cartesian coordinates.
isCartesian :: ChartType -> Boolean
isCartesian ct = ct == Line || ct == Area || ct == Bar || ct == Column || ct == Scatter || ct == Bubble

-- | Check if chart type uses polar coordinates.
isPolar :: ChartType -> Boolean
isPolar ct = ct == Pie || ct == Donut || ct == Radar || ct == Polar

-- | Check if chart type requires X axis.
needsXAxis :: ChartType -> Boolean
needsXAxis ct = isCartesian ct

-- | Check if chart type requires Y axis.
needsYAxis :: ChartType -> Boolean
needsYAxis ct = isCartesian ct

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // axis types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis value types.
data AxisType
  = AxisNumeric
  | AxisCategory
  | AxisDatetime
  | AxisLogarithmic

derive instance eqAxisType :: Eq AxisType

instance showAxisType :: Show AxisType where
  show = axisTypeToString

-- | Convert axis type to string.
axisTypeToString :: AxisType -> String
axisTypeToString at = case at of
  AxisNumeric -> "numeric"
  AxisCategory -> "category"
  AxisDatetime -> "datetime"
  AxisLogarithmic -> "logarithmic"

-- | Axis configuration.
type AxisConfig =
  { axisType :: AxisType
  , label :: Maybe String
  , min :: Maybe Number
  , max :: Maybe Number
  , categories :: Maybe (Array String)
  , format :: Maybe String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // data types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Single data point.
-- |
-- | For most charts, x and y are the primary values.
-- | z is used for bubble charts (bubble size).
type DataPoint =
  { x :: Number
  , y :: Number
  , z :: Maybe Number      -- ^ Bubble size (for Bubble charts)
  , label :: Maybe String  -- ^ Point label (for tooltips)
  , color :: Maybe String  -- ^ Override color for this point
  }

-- | Chart series (a collection of data points).
type SeriesData =
  { name :: String
  , data :: Array DataPoint
  , color :: Maybe String         -- ^ Series color
  , chartType :: Maybe ChartType  -- ^ Override for mixed charts
  , stack :: Maybe String         -- ^ Stack group name
  , yAxisIndex :: Maybe Int       -- ^ Y-axis index (for dual axis)
  }

-- | Complete chart data payload.
type ChartData =
  { chartType :: ChartType
  , series :: Array SeriesData
  , xAxis :: Maybe AxisConfig
  , yAxis :: Maybe AxisConfig
  , yAxis2 :: Maybe AxisConfig   -- ^ Secondary Y-axis for dual axis charts
  , title :: Maybe String
  , subtitle :: Maybe String
  , showLegend :: Boolean
  , stacked :: Boolean
  , animated :: Boolean
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chart widget properties.
type ChartProps =
  { showLegend :: Boolean
  , stacked :: Boolean
  , animated :: Boolean
  , aspectRatio :: Number   -- ^ Width/height ratio
  , className :: String
  }

-- | Property modifier.
type ChartProp = ChartProps -> ChartProps

-- | Default properties.
defaultProps :: ChartProps
defaultProps =
  { showLegend: true
  , stacked: false
  , animated: true
  , aspectRatio: 2.0  -- 2:1 width to height
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show/hide legend.
showLegend :: Boolean -> ChartProp
showLegend b props = props { showLegend = b }

-- | Enable stacking.
stacked :: Boolean -> ChartProp
stacked b props = props { stacked = b }

-- | Enable animations.
animated :: Boolean -> ChartProp
animated b props = props { animated = b }

-- | Set aspect ratio (width/height).
aspectRatio :: Number -> ChartProp
aspectRatio r props = props { aspectRatio = r }

-- | Add custom CSS class.
className :: String -> ChartProp
className c props = props { className = props.className <> " " <> c }
