-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // widget // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Widget Types — Core types for dashboard widgets.
-- |
-- | ## Design Philosophy
-- |
-- | Widgets are data visualization components for dashboards. Each widget
-- | type has a corresponding data payload type that contains ALL information
-- | needed to render the widget. No external state, no async loading within
-- | the widget itself — the data is provided, the widget renders it.
-- |
-- | This module defines:
-- | - WidgetId — Deterministic identifier for widget instances
-- | - WidgetType — Enumeration of all widget kinds
-- | - RefreshRate — How often widget data should be refreshed
-- | - ChangeDirection — Trend indicators (up/down/flat)
-- | - Common formatting types
-- |
-- | Individual widget data types (MetricData, ChartData, etc.) are defined
-- | in their respective modules to keep this file focused and under 500 lines.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Widget.Types as Widget
-- |
-- | -- Create a widget ID
-- | myWidgetId = Widget.widgetId "dashboard-main" "revenue-metric"
-- |
-- | -- Check widget type
-- | case Widget.Metric of
-- |   Widget.Metric -> "Displays a single KPI"
-- |   Widget.Chart -> "Displays chart visualization"
-- |   _ -> "Other widget type"
-- | ```

module Hydrogen.Element.Compound.Widget.Types
  ( -- * Widget Identity
    WidgetId
  , widgetId
  , widgetIdFromString
  , unwrapWidgetId
  , widgetIdToString
  
  -- * Dashboard Identity
  , DashboardId
  , dashboardId
  , dashboardIdFromString
  , unwrapDashboardId
  , dashboardIdToString
  
  -- * Widget Types
  , WidgetType
    ( Metric
    , Chart
    , Table
    , Gauge
    , Sparkline
    , Heatmap
    , Funnel
    , Sankey
    , Treemap
    , Map
    )
  , widgetTypeToString
  , widgetTypeFromString
  , allWidgetTypes
  
  -- * Change Indicators
  , ChangeDirection
    ( ChangeUp
    , ChangeDown
    , ChangeFlat
    )
  , changeDirectionToString
  , isPositiveChange
  , isNegativeChange
  
  -- * Refresh Configuration
  , RefreshRate
    ( RefreshRealtime
    , RefreshInterval
    , RefreshManual
    )
  , RefreshMs
  , mkRefreshMs
  , unwrapRefreshMs
  , refreshRateToMs
  , defaultRefreshRate
  
  -- * Value Formatting
  , ValueFormat
    ( FormatNumber
    , FormatCurrency
    , FormatPercent
    , FormatDate
    , FormatDatetime
    , FormatDuration
    , FormatCustom
    )
  , formatValueToString
  
  -- * Grid Position
  , GridPosition
  , gridPosition
  , defaultGridPosition
  
  -- * Widget Size
  , WidgetSize
  , widgetSize
  , smallWidget
  , mediumWidget
  , largeWidget
  , fullWidthWidget
  
  -- * Bounded Types
  , GridColumn
  , mkGridColumn
  , unwrapGridColumn
  , GridRow
  , mkGridRow
  , unwrapGridRow
  , Percentage
  , mkPercentage
  , unwrapPercentage
  , DecimalPlaces
  , mkDecimalPlaces
  , unwrapDecimalPlaces
  
  -- * Utility Functions
  , isInRange
  , exceedsThreshold
  , isSameWidgetType
  , isVisualization
  , isFlowWidget
  , isOrigin
  , fitsInGrid
  
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (==)
  , (&&)
  , (||)
  , (<>)
  , (<=)
  , (>=)
  , (<)
  , (>)
  , (+)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Identity (EntityId, entityId, unwrapEntityId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // widget identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a widget instance.
-- |
-- | Generated deterministically from dashboard name + widget name.
-- | Two widgets with the same dashboard and widget name will always
-- | have the same WidgetId.
newtype WidgetId = WidgetId String

derive instance eqWidgetId :: Eq WidgetId
derive instance ordWidgetId :: Ord WidgetId

instance showWidgetId :: Show WidgetId where
  show (WidgetId id) = "widget:" <> id

-- | Create a widget ID from dashboard name and widget name.
-- |
-- | Uses a namespaced approach to generate deterministic IDs:
-- | `widget:dashboardName/widgetName` is hashed to produce a UUID.
-- |
-- | ```purescript
-- | revenueWidget = widgetId "main-dashboard" "monthly-revenue"
-- | usersWidget = widgetId "main-dashboard" "active-users"
-- | ```
widgetId :: String -> String -> WidgetId
widgetId dashboardName widgetName =
  let eid :: EntityId
      eid = entityId ("widget:" <> dashboardName <> "/" <> widgetName)
  in WidgetId (unwrapEntityId eid)

-- | Create WidgetId from raw string (for deserialization).
-- |
-- | Use with caution — this bypasses deterministic generation.
widgetIdFromString :: String -> WidgetId
widgetIdFromString = WidgetId

-- | Unwrap widget ID to String.
unwrapWidgetId :: WidgetId -> String
unwrapWidgetId (WidgetId id) = id

-- | Convert to string for serialization.
widgetIdToString :: WidgetId -> String
widgetIdToString = unwrapWidgetId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // dashboard identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a dashboard.
-- |
-- | Dashboards contain multiple widgets and have their own identity.
newtype DashboardId = DashboardId String

derive instance eqDashboardId :: Eq DashboardId
derive instance ordDashboardId :: Ord DashboardId

instance showDashboardId :: Show DashboardId where
  show (DashboardId id) = "dashboard:" <> id

-- | Create a dashboard ID from organization and dashboard name.
-- |
-- | Uses a namespaced approach to generate deterministic IDs:
-- | `dashboard:orgName/dashName` is hashed to produce a UUID.
dashboardId :: String -> String -> DashboardId
dashboardId orgName dashName =
  let eid :: EntityId
      eid = entityId ("dashboard:" <> orgName <> "/" <> dashName)
  in DashboardId (unwrapEntityId eid)

-- | Create DashboardId from raw string.
dashboardIdFromString :: String -> DashboardId
dashboardIdFromString = DashboardId

-- | Unwrap dashboard ID.
unwrapDashboardId :: DashboardId -> String
unwrapDashboardId (DashboardId id) = id

-- | Convert to string.
dashboardIdToString :: DashboardId -> String
dashboardIdToString = unwrapDashboardId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // widget types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Types of dashboard widgets.
-- |
-- | Each type corresponds to a specific visualization pattern:
-- | - Metric: Single KPI with optional trend
-- | - Chart: Line, bar, pie, etc. visualizations
-- | - Table: Tabular data with sorting/pagination
-- | - Gauge: Circular progress toward a target
-- | - Sparkline: Inline mini chart
-- | - Heatmap: Color-coded matrix
-- | - Funnel: Conversion funnel
-- | - Sankey: Flow diagram
-- | - Treemap: Hierarchical boxes
-- | - Map: Geographic visualization
data WidgetType
  = Metric
  | Chart
  | Table
  | Gauge
  | Sparkline
  | Heatmap
  | Funnel
  | Sankey
  | Treemap
  | Map

derive instance eqWidgetType :: Eq WidgetType
derive instance ordWidgetType :: Ord WidgetType

instance showWidgetType :: Show WidgetType where
  show = widgetTypeToString

-- | Convert widget type to string.
widgetTypeToString :: WidgetType -> String
widgetTypeToString wt = case wt of
  Metric -> "metric"
  Chart -> "chart"
  Table -> "table"
  Gauge -> "gauge"
  Sparkline -> "sparkline"
  Heatmap -> "heatmap"
  Funnel -> "funnel"
  Sankey -> "sankey"
  Treemap -> "treemap"
  Map -> "map"

-- | Parse widget type from string.
widgetTypeFromString :: String -> Maybe WidgetType
widgetTypeFromString s = case s of
  "metric" -> Just Metric
  "chart" -> Just Chart
  "table" -> Just Table
  "gauge" -> Just Gauge
  "sparkline" -> Just Sparkline
  "heatmap" -> Just Heatmap
  "funnel" -> Just Funnel
  "sankey" -> Just Sankey
  "treemap" -> Just Treemap
  "map" -> Just Map
  _ -> Nothing

-- | All widget types for iteration.
allWidgetTypes :: Array WidgetType
allWidgetTypes =
  [ Metric
  , Chart
  , Table
  , Gauge
  , Sparkline
  , Heatmap
  , Funnel
  , Sankey
  , Treemap
  , Map
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // change indicators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction of metric change.
-- |
-- | Used to indicate whether a metric has increased, decreased, or
-- | stayed flat compared to a previous period.
data ChangeDirection
  = ChangeUp
  | ChangeDown
  | ChangeFlat

derive instance eqChangeDirection :: Eq ChangeDirection
derive instance ordChangeDirection :: Ord ChangeDirection

instance showChangeDirection :: Show ChangeDirection where
  show = changeDirectionToString

-- | Convert change direction to string.
changeDirectionToString :: ChangeDirection -> String
changeDirectionToString cd = case cd of
  ChangeUp -> "up"
  ChangeDown -> "down"
  ChangeFlat -> "flat"

-- | Check if change is positive (up).
isPositiveChange :: ChangeDirection -> Boolean
isPositiveChange ChangeUp = true
isPositiveChange _ = false

-- | Check if change is negative (down).
isNegativeChange :: ChangeDirection -> Boolean
isNegativeChange ChangeDown = true
isNegativeChange _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // refresh configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Refresh interval in milliseconds (1 to 86400000, i.e., 1ms to 24 hours).
-- |
-- | Clamped to valid range on construction. Minimum 1ms prevents spinning,
-- | maximum 24 hours is a reasonable upper bound for polling intervals.
newtype RefreshMs = RefreshMs Int

derive instance eqRefreshMs :: Eq RefreshMs
derive instance ordRefreshMs :: Ord RefreshMs

instance showRefreshMs :: Show RefreshMs where
  show (RefreshMs ms) = show ms <> "ms"

-- | Create a refresh interval, clamping to valid range (1-86400000).
mkRefreshMs :: Int -> RefreshMs
mkRefreshMs ms
  | ms < 1 = RefreshMs 1
  | ms > 86400000 = RefreshMs 86400000
  | otherwise = RefreshMs ms

-- | Unwrap refresh milliseconds.
unwrapRefreshMs :: RefreshMs -> Int
unwrapRefreshMs (RefreshMs ms) = ms

-- | Widget refresh rate.
-- |
-- | Controls how often the widget's data should be refreshed:
-- | - RefreshRealtime: Push updates on every data change
-- | - RefreshInterval: Poll at specified millisecond interval (bounded 1ms-24h)
-- | - RefreshManual: Only refresh on explicit user request
data RefreshRate
  = RefreshRealtime
  | RefreshInterval RefreshMs
  | RefreshManual

derive instance eqRefreshRate :: Eq RefreshRate

instance showRefreshRate :: Show RefreshRate where
  show RefreshRealtime = "realtime"
  show (RefreshInterval ms) = "interval(" <> show ms <> ")"
  show RefreshManual = "manual"

-- | Convert refresh rate to milliseconds.
-- |
-- | Returns Nothing for realtime and manual (no polling interval).
refreshRateToMs :: RefreshRate -> Maybe Int
refreshRateToMs rr = case rr of
  RefreshRealtime -> Nothing
  RefreshInterval ms -> Just (unwrapRefreshMs ms)
  RefreshManual -> Nothing

-- | Default refresh rate: 30 seconds.
defaultRefreshRate :: RefreshRate
defaultRefreshRate = RefreshInterval (mkRefreshMs 30000)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // value formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Value formatting specification.
-- |
-- | Tells the widget how to format numeric values for display.
data ValueFormat
  = FormatNumber
  | FormatCurrency String  -- Currency code (USD, EUR, etc.)
  | FormatPercent
  | FormatDate
  | FormatDatetime
  | FormatDuration
  | FormatCustom String    -- Custom format string

derive instance eqValueFormat :: Eq ValueFormat

instance showValueFormat :: Show ValueFormat where
  show = formatValueToString

-- | Convert value format to string representation.
formatValueToString :: ValueFormat -> String
formatValueToString vf = case vf of
  FormatNumber -> "number"
  FormatCurrency code -> "currency:" <> code
  FormatPercent -> "percent"
  FormatDate -> "date"
  FormatDatetime -> "datetime"
  FormatDuration -> "duration"
  FormatCustom fmt -> "custom:" <> fmt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // grid position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid position for widget placement.
-- |
-- | Widgets are placed on a grid (typically 12 columns).
-- | Position specifies the (x, y) coordinate in grid cells.
type GridPosition =
  { x :: GridColumn
  , y :: GridRow
  }

-- | Create a grid position.
gridPosition :: Int -> Int -> GridPosition
gridPosition x y =
  { x: mkGridColumn x
  , y: mkGridRow y
  }

-- | Default position: top-left corner.
defaultGridPosition :: GridPosition
defaultGridPosition = gridPosition 0 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // widget size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Widget size in grid cells.
-- |
-- | Width is in columns (typically 1-12), height is in rows.
type WidgetSize =
  { width :: GridColumn
  , height :: GridRow
  }

-- | Create a widget size.
widgetSize :: Int -> Int -> WidgetSize
widgetSize w h =
  { width: mkGridColumn w
  , height: mkGridRow h
  }

-- | Small widget: 3 columns, 2 rows.
smallWidget :: WidgetSize
smallWidget = widgetSize 3 2

-- | Medium widget: 4 columns, 2 rows.
mediumWidget :: WidgetSize
mediumWidget = widgetSize 4 2

-- | Large widget: 6 columns, 3 rows.
largeWidget :: WidgetSize
largeWidget = widgetSize 6 3

-- | Full width widget: 12 columns, 4 rows.
fullWidthWidget :: WidgetSize
fullWidthWidget = widgetSize 12 4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // bounded types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid column (0-11 for 12-column grid).
-- |
-- | Clamped to valid range on construction.
newtype GridColumn = GridColumn Int

derive instance eqGridColumn :: Eq GridColumn
derive instance ordGridColumn :: Ord GridColumn

instance showGridColumn :: Show GridColumn where
  show (GridColumn n) = show n

-- | Create a grid column, clamping to valid range (0-11).
mkGridColumn :: Int -> GridColumn
mkGridColumn n
  | n < 0 = GridColumn 0
  | n > 11 = GridColumn 11
  | otherwise = GridColumn n

-- | Unwrap grid column.
unwrapGridColumn :: GridColumn -> Int
unwrapGridColumn (GridColumn n) = n

-- | Grid row (0-99).
-- |
-- | Clamped to valid range on construction.
newtype GridRow = GridRow Int

derive instance eqGridRow :: Eq GridRow
derive instance ordGridRow :: Ord GridRow

instance showGridRow :: Show GridRow where
  show (GridRow n) = show n

-- | Create a grid row, clamping to valid range (0-99).
mkGridRow :: Int -> GridRow
mkGridRow n
  | n < 0 = GridRow 0
  | n > 99 = GridRow 99
  | otherwise = GridRow n

-- | Unwrap grid row.
unwrapGridRow :: GridRow -> Int
unwrapGridRow (GridRow n) = n

-- | Percentage (0.0-100.0).
-- |
-- | Clamped to valid range on construction.
newtype Percentage = Percentage Number

derive instance eqPercentage :: Eq Percentage
derive instance ordPercentage :: Ord Percentage

instance showPercentage :: Show Percentage where
  show (Percentage n) = show n <> "%"

-- | Create a percentage, clamping to valid range (0-100).
mkPercentage :: Number -> Percentage
mkPercentage n
  | n < 0.0 = Percentage 0.0
  | n > 100.0 = Percentage 100.0
  | otherwise = Percentage n

-- | Unwrap percentage.
unwrapPercentage :: Percentage -> Number
unwrapPercentage (Percentage n) = n

-- | Decimal places (0-10).
-- |
-- | Clamped to valid range on construction.
newtype DecimalPlaces = DecimalPlaces Int

derive instance eqDecimalPlaces :: Eq DecimalPlaces
derive instance ordDecimalPlaces :: Ord DecimalPlaces

instance showDecimalPlaces :: Show DecimalPlaces where
  show (DecimalPlaces n) = show n

-- | Create decimal places, clamping to valid range (0-10).
mkDecimalPlaces :: Int -> DecimalPlaces
mkDecimalPlaces n
  | n < 0 = DecimalPlaces 0
  | n > 10 = DecimalPlaces 10
  | otherwise = DecimalPlaces n

-- | Unwrap decimal places.
unwrapDecimalPlaces :: DecimalPlaces -> Int
unwrapDecimalPlaces (DecimalPlaces n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // utility functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a percentage is within a threshold range (inclusive).
-- |
-- | Useful for gauge thresholds and progress indicators.
-- | ```purescript
-- | isInRange (mkPercentage 50.0) (mkPercentage 25.0) (mkPercentage 75.0)  -- true
-- | isInRange (mkPercentage 90.0) (mkPercentage 25.0) (mkPercentage 75.0)  -- false
-- | ```
isInRange :: Percentage -> Percentage -> Percentage -> Boolean
isInRange value low high =
  let v = unwrapPercentage value
      l = unwrapPercentage low
      h = unwrapPercentage high
  in v >= l && v <= h

-- | Check if a percentage exceeds a threshold.
-- |
-- | Used for critical/warning threshold detection in gauges.
exceedsThreshold :: Percentage -> Percentage -> Boolean
exceedsThreshold value threshold =
  unwrapPercentage value > unwrapPercentage threshold

-- | Check if two widget types are the same.
-- |
-- | Useful for filtering or grouping widgets by type.
isSameWidgetType :: WidgetType -> WidgetType -> Boolean
isSameWidgetType a b = a == b

-- | Check if a widget type is a data visualization (Chart, Gauge, Sparkline, Heatmap).
isVisualization :: WidgetType -> Boolean
isVisualization wt = 
  wt == Chart || wt == Gauge || wt == Sparkline || wt == Heatmap

-- | Check if a widget type displays flow/hierarchy (Funnel, Sankey, Treemap).
isFlowWidget :: WidgetType -> Boolean
isFlowWidget wt =
  wt == Funnel || wt == Sankey || wt == Treemap

-- | Check if grid position is at origin.
isOrigin :: GridPosition -> Boolean
isOrigin pos = 
  unwrapGridColumn pos.x == 0 && unwrapGridRow pos.y == 0

-- | Check if a widget fits within grid bounds.
-- |
-- | Given a position and size, checks if the widget stays within
-- | a 12-column grid.
fitsInGrid :: GridPosition -> WidgetSize -> Boolean
fitsInGrid pos size =
  let endCol = unwrapGridColumn pos.x + unwrapGridColumn size.width
  in endCol <= 12

