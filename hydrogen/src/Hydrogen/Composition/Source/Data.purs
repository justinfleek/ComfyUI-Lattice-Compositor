-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // composition // source // data
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Data Sources — Chart, Table, Graph, Map, Metric, Timeline, Heatmap, Tree.
-- |
-- | Data-driven visualizations that generate pixels from query results.

module Hydrogen.Composition.Source.Data
  ( -- * Data Binding
    QueryRef(..)
  , DataRef(..)
  
  -- * Chart
  , ChartSpec
  , ChartType(..)
  , chart
  
  -- * Table
  , TableSpec
  , table
  
  -- * Graph (Network)
  , GraphSpec
  , GraphLayout(..)
  , graph
  
  -- * Map (Geographic)
  , MapSpec
  , MapStyle(..)
  , geoMap
  
  -- * Metric (Single Value)
  , MetricSpec
  , MetricStyle(..)
  , metric
  
  -- * Timeline
  , TimelineSpec
  , timeline
  
  -- * Heatmap
  , HeatmapSpec
  , HeatmapColorScale(..)
  , heatmap
  
  -- * Tree
  , TreeSpec
  , TreeLayout(..)
  , tree
  
  -- * Sankey
  , SankeySpec
  , sankey
  
  -- * Funnel
  , FunnelSpec
  , funnel
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Color.Opacity (Opacity)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // data binding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Reference to a query result.
newtype QueryRef = QueryRef String

derive instance eqQueryRef :: Eq QueryRef
derive instance ordQueryRef :: Ord QueryRef

instance showQueryRef :: Show QueryRef where
  show (QueryRef q) = "(QueryRef " <> show q <> ")"

-- | Reference to data in store.
newtype DataRef = DataRef String

derive instance eqDataRef :: Eq DataRef
derive instance ordDataRef :: Ord DataRef

instance showDataRef :: Show DataRef where
  show (DataRef d) = "(DataRef " <> show d <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Chart type.
data ChartType
  = ChartLine
  | ChartArea
  | ChartBar
  | ChartColumn
  | ChartPie
  | ChartDonut
  | ChartScatter
  | ChartBubble
  | ChartRadar
  | ChartPolar
  | ChartCandlestick
  | ChartWaterfall
  | ChartBox          -- Box plot
  | ChartViolin

derive instance eqChartType :: Eq ChartType

instance showChartType :: Show ChartType where
  show ChartLine = "line"
  show ChartArea = "area"
  show ChartBar = "bar"
  show ChartColumn = "column"
  show ChartPie = "pie"
  show ChartDonut = "donut"
  show ChartScatter = "scatter"
  show ChartBubble = "bubble"
  show ChartRadar = "radar"
  show ChartPolar = "polar"
  show ChartCandlestick = "candlestick"
  show ChartWaterfall = "waterfall"
  show ChartBox = "box"
  show ChartViolin = "violin"

-- | Chart source.
type ChartSpec =
  { chartType :: ChartType
  , data :: QueryRef
  , title :: String
  , showLegend :: Boolean
  , showGrid :: Boolean
  , animate :: Boolean
  , opacity :: Opacity
  }

-- | Create a chart source.
chart :: ChartType -> QueryRef -> String -> Opacity -> ChartSpec
chart chartType d title opacity =
  { chartType, data: d, title, opacity
  , showLegend: true, showGrid: true, animate: true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // table
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Table source.
type TableSpec =
  { data :: QueryRef
  , showHeader :: Boolean
  , striped :: Boolean
  , hoverable :: Boolean
  , sortable :: Boolean
  , pageSize :: Int
  , opacity :: Opacity
  }

-- | Create a table source.
table :: QueryRef -> Opacity -> TableSpec
table d opacity =
  { data: d, opacity
  , showHeader: true, striped: true, hoverable: true
  , sortable: true, pageSize: 50 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // graph
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Graph layout algorithm.
data GraphLayout
  = GraphForce        -- Force-directed
  | GraphHierarchy    -- Hierarchical
  | GraphRadial       -- Radial layout
  | GraphCircular     -- Circular layout
  | GraphGrid         -- Grid layout
  | GraphSpectral     -- Spectral layout

derive instance eqGraphLayout :: Eq GraphLayout

instance showGraphLayout :: Show GraphLayout where
  show GraphForce = "force"
  show GraphHierarchy = "hierarchy"
  show GraphRadial = "radial"
  show GraphCircular = "circular"
  show GraphGrid = "grid"
  show GraphSpectral = "spectral"

-- | Network graph source.
type GraphSpec =
  { data :: QueryRef          -- Nodes and edges
  , layout :: GraphLayout
  , nodeSize :: Number
  , edgeWidth :: Number
  , showLabels :: Boolean
  , physics :: Boolean        -- Interactive physics
  , opacity :: Opacity
  }

-- | Create a graph source.
graph :: QueryRef -> GraphLayout -> Opacity -> GraphSpec
graph d layout opacity =
  { data: d, layout, opacity
  , nodeSize: 10.0, edgeWidth: 1.0, showLabels: true, physics: true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                          // map
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Map style.
data MapStyle
  = MapStreet
  | MapSatellite
  | MapTerrain
  | MapDark
  | MapLight
  | MapOutdoors
  | MapNavigation

derive instance eqMapStyle :: Eq MapStyle

instance showMapStyle :: Show MapStyle where
  show MapStreet = "street"
  show MapSatellite = "satellite"
  show MapTerrain = "terrain"
  show MapDark = "dark"
  show MapLight = "light"
  show MapOutdoors = "outdoors"
  show MapNavigation = "navigation"

-- | Geographic map source.
type MapSpec =
  { data :: QueryRef          -- GeoJSON or coordinates
  , style :: MapStyle
  , centerLat :: Number
  , centerLng :: Number
  , zoom :: Number
  , showMarkers :: Boolean
  , showHeatmap :: Boolean
  , opacity :: Opacity
  }

-- | Create a map source.
geoMap :: QueryRef -> MapStyle -> Number -> Number -> Number -> Opacity -> MapSpec
geoMap d style centerLat centerLng zoom opacity =
  { data: d, style, centerLat, centerLng, zoom, opacity
  , showMarkers: true, showHeatmap: false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // metric
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Metric display style.
data MetricStyle
  = MetricNumber        -- Simple number
  | MetricGauge         -- Radial gauge
  | MetricProgress      -- Progress bar
  | MetricSparkline     -- With sparkline
  | MetricDelta         -- With change indicator
  | MetricComparison    -- Two values compared

derive instance eqMetricStyle :: Eq MetricStyle

instance showMetricStyle :: Show MetricStyle where
  show MetricNumber = "number"
  show MetricGauge = "gauge"
  show MetricProgress = "progress"
  show MetricSparkline = "sparkline"
  show MetricDelta = "delta"
  show MetricComparison = "comparison"

-- | Single value metric source.
type MetricSpec =
  { data :: QueryRef
  , style :: MetricStyle
  , label :: String
  , unit :: String
  , prefix :: String
  , suffix :: String
  , decimals :: Int
  , opacity :: Opacity
  }

-- | Create a metric source.
metric :: QueryRef -> MetricStyle -> String -> Opacity -> MetricSpec
metric d style label opacity =
  { data: d, style, label, opacity
  , unit: "", prefix: "", suffix: "", decimals: 0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // timeline
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Timeline source.
type TimelineSpec =
  { data :: QueryRef          -- Events with timestamps
  , showAxis :: Boolean
  , zoomable :: Boolean
  , orientation :: String     -- "horizontal" or "vertical"
  , opacity :: Opacity
  }

-- | Create a timeline source.
timeline :: QueryRef -> Opacity -> TimelineSpec
timeline d opacity =
  { data: d, opacity
  , showAxis: true, zoomable: true, orientation: "horizontal" }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // heatmap
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Heatmap color scale.
data HeatmapColorScale
  = ScaleViridis
  | ScalePlasma
  | ScaleInferno
  | ScaleMagma
  | ScaleCividis
  | ScaleTurbo
  | ScaleBlueRed
  | ScaleGreenYellow

derive instance eqHeatmapColorScale :: Eq HeatmapColorScale

instance showHeatmapColorScale :: Show HeatmapColorScale where
  show ScaleViridis = "viridis"
  show ScalePlasma = "plasma"
  show ScaleInferno = "inferno"
  show ScaleMagma = "magma"
  show ScaleCividis = "cividis"
  show ScaleTurbo = "turbo"
  show ScaleBlueRed = "blue_red"
  show ScaleGreenYellow = "green_yellow"

-- | Heatmap source.
type HeatmapSpec =
  { data :: QueryRef          -- 2D matrix
  , colorScale :: HeatmapColorScale
  , showValues :: Boolean
  , showAxis :: Boolean
  , opacity :: Opacity
  }

-- | Create a heatmap source.
heatmap :: QueryRef -> HeatmapColorScale -> Opacity -> HeatmapSpec
heatmap d colorScale opacity =
  { data: d, colorScale, opacity
  , showValues: false, showAxis: true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // tree
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tree layout.
data TreeLayout
  = TreeVertical      -- Top to bottom
  | TreeHorizontal    -- Left to right
  | TreeRadialTree    -- Radial tree
  | TreeMindmap       -- Mindmap style
  | TreeDendrogram    -- Dendrogram
  | TreeTreemap       -- Rectangular treemap
  | TreeSunburst      -- Sunburst chart

derive instance eqTreeLayout :: Eq TreeLayout

instance showTreeLayout :: Show TreeLayout where
  show TreeVertical = "vertical"
  show TreeHorizontal = "horizontal"
  show TreeRadialTree = "radial"
  show TreeMindmap = "mindmap"
  show TreeDendrogram = "dendrogram"
  show TreeTreemap = "treemap"
  show TreeSunburst = "sunburst"

-- | Tree source.
type TreeSpec =
  { data :: QueryRef          -- Hierarchical data
  , layout :: TreeLayout
  , showLabels :: Boolean
  , collapsible :: Boolean
  , opacity :: Opacity
  }

-- | Create a tree source.
tree :: QueryRef -> TreeLayout -> Opacity -> TreeSpec
tree d layout opacity =
  { data: d, layout, opacity, showLabels: true, collapsible: true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // sankey
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sankey diagram source.
type SankeySpec =
  { data :: QueryRef          -- Flows
  , nodeWidth :: Number
  , nodePadding :: Number
  , showLabels :: Boolean
  , opacity :: Opacity
  }

-- | Create a sankey source.
sankey :: QueryRef -> Opacity -> SankeySpec
sankey d opacity =
  { data: d, opacity, nodeWidth: 20.0, nodePadding: 10.0, showLabels: true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // funnel
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Funnel chart source.
type FunnelSpec =
  { data :: QueryRef          -- Stages
  , showLabels :: Boolean
  , showValues :: Boolean
  , showPercentage :: Boolean
  , opacity :: Opacity
  }

-- | Create a funnel source.
funnel :: QueryRef -> Opacity -> FunnelSpec
funnel d opacity =
  { data: d, opacity
  , showLabels: true, showValues: true, showPercentage: true }
