-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // widget // chart
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chart Widget — Data visualization with multiple chart types.
-- |
-- | ## Design Philosophy
-- |
-- | A Chart widget displays data visualizations supporting multiple formats:
-- | - Line/Area charts for time series (Cartesian module)
-- | - Bar/Column charts for comparisons (Cartesian module)
-- | - Scatter/Bubble charts for correlations (Cartesian module)
-- | - Pie/Donut charts for proportions (Polar module)
-- | - Radar/Polar charts for multi-dimensional data (Polar module)
-- |
-- | Pure data in, Element out. No FFI. No JavaScript.
-- |
-- | ## Module Structure
-- |
-- | - Chart.Types: ChartType, AxisType, DataPoint, SeriesData, ChartData, props
-- | - Chart.Palette: Color palettes and generation
-- | - Chart.Helpers: Math utilities (using Hydrogen.Math.Core)
-- | - Chart.Cartesian: Line, Area, Bar, Column, Scatter, Bubble renderers
-- | - Chart.Polar: Pie, Donut, Radar, Polar renderers

module Hydrogen.Element.Compound.Widget.Chart
  ( -- * Widget Component
    chartWidget
  , chartWidgetSimple
  
  -- * Re-exports from Types
  , module Types
  
  -- * Re-exports from Palette
  , module Palette
  ) where

import Prelude
  ( show
  , (&&)
  , (<>)
  , (/)
  , (+)
  , (-)
  , (>)
  )

import Data.Array (foldl, mapWithIndex)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Element.Compound.Widget.Chart.Cartesian as Cartesian
import Hydrogen.Element.Compound.Widget.Chart.Palette (defaultPalette, getColorAtIndex)
import Hydrogen.Element.Compound.Widget.Chart.Palette 
  ( defaultPalette
  , pastelPalette
  , vibrantPalette
  , monochromaticPalette
  , generateSeriesColors
  , getColorAtIndex
  ) as Palette
import Hydrogen.Element.Compound.Widget.Chart.Polar as Polar
import Hydrogen.Element.Compound.Widget.Chart.Types 
  ( ChartType(Line, Area, Bar, Column, Pie, Donut, Scatter, Bubble, Radar, Polar)
  , chartTypeToString
  , isCartesian
  , isPolar
  , needsXAxis
  , needsYAxis
  , AxisType(AxisNumeric, AxisCategory, AxisDatetime, AxisLogarithmic)
  , axisTypeToString
  , AxisConfig
  , DataPoint
  , SeriesData
  , ChartData
  , ChartProps
  , ChartProp
  , defaultProps
  , showLegend
  , stacked
  , animated
  , aspectRatio
  , className
  ) as Types
import Hydrogen.Element.Compound.Widget.Chart.Types 
  ( ChartType(Line, Area, Bar, Column, Pie, Donut, Scatter, Bubble, Radar, Polar)
  , ChartData
  , ChartProps
  , ChartProp
  , SeriesData
  , defaultProps
  )
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a chart widget.
-- |
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
-- | The chart is rendered as SVG for crisp scaling.
chartWidget :: forall msg. Array ChartProp -> ChartData -> E.Element msg
chartWidget propMods chartData =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    containerCls = "rounded-lg border bg-card text-card-foreground p-4" <> 
                   " " <> props.className
  in
    E.div_
      [ E.class_ containerCls ]
      [ -- Title
        renderTitle chartData.title chartData.subtitle
      
      -- Chart container
      , E.div_
          [ E.class_ "relative mt-4"
          , E.style "padding-bottom" (show (100.0 / props.aspectRatio) <> "%")
          ]
          [ E.div_
              [ E.class_ "absolute inset-0" ]
              [ renderChart props chartData ]
          ]
      
      -- Legend
      , if chartData.showLegend && props.showLegend
          then renderLegend chartData.series
          else E.text ""
      ]

-- | Simple chart widget (minimal configuration).
chartWidgetSimple :: forall msg. 
  ChartType -> 
  Array { name :: String, values :: Array Number } -> 
  E.Element msg
chartWidgetSimple ct simpleSeries =
  let
    series = mapWithIndex (\idx s ->
      { name: s.name
      , data: mapWithIndex (\i v -> 
          { x: toNumber i
          , y: v
          , z: Nothing
          , label: Nothing
          , color: Nothing
          }
        ) s.values
      , color: Just (getColorAtIndex defaultPalette idx)
      , chartType: Nothing
      , stack: Nothing
      , yAxisIndex: Nothing
      }
    ) simpleSeries
    
    chartData :: ChartData
    chartData =
      { chartType: ct
      , series: series
      , xAxis: Nothing
      , yAxis: Nothing
      , yAxis2: Nothing
      , title: Nothing
      , subtitle: Nothing
      , showLegend: true
      , stacked: false
      , animated: true
      }
  in
    chartWidget [] chartData

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // render dispatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the chart SVG based on chart type.
renderChart :: forall msg. ChartProps -> ChartData -> E.Element msg
renderChart props chartData =
  case chartData.chartType of
    Line -> Cartesian.renderLineChart props chartData
    Area -> Cartesian.renderAreaChart props chartData
    Bar -> Cartesian.renderBarChart props chartData
    Column -> Cartesian.renderColumnChart props chartData
    Scatter -> Cartesian.renderScatterChart props chartData
    Bubble -> Cartesian.renderBubbleChart props chartData
    Pie -> Polar.renderPieChart props chartData
    Donut -> Polar.renderDonutChart props chartData
    Radar -> Polar.renderRadarChart props chartData
    Polar -> Polar.renderPolarChart props chartData

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // render helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render chart title and subtitle.
renderTitle :: forall msg. Maybe String -> Maybe String -> E.Element msg
renderTitle maybeTitle maybeSubtitle =
  case maybeTitle of
    Nothing -> E.text ""
    Just title ->
      E.div_
        [ E.class_ "mb-4" ]
        [ E.h3_
            [ E.class_ "text-lg font-semibold" ]
            [ E.text title ]
        , case maybeSubtitle of
            Nothing -> E.text ""
            Just subtitle ->
              E.p_
                [ E.class_ "text-sm text-muted-foreground" ]
                [ E.text subtitle ]
        ]

-- | Render legend.
renderLegend :: forall msg. Array SeriesData -> E.Element msg
renderLegend series =
  E.div_
    [ E.class_ "flex flex-wrap gap-4 mt-4 justify-center" ]
    (mapWithIndex renderLegendItem series)

-- | Render single legend item.
renderLegendItem :: forall msg. Int -> SeriesData -> E.Element msg
renderLegendItem idx s =
  let
    color = case s.color of
      Just c -> c
      Nothing -> getColorAtIndex defaultPalette idx
  in
    E.div_
      [ E.class_ "flex items-center gap-2" ]
      [ E.div_
          [ E.class_ "w-3 h-3 rounded-full"
          , E.style "background-color" color
          ]
          []
      , E.span_
          [ E.class_ "text-sm text-muted-foreground" ]
          [ E.text s.name ]
      ]

-- | Convert Int to Number.
toNumber :: Int -> Number
toNumber n = 
  let go :: Int -> Number -> Number
      go 0 acc = acc
      go i acc = if i > 0 then go (i - 1) (acc + 1.0) else go (i + 1) (acc - 1.0)
  in go n 0.0
