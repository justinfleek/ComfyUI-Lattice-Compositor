-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // element // widget // chart // cartesian
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cartesian Chart Renderers — Line, Area, Bar, Column, Scatter, Bubble.
-- |
-- | Charts using X/Y coordinate systems with axes.
-- | Pure Element output — no framework dependencies.

module Hydrogen.Element.Compound.Widget.Chart.Cartesian
  ( -- * Chart Renderers
    renderLineChart
  , renderAreaChart
  , renderBarChart
  , renderColumnChart
  , renderScatterChart
  , renderBubbleChart
  
  -- * Shared Components
  , renderAxes
  ) where

import Prelude
  ( show
  , (==)
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Array (foldl, index, length, mapWithIndex)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Hydrogen.Element.Compound.Widget.Chart.Helpers (arrayMax, arrayMin, mapPoints)
import Hydrogen.Element.Compound.Widget.Chart.Palette (defaultPalette, getColorAtIndex)
import Hydrogen.Element.Compound.Widget.Chart.Types (ChartData, ChartProps, DataPoint, SeriesData)
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // line chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render line chart.
renderLineChart :: forall msg. ChartProps -> ChartData -> E.Element msg
renderLineChart _props chartData =
  let
    viewBox = "0 0 400 200"
    chartWidth = 400.0
    chartHeight = 200.0
    padding = 40.0
    
    -- Calculate data bounds
    allPoints = foldl (\acc s -> acc <> s.data) [] chartData.series
    minX = arrayMin (mapPoints (\p -> p.x) allPoints)
    maxX = arrayMax (mapPoints (\p -> p.x) allPoints)
    minY = arrayMin (mapPoints (\p -> p.y) allPoints)
    maxY = arrayMax (mapPoints (\p -> p.y) allPoints)
    
    rangeX = if maxX - minX == 0.0 then 1.0 else maxX - minX
    rangeY = if maxY - minY == 0.0 then 1.0 else maxY - minY
    
    plotWidth = chartWidth - padding * 2.0
    plotHeight = chartHeight - padding * 2.0
    
    scaleX :: Number -> Number
    scaleX x = padding + ((x - minX) / rangeX) * plotWidth
    
    scaleY :: Number -> Number
    scaleY y = padding + plotHeight - ((y - minY) / rangeY) * plotHeight
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ "w-full h-full"
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      ([ renderAxes chartData padding plotWidth plotHeight
       ] <> mapWithIndex (renderLineSeries scaleX scaleY) chartData.series)

-- | Render a single line series.
renderLineSeries :: forall msg. 
  (Number -> Number) -> 
  (Number -> Number) -> 
  Int -> 
  SeriesData -> 
  E.Element msg
renderLineSeries scaleX scaleY idx series =
  let
    color = fromMaybe (getColorAtIndex defaultPalette idx) series.color
    pathData = generateLinePath scaleX scaleY series.data
  in
    E.path_
      [ E.attr "d" pathData
      , E.attr "fill" "none"
      , E.attr "stroke" color
      , E.attr "stroke-width" "2"
      , E.attr "stroke-linecap" "round"
      , E.attr "stroke-linejoin" "round"
      ]

-- | Generate SVG path data for line series.
generateLinePath :: (Number -> Number) -> (Number -> Number) -> Array DataPoint -> String
generateLinePath scaleX scaleY points =
  let
    pathParts = mapWithIndex (\idx p ->
      let x = scaleX p.x
          y = scaleY p.y
      in if idx == 0
           then "M " <> show x <> " " <> show y
           else "L " <> show x <> " " <> show y
    ) points
  in
    foldl (\acc part -> acc <> " " <> part) "" pathParts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // area chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render area chart (line with filled area to baseline).
renderAreaChart :: forall msg. ChartProps -> ChartData -> E.Element msg
renderAreaChart _props chartData =
  let
    viewBox = "0 0 400 200"
    chartWidth = 400.0
    chartHeight = 200.0
    padding = 40.0
    
    -- Calculate data bounds
    allPoints = foldl (\acc s -> acc <> s.data) [] chartData.series
    minX = arrayMin (mapPoints (\p -> p.x) allPoints)
    maxX = arrayMax (mapPoints (\p -> p.x) allPoints)
    minY = arrayMin (mapPoints (\p -> p.y) allPoints)
    maxY = arrayMax (mapPoints (\p -> p.y) allPoints)
    
    rangeX = if maxX - minX == 0.0 then 1.0 else maxX - minX
    rangeY = if maxY - minY == 0.0 then 1.0 else maxY - minY
    
    plotWidth = chartWidth - padding * 2.0
    plotHeight = chartHeight - padding * 2.0
    
    -- Baseline Y coordinate (bottom of plot)
    baselineY = padding + plotHeight
    
    scaleX :: Number -> Number
    scaleX x = padding + ((x - minX) / rangeX) * plotWidth
    
    scaleY :: Number -> Number
    scaleY y = padding + plotHeight - ((y - minY) / rangeY) * plotHeight
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ "w-full h-full"
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      ([ renderAxes chartData padding plotWidth plotHeight
       ] <> mapWithIndex (renderAreaSeries scaleX scaleY baselineY) chartData.series)

-- | Render a single area series (filled region + line).
renderAreaSeries :: forall msg. 
  (Number -> Number) -> 
  (Number -> Number) -> 
  Number -> 
  Int -> 
  SeriesData -> 
  E.Element msg
renderAreaSeries scaleX scaleY baselineY idx series =
  let
    color = fromMaybe (getColorAtIndex defaultPalette idx) series.color
    
    -- Generate the area path (closed polygon from baseline)
    areaPath = generateAreaPath scaleX scaleY baselineY series.data
    
    -- Generate the line path (for crisp line on top)
    linePath = generateLinePath scaleX scaleY series.data
  in
    E.g_
      [ E.class_ "area-series" ]
      [ -- Filled area
        E.path_
          [ E.attr "d" areaPath
          , E.attr "fill" color
          , E.attr "fill-opacity" "0.3"
          , E.attr "stroke" "none"
          ]
      -- Line on top
      , E.path_
          [ E.attr "d" linePath
          , E.attr "fill" "none"
          , E.attr "stroke" color
          , E.attr "stroke-width" "2"
          , E.attr "stroke-linecap" "round"
          , E.attr "stroke-linejoin" "round"
          ]
      ]

-- | Generate SVG path data for filled area.
generateAreaPath :: (Number -> Number) -> (Number -> Number) -> Number -> Array DataPoint -> String
generateAreaPath scaleX scaleY baselineY points =
  let
    -- Get first and last X coordinates for baseline
    firstX = case index points 0 of
      Just p -> scaleX p.x
      Nothing -> 0.0
    lastX = case index points (length points - 1) of
      Just p -> scaleX p.x
      Nothing -> 0.0
    
    -- Start at baseline under first point
    startPath = "M " <> show firstX <> " " <> show baselineY
    
    -- Line up to first data point and through all points
    dataPath = foldl (\acc p ->
      let x = scaleX p.x
          y = scaleY p.y
      in acc <> " L " <> show x <> " " <> show y
    ) "" points
    
    -- Line down to baseline and close
    closePath = " L " <> show lastX <> " " <> show baselineY <> " Z"
  in
    startPath <> dataPath <> closePath

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // bar chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render bar chart (horizontal bars).
renderBarChart :: forall msg. ChartProps -> ChartData -> E.Element msg
renderBarChart _props chartData =
  let
    viewBox = "0 0 400 200"
    numSeries = length chartData.series
    barHeight = if numSeries == 0 then 20.0 else 160.0 / toNumber numSeries
    padding = 20.0
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ "w-full h-full"
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      (mapWithIndex (renderBarSeries barHeight padding) chartData.series)

-- | Render bar series.
renderBarSeries :: forall msg. Number -> Number -> Int -> SeriesData -> E.Element msg
renderBarSeries barHeight padding idx series =
  let
    color = fromMaybe (getColorAtIndex defaultPalette idx) series.color
    y = padding + toNumber idx * barHeight
    -- Use first data point's value as bar width (simplified)
    firstPoint = index series.data 0
    width = case firstPoint of
      Just p -> p.y / 100.0 * 360.0  -- Assume max 100, scale to 360px
      Nothing -> 0.0
  in
    E.rect_
      [ E.attr "x" (show padding)
      , E.attr "y" (show y)
      , E.attr "width" (show width)
      , E.attr "height" (show (barHeight * 0.8))
      , E.attr "fill" color
      , E.attr "rx" "4"
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // column chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render column chart (vertical bars).
renderColumnChart :: forall msg. ChartProps -> ChartData -> E.Element msg
renderColumnChart _props chartData =
  let
    viewBox = "0 0 400 200"
    numSeries = length chartData.series
    barWidth = if numSeries == 0 then 30.0 else 360.0 / toNumber numSeries
    padding = 20.0
    chartHeight = 200.0
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ "w-full h-full"
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      (mapWithIndex (renderColumnSeries barWidth padding chartHeight) chartData.series)

-- | Render column series.
renderColumnSeries :: forall msg. Number -> Number -> Number -> Int -> SeriesData -> E.Element msg
renderColumnSeries barWidth padding chartHeight idx series =
  let
    color = fromMaybe (getColorAtIndex defaultPalette idx) series.color
    x = padding + toNumber idx * barWidth
    -- Use first data point's value as bar height (simplified)
    firstPoint = index series.data 0
    height = case firstPoint of
      Just p -> p.y / 100.0 * (chartHeight - padding * 2.0)
      Nothing -> 0.0
    y = chartHeight - padding - height
  in
    E.rect_
      [ E.attr "x" (show x)
      , E.attr "y" (show y)
      , E.attr "width" (show (barWidth * 0.8))
      , E.attr "height" (show height)
      , E.attr "fill" color
      , E.attr "rx" "4"
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // scatter chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render scatter chart.
renderScatterChart :: forall msg. ChartProps -> ChartData -> E.Element msg
renderScatterChart _props chartData =
  let
    viewBox = "0 0 400 200"
    padding = 40.0
    plotWidth = 320.0
    plotHeight = 120.0
    
    allPoints = foldl (\acc s -> acc <> s.data) [] chartData.series
    minX = arrayMin (mapPoints (\p -> p.x) allPoints)
    maxX = arrayMax (mapPoints (\p -> p.x) allPoints)
    minY = arrayMin (mapPoints (\p -> p.y) allPoints)
    maxY = arrayMax (mapPoints (\p -> p.y) allPoints)
    
    rangeX = if maxX - minX == 0.0 then 1.0 else maxX - minX
    rangeY = if maxY - minY == 0.0 then 1.0 else maxY - minY
    
    scaleX x = padding + ((x - minX) / rangeX) * plotWidth
    scaleY y = padding + plotHeight - ((y - minY) / rangeY) * plotHeight
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ "w-full h-full"
      ]
      (foldl (\acc s ->
        acc <> mapWithIndex (\_ p ->
          let
            color = fromMaybe "#3B82F6" s.color
          in
            E.circle_
              [ E.attr "cx" (show (scaleX p.x))
              , E.attr "cy" (show (scaleY p.y))
              , E.attr "r" "4"
              , E.attr "fill" color
              ]
        ) s.data
      ) [] chartData.series)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // bubble chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render bubble chart (scatter with variable radius from z dimension).
renderBubbleChart :: forall msg. ChartProps -> ChartData -> E.Element msg
renderBubbleChart _props chartData =
  let
    viewBox = "0 0 400 200"
    padding = 40.0
    plotWidth = 320.0
    plotHeight = 120.0
    
    allPoints = foldl (\acc s -> acc <> s.data) [] chartData.series
    minX = arrayMin (mapPoints (\p -> p.x) allPoints)
    maxX = arrayMax (mapPoints (\p -> p.x) allPoints)
    minY = arrayMin (mapPoints (\p -> p.y) allPoints)
    maxY = arrayMax (mapPoints (\p -> p.y) allPoints)
    
    -- Get z range for scaling bubble sizes
    zValues = mapPoints (\p -> fromMaybe 1.0 p.z) allPoints
    minZ = arrayMin zValues
    maxZ = arrayMax zValues
    rangeZ = if maxZ - minZ == 0.0 then 1.0 else maxZ - minZ
    
    rangeX = if maxX - minX == 0.0 then 1.0 else maxX - minX
    rangeY = if maxY - minY == 0.0 then 1.0 else maxY - minY
    
    scaleX x = padding + ((x - minX) / rangeX) * plotWidth
    scaleY y = padding + plotHeight - ((y - minY) / rangeY) * plotHeight
    
    -- Scale z value to bubble radius (min 4, max 30)
    minRadius = 4.0
    maxRadius = 30.0
    scaleZ :: Number -> Number
    scaleZ z = minRadius + ((z - minZ) / rangeZ) * (maxRadius - minRadius)
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ "w-full h-full"
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      ([ renderAxes chartData padding plotWidth plotHeight
       ] <> foldl (\acc s ->
        acc <> mapWithIndex (\_ p ->
          let
            color = fromMaybe "#3B82F6" s.color
            zVal = fromMaybe 1.0 p.z
            radius = scaleZ zVal
          in
            E.circle_
              [ E.attr "cx" (show (scaleX p.x))
              , E.attr "cy" (show (scaleY p.y))
              , E.attr "r" (show radius)
              , E.attr "fill" color
              , E.attr "fill-opacity" "0.6"
              , E.attr "stroke" color
              , E.attr "stroke-width" "1"
              ]
        ) s.data
      ) [] chartData.series)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // shared: axes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render axes.
renderAxes :: forall msg. ChartData -> Number -> Number -> Number -> E.Element msg
renderAxes _chartData padding plotWidth plotHeight =
  let
    x0 = padding
    y0 = padding + plotHeight
    x1 = padding + plotWidth
    y1 = padding
  in
    E.g_
      [ E.class_ "axes" ]
      [ -- X axis
        E.line_
          [ E.attr "x1" (show x0)
          , E.attr "y1" (show y0)
          , E.attr "x2" (show x1)
          , E.attr "y2" (show y0)
          , E.attr "stroke" "currentColor"
          , E.attr "stroke-opacity" "0.2"
          , E.attr "stroke-width" "1"
          ]
      -- Y axis
      , E.line_
          [ E.attr "x1" (show x0)
          , E.attr "y1" (show y0)
          , E.attr "x2" (show x0)
          , E.attr "y2" (show y1)
          , E.attr "stroke" "currentColor"
          , E.attr "stroke-opacity" "0.2"
          , E.attr "stroke-width" "1"
          ]
      ]
