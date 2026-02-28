-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // widget // chart // polar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Polar Chart Renderers — Pie, Donut, Radar, Polar.
-- |
-- | Charts using circular/radial coordinate systems.
-- | Pure Element output — no framework dependencies.
-- | Math functions from Hydrogen.Math.Core (Taylor series, no FFI).

module Hydrogen.Element.Compound.Widget.Chart.Polar
  ( -- * Chart Renderers
    renderPieChart
  , renderDonutChart
  , renderRadarChart
  , renderPolarChart
  ) where

import Prelude
  ( show
  , (==)
  , (&&)
  , (<>)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  )

import Data.Array (foldl, index, length, mapWithIndex, replicate)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Hydrogen.Element.Compound.Widget.Chart.Helpers (arrayMax, arrayMin, mapPoints, sumArray)
import Hydrogen.Element.Compound.Widget.Chart.Palette (defaultPalette, getColorAtIndex)
import Hydrogen.Element.Compound.Widget.Chart.Types (ChartData, ChartProps, DataPoint, SeriesData)
import Hydrogen.Math.Core (cos, sin)
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // pie chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render pie chart.
renderPieChart :: forall msg. ChartProps -> ChartData -> E.Element msg
renderPieChart _props chartData =
  let
    viewBox = "0 0 200 200"
    cx = 100.0
    cy = 100.0
    r = 80.0
    
    -- Calculate total for percentages
    total = foldl (\acc s ->
      acc + foldl (\a p -> a + p.y) 0.0 s.data
    ) 0.0 chartData.series
    
    -- Generate pie slices
    slices = generatePieSlices chartData.series cx cy r total
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ "w-full h-full"
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      slices

-- | Generate pie slices.
generatePieSlices :: forall msg. Array SeriesData -> Number -> Number -> Number -> Number -> Array (E.Element msg)
generatePieSlices series cx cy r total =
  let
    values = foldl (\acc s ->
      acc <> mapWithIndex (\_ p -> p.y) s.data
    ) [] series
    
    angles = calculateAngles values total
  in
    mapWithIndex (\idx angle ->
      let
        color = getColorAtIndex defaultPalette idx
        startAngle = sumArray (take idx angles)
        endAngle = startAngle + angle
      in
        renderPieSlice cx cy r startAngle endAngle color
    ) angles

-- | Calculate angles for pie slices.
calculateAngles :: Array Number -> Number -> Array Number
calculateAngles values total =
  if total == 0.0
    then mapWithIndex (\_ _ -> 0.0) values
    else mapWithIndex (\_ v -> v / total * 360.0) values

-- | Take first n elements from array.
take :: forall a. Int -> Array a -> Array a
take n arr = 
  let len = length arr
      count = if n < 0 then 0 else if n > len then len else n
  in takeHelper 0 count arr []

takeHelper :: forall a. Int -> Int -> Array a -> Array a -> Array a
takeHelper idx count arr acc =
  if idx >= count 
    then acc
    else case index arr idx of
      Nothing -> acc
      Just x -> takeHelper (idx + 1) count arr (acc <> [x])

-- | Render single pie slice.
renderPieSlice :: forall msg. Number -> Number -> Number -> Number -> Number -> String -> E.Element msg
renderPieSlice cx cy r startAngle endAngle color =
  let
    startRad = (startAngle - 90.0) * 3.14159265359 / 180.0
    endRad = (endAngle - 90.0) * 3.14159265359 / 180.0
    
    x1 = cx + r * cos startRad
    y1 = cy + r * sin startRad
    x2 = cx + r * cos endRad
    y2 = cy + r * sin endRad
    
    largeArc = if endAngle - startAngle > 180.0 then "1" else "0"
    
    d = "M " <> show cx <> " " <> show cy <> 
        " L " <> show x1 <> " " <> show y1 <> 
        " A " <> show r <> " " <> show r <> " 0 " <> largeArc <> " 1 " <> show x2 <> " " <> show y2 <> 
        " Z"
  in
    E.path_
      [ E.attr "d" d
      , E.attr "fill" color
      , E.attr "stroke" "white"
      , E.attr "stroke-width" "2"
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // donut chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render donut chart.
renderDonutChart :: forall msg. ChartProps -> ChartData -> E.Element msg
renderDonutChart props chartData =
  -- Donut is pie with inner radius
  E.div_
    [ E.class_ "relative" ]
    [ renderPieChart props chartData
    , E.div_
        [ E.class_ "absolute inset-0 flex items-center justify-center"
        , E.style "pointer-events" "none"
        ]
        [ E.div_
            [ E.class_ "w-1/2 h-1/2 rounded-full bg-background" ]
            []
        ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // radar chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render radar chart (spider/web chart).
renderRadarChart :: forall msg. ChartProps -> ChartData -> E.Element msg
renderRadarChart _props chartData =
  let
    viewBox = "0 0 300 300"
    cx = 150.0
    cy = 150.0
    maxRadius = 120.0
    
    -- Get number of axes from first series data points
    numAxes = case index chartData.series 0 of
      Nothing -> 0
      Just s -> length s.data
    
    -- Generate axis angles (evenly distributed around circle)
    axisAngles = generateAxisAngles numAxes
    
    -- Calculate data range for scaling
    allPoints = foldl (\acc s -> acc <> s.data) [] chartData.series
    maxVal = arrayMax (mapPoints (\p -> p.y) allPoints)
    minVal = arrayMin (mapPoints (\p -> p.y) allPoints)
    dataRange = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
    
    -- Scale a value to radius
    scaleToRadius :: Number -> Number
    scaleToRadius v = ((v - minVal) / dataRange) * maxRadius
    
    -- Render grid circles (concentric rings)
    gridCircles = renderRadarGrid cx cy maxRadius 5
    
    -- Render axis lines
    axisLines = renderRadarAxes cx cy maxRadius axisAngles
    
    -- Render axis labels
    axisLabels = renderRadarLabels cx cy maxRadius axisAngles chartData
    
    -- Render data polygons for each series
    dataPolygons = mapWithIndex 
      (renderRadarSeries cx cy scaleToRadius axisAngles) 
      chartData.series
  in
    if numAxes < 3
      then 
        E.div_
          [ E.class_ "flex items-center justify-center h-full text-muted-foreground" ]
          [ E.text "Radar chart requires at least 3 data points" ]
      else
        E.svg_
          [ E.attr "viewBox" viewBox
          , E.class_ "w-full h-full"
          , E.attr "preserveAspectRatio" "xMidYMid meet"
          ]
          ([ gridCircles, axisLines, axisLabels ] <> dataPolygons)

-- | Generate evenly spaced angles for radar axes.
generateAxisAngles :: Int -> Array Number
generateAxisAngles n =
  if n <= 0 
    then []
    else mapWithIndex (\idx _ -> 
      (toNumber idx / toNumber n) * 360.0 - 90.0
    ) (replicate n 0)

-- | Render concentric grid circles for radar chart.
renderRadarGrid :: forall msg. Number -> Number -> Number -> Int -> E.Element msg
renderRadarGrid cx cy maxRadius numRings =
  E.g_
    [ E.class_ "radar-grid" ]
    (mapWithIndex (\idx _ ->
      let
        r = maxRadius * (toNumber (idx + 1) / toNumber numRings)
      in
        E.circle_
          [ E.attr "cx" (show cx)
          , E.attr "cy" (show cy)
          , E.attr "r" (show r)
          , E.attr "fill" "none"
          , E.attr "stroke" "currentColor"
          , E.attr "stroke-opacity" "0.1"
          , E.attr "stroke-width" "1"
          ]
    ) (replicate numRings 0))

-- | Render axis lines radiating from center.
renderRadarAxes :: forall msg. Number -> Number -> Number -> Array Number -> E.Element msg
renderRadarAxes cx cy maxRadius angles =
  E.g_
    [ E.class_ "radar-axes" ]
    (mapWithIndex (\_ angle ->
      let
        rad = angle * 3.14159265359 / 180.0
        x2 = cx + maxRadius * cos rad
        y2 = cy + maxRadius * sin rad
      in
        E.line_
          [ E.attr "x1" (show cx)
          , E.attr "y1" (show cy)
          , E.attr "x2" (show x2)
          , E.attr "y2" (show y2)
          , E.attr "stroke" "currentColor"
          , E.attr "stroke-opacity" "0.2"
          , E.attr "stroke-width" "1"
          ]
    ) angles)

-- | Render axis labels at the outer edge.
renderRadarLabels :: forall msg. Number -> Number -> Number -> Array Number -> ChartData -> E.Element msg
renderRadarLabels cx cy maxRadius angles chartData =
  let
    labelRadius = maxRadius + 15.0
    
    -- Get labels from first series data point labels, or use indices
    labels = case index chartData.series 0 of
      Nothing -> []
      Just s -> mapWithIndex (\idx p -> 
        fromMaybe ("Axis " <> show (idx + 1)) p.label
      ) s.data
  in
    E.g_
      [ E.class_ "radar-labels" ]
      (mapWithIndex (\idx angle ->
        let
          rad = angle * 3.14159265359 / 180.0
          x = cx + labelRadius * cos rad
          y = cy + labelRadius * sin rad
          labelText = fromMaybe "" (index labels idx)
          
          -- Adjust text anchor based on position
          anchor = 
            if angle > (negate 45.0) && angle < 45.0 then "start"
            else if angle > 135.0 || angle < (negate 135.0) then "end"
            else "middle"
        in
          E.text_
            [ E.attr "x" (show x)
            , E.attr "y" (show y)
            , E.attr "text-anchor" anchor
            , E.attr "dominant-baseline" "middle"
            , E.attr "font-size" "10"
            , E.attr "fill" "currentColor"
            , E.attr "fill-opacity" "0.7"
            ]
            [ E.text labelText ]
      ) angles)

-- | Render a single series as a polygon on the radar chart.
renderRadarSeries :: forall msg. 
  Number -> 
  Number -> 
  (Number -> Number) -> 
  Array Number -> 
  Int -> 
  SeriesData -> 
  E.Element msg
renderRadarSeries cx cy scaleToRadius angles idx series =
  let
    color = fromMaybe (getColorAtIndex defaultPalette idx) series.color
    
    -- Calculate polygon vertices
    vertices = mapWithIndex (\i angle ->
      let
        dataPoint = index series.data i
        value = case dataPoint of
          Just p -> p.y
          Nothing -> 0.0
        r = scaleToRadius value
        rad = angle * 3.14159265359 / 180.0
        x = cx + r * cos rad
        y = cy + r * sin rad
      in
        { x: x, y: y }
    ) angles
    
    -- Generate path data for polygon
    pathData = foldl (\acc vertex ->
      if acc == ""
        then "M " <> show vertex.x <> " " <> show vertex.y
        else acc <> " L " <> show vertex.x <> " " <> show vertex.y
    ) "" vertices
    
    closedPath = pathData <> " Z"
  in
    E.g_
      [ E.class_ "radar-series" ]
      [ -- Filled polygon
        E.path_
          [ E.attr "d" closedPath
          , E.attr "fill" color
          , E.attr "fill-opacity" "0.2"
          , E.attr "stroke" color
          , E.attr "stroke-width" "2"
          , E.attr "stroke-linejoin" "round"
          ]
      -- Data points
      , E.g_
          [ E.class_ "radar-points" ]
          (mapWithIndex (\_ vertex ->
            E.circle_
              [ E.attr "cx" (show vertex.x)
              , E.attr "cy" (show vertex.y)
              , E.attr "r" "4"
              , E.attr "fill" color
              ]
          ) vertices)
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // polar chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render polar chart (circular bar chart with angular positioning).
renderPolarChart :: forall msg. ChartProps -> ChartData -> E.Element msg
renderPolarChart _props chartData =
  let
    viewBox = "0 0 300 300"
    cx = 150.0
    cy = 150.0
    maxRadius = 120.0
    
    -- Collect all data points from first series
    dataPoints = case index chartData.series 0 of
      Nothing -> []
      Just s -> s.data
    
    numPoints = length dataPoints
    
    -- Calculate angle per segment
    anglePerSegment = if numPoints == 0 then 0.0 else 360.0 / toNumber numPoints
    
    -- Calculate data range for scaling radius
    maxVal = arrayMax (mapPoints (\p -> p.y) dataPoints)
    minVal = arrayMin (mapPoints (\p -> p.y) dataPoints)
    dataRange = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
    
    -- Scale value to radius
    scaleToRadius :: Number -> Number
    scaleToRadius v = ((v - minVal) / dataRange) * maxRadius
    
    -- Render grid circles
    gridCircles = renderPolarGrid cx cy maxRadius 4
    
    -- Render polar segments
    segments = mapWithIndex 
      (renderPolarSegment cx cy scaleToRadius anglePerSegment) 
      dataPoints
    
    -- Render labels
    labels = renderPolarLabels cx cy maxRadius anglePerSegment dataPoints
  in
    if numPoints == 0
      then
        E.div_
          [ E.class_ "flex items-center justify-center h-full text-muted-foreground" ]
          [ E.text "No data for polar chart" ]
      else
        E.svg_
          [ E.attr "viewBox" viewBox
          , E.class_ "w-full h-full"
          , E.attr "preserveAspectRatio" "xMidYMid meet"
          ]
          ([ gridCircles ] <> segments <> [ labels ])

-- | Render concentric grid circles for polar chart.
renderPolarGrid :: forall msg. Number -> Number -> Number -> Int -> E.Element msg
renderPolarGrid cx cy maxRadius numRings =
  E.g_
    [ E.class_ "polar-grid" ]
    (mapWithIndex (\idx _ ->
      let
        r = maxRadius * (toNumber (idx + 1) / toNumber numRings)
      in
        E.circle_
          [ E.attr "cx" (show cx)
          , E.attr "cy" (show cy)
          , E.attr "r" (show r)
          , E.attr "fill" "none"
          , E.attr "stroke" "currentColor"
          , E.attr "stroke-opacity" "0.1"
          , E.attr "stroke-width" "1"
          ]
    ) (replicate numRings 0))

-- | Render a single polar segment (arc from center).
renderPolarSegment :: forall msg. 
  Number -> 
  Number -> 
  (Number -> Number) -> 
  Number -> 
  Int -> 
  DataPoint -> 
  E.Element msg
renderPolarSegment cx cy scaleToRadius anglePerSegment idx dataPoint =
  let
    color = fromMaybe (getColorAtIndex defaultPalette idx) dataPoint.color
    r = scaleToRadius dataPoint.y
    
    -- Calculate start and end angles (starting from top, going clockwise)
    startAngle = toNumber idx * anglePerSegment - 90.0
    endAngle = startAngle + anglePerSegment
    
    -- Add small gap between segments
    gapAngle = 1.0
    adjustedStart = startAngle + gapAngle / 2.0
    adjustedEnd = endAngle - gapAngle / 2.0
    
    -- Convert to radians
    startRad = adjustedStart * 3.14159265359 / 180.0
    endRad = adjustedEnd * 3.14159265359 / 180.0
    
    -- Calculate arc points
    x1 = cx + r * cos startRad
    y1 = cy + r * sin startRad
    x2 = cx + r * cos endRad
    y2 = cy + r * sin endRad
    
    -- Determine if large arc flag needed
    largeArc = if adjustedEnd - adjustedStart > 180.0 then "1" else "0"
    
    -- SVG path: Move to center, line to start of arc, arc to end, close
    d = "M " <> show cx <> " " <> show cy <> 
        " L " <> show x1 <> " " <> show y1 <>
        " A " <> show r <> " " <> show r <> " 0 " <> largeArc <> " 1 " <> show x2 <> " " <> show y2 <>
        " Z"
  in
    E.path_
      [ E.attr "d" d
      , E.attr "fill" color
      , E.attr "fill-opacity" "0.8"
      , E.attr "stroke" color
      , E.attr "stroke-width" "1"
      ]

-- | Render labels around the polar chart.
renderPolarLabels :: forall msg. Number -> Number -> Number -> Number -> Array DataPoint -> E.Element msg
renderPolarLabels cx cy maxRadius anglePerSegment dataPoints =
  let
    labelRadius = maxRadius + 15.0
  in
    E.g_
      [ E.class_ "polar-labels" ]
      (mapWithIndex (\idx p ->
        let
          -- Position label at center of segment
          midAngle = toNumber idx * anglePerSegment + anglePerSegment / 2.0 - 90.0
          rad = midAngle * 3.14159265359 / 180.0
          x = cx + labelRadius * cos rad
          y = cy + labelRadius * sin rad
          
          labelText = fromMaybe ("" <> show (idx + 1)) p.label
          
          -- Adjust text anchor based on position
          anchor = 
            if midAngle > (negate 45.0) && midAngle < 45.0 then "start"
            else if midAngle > 135.0 || midAngle < (negate 135.0) then "end"
            else "middle"
        in
          E.text_
            [ E.attr "x" (show x)
            , E.attr "y" (show y)
            , E.attr "text-anchor" anchor
            , E.attr "dominant-baseline" "middle"
            , E.attr "font-size" "10"
            , E.attr "fill" "currentColor"
            , E.attr "fill-opacity" "0.7"
            ]
            [ E.text labelText ]
      ) dataPoints)
