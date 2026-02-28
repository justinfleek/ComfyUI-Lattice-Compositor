-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // element // widget // chart-advanced // stacked
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stacked Charts — Bar and column charts showing composition.
-- |
-- | ## Design Philosophy
-- |
-- | Stacked charts show how a total breaks down into component parts.
-- | Each bar/column is divided into segments representing different series,
-- | stacked on top of each other.
-- |
-- | - **stackedBarChart**: Horizontal stacked bars (rows)
-- | - **stackedColumnChart**: Vertical stacked columns
-- |
-- | Common uses:
-- | - Revenue breakdown by product line
-- | - Time allocation by activity
-- | - Portfolio composition
-- |
-- | Pure Element output — no framework dependencies.

module Hydrogen.Element.Compound.Widget.ChartAdvanced.Stacked
  ( -- * Types
    StackedData
  , StackedConfig
  
  -- * Defaults
  , defaultStackedConfig
  
  -- * Rendering
  , stackedBarChart
  , stackedColumnChart
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (==)
  , (<>)
  , (<=)
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Array (foldl, index, length, mapWithIndex)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing), fromMaybe)
import Hydrogen.Element.Compound.Widget.Chart.Helpers (arrayMax)
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stacked chart data.
-- |
-- | Each category has multiple values (one per series), which will be stacked.
type StackedData =
  { category :: String
  , values :: Array Number  -- ^ One value per series
  }

-- | Stacked chart configuration.
type StackedConfig =
  { title :: Maybe String
  , width :: Number
  , height :: Number
  , seriesNames :: Array String
  , seriesColors :: Array String
  , className :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default stacked configuration.
defaultStackedConfig :: StackedConfig
defaultStackedConfig =
  { title: Nothing
  , width: 400.0
  , height: 200.0
  , seriesNames: []
  , seriesColors: ["#22C55E", "#8B5CF6", "#3B82F6", "#FBBF24", "#F43F5E"]
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // stacked bar
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a stacked bar chart (horizontal).
stackedBarChart :: forall msg. StackedConfig -> Array StackedData -> E.Element msg
stackedBarChart cfg dataPoints =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    padding = 40.0
    plotWidth = cfg.width - padding * 2.0
    plotHeight = cfg.height - padding * 2.0
    
    numCategories = length dataPoints
    barHeight = if numCategories <= 0 then 20.0 else (plotHeight / toNumber numCategories) * 0.7
    
    -- Get max total for scaling
    totals = mapWithIndex (\_ d -> foldl (+) 0.0 d.values) dataPoints
    maxTotal = arrayMax totals
    
    scaleX :: Number -> Number
    scaleX v = if maxTotal == 0.0 then 0.0 else (v / maxTotal) * plotWidth
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ ("w-full h-full " <> cfg.className)
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      [ E.g_
          [ E.class_ "stacked-bars" ]
          (mapWithIndex (renderStackedBarRow cfg padding barHeight scaleX) dataPoints)
      ]

-- | Render a single stacked bar row.
renderStackedBarRow :: forall msg.
  StackedConfig ->
  Number ->
  Number ->
  (Number -> Number) ->
  Int ->
  StackedData ->
  E.Element msg
renderStackedBarRow cfg padding barHeight scaleX rowIdx rowData =
  let
    y = padding + toNumber rowIdx * (barHeight * 1.4)
    
    -- Calculate segment positions
    segments = calculateStackedSegments cfg.seriesColors rowData.values scaleX
  in
    E.g_
      []
      ([ E.text_
           [ E.attr "x" (show (padding - 5.0))
           , E.attr "y" (show (y + barHeight / 2.0))
           , E.attr "text-anchor" "end"
           , E.attr "dominant-baseline" "middle"
           , E.attr "font-size" "10"
           , E.attr "fill" "currentColor"
           , E.attr "fill-opacity" "0.7"
           ]
           [ E.text rowData.category ]
       ] <> mapWithIndex (\_ seg ->
         E.rect_
           [ E.attr "x" (show (padding + seg.x))
           , E.attr "y" (show y)
           , E.attr "width" (show seg.width)
           , E.attr "height" (show barHeight)
           , E.attr "fill" seg.color
           , E.attr "rx" "2"
           , E.style "filter" ("drop-shadow(0 0 6px " <> seg.color <> "50)")
           ]
       ) segments)

-- | Calculate stacked segment positions.
calculateStackedSegments :: Array String -> Array Number -> (Number -> Number) -> Array { x :: Number, width :: Number, color :: String }
calculateStackedSegments colors values scaleX =
  let
    go :: { runningX :: Number, segments :: Array { x :: Number, width :: Number, color :: String } } -> 
          { idx :: Int, value :: Number } -> 
          { runningX :: Number, segments :: Array { x :: Number, width :: Number, color :: String } }
    go acc item =
      let
        width = scaleX item.value
        color = fromMaybe "#3B82F6" (index colors item.idx)
        segment = { x: acc.runningX, width: width, color: color }
      in
        { runningX: acc.runningX + width, segments: acc.segments <> [segment] }
    
    indexed = mapWithIndex (\idx v -> { idx: idx, value: v }) values
    result = foldl go { runningX: 0.0, segments: [] } indexed
  in
    result.segments

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // stacked column
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a stacked column chart (vertical).
stackedColumnChart :: forall msg. StackedConfig -> Array StackedData -> E.Element msg
stackedColumnChart cfg dataPoints =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    padding = 40.0
    plotWidth = cfg.width - padding * 2.0
    plotHeight = cfg.height - padding * 2.0
    
    numCategories = length dataPoints
    barWidth = if numCategories <= 0 then 30.0 else (plotWidth / toNumber numCategories) * 0.7
    
    -- Get max total for scaling
    totals = mapWithIndex (\_ d -> foldl (+) 0.0 d.values) dataPoints
    maxTotal = arrayMax totals
    
    scaleY :: Number -> Number
    scaleY v = if maxTotal == 0.0 then 0.0 else (v / maxTotal) * plotHeight
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ ("w-full h-full " <> cfg.className)
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      [ E.g_
          [ E.class_ "stacked-columns" ]
          (mapWithIndex (renderStackedColumnGroup cfg padding plotHeight barWidth scaleY) dataPoints)
      ]

-- | Render a single stacked column.
renderStackedColumnGroup :: forall msg.
  StackedConfig ->
  Number ->
  Number ->
  Number ->
  (Number -> Number) ->
  Int ->
  StackedData ->
  E.Element msg
renderStackedColumnGroup cfg padding plotHeight barWidth scaleY colIdx colData =
  let
    x = padding + toNumber colIdx * (barWidth * 1.4) + barWidth * 0.2
    baseline = padding + plotHeight
    
    -- Calculate segment positions (bottom to top)
    segments = calculateStackedColumnSegments cfg.seriesColors colData.values scaleY baseline
  in
    E.g_
      []
      ([ E.text_
           [ E.attr "x" (show (x + barWidth / 2.0))
           , E.attr "y" (show (baseline + 15.0))
           , E.attr "text-anchor" "middle"
           , E.attr "font-size" "10"
           , E.attr "fill" "currentColor"
           , E.attr "fill-opacity" "0.7"
           ]
           [ E.text colData.category ]
       ] <> mapWithIndex (\_ seg ->
         E.rect_
           [ E.attr "x" (show x)
           , E.attr "y" (show seg.y)
           , E.attr "width" (show barWidth)
           , E.attr "height" (show seg.height)
           , E.attr "fill" seg.color
           , E.attr "rx" "2"
           , E.style "filter" ("drop-shadow(0 0 6px " <> seg.color <> "50)")
           ]
       ) segments)

-- | Calculate stacked column segment positions.
calculateStackedColumnSegments :: Array String -> Array Number -> (Number -> Number) -> Number -> Array { y :: Number, height :: Number, color :: String }
calculateStackedColumnSegments colors values scaleY baseline =
  let
    go :: { runningY :: Number, segments :: Array { y :: Number, height :: Number, color :: String } } -> 
          { idx :: Int, value :: Number } -> 
          { runningY :: Number, segments :: Array { y :: Number, height :: Number, color :: String } }
    go acc item =
      let
        height = scaleY item.value
        color = fromMaybe "#3B82F6" (index colors item.idx)
        y = acc.runningY - height
        segment = { y: y, height: height, color: color }
      in
        { runningY: y, segments: acc.segments <> [segment] }
    
    indexed = mapWithIndex (\idx v -> { idx: idx, value: v }) values
    result = foldl go { runningY: baseline, segments: [] } indexed
  in
    result.segments
