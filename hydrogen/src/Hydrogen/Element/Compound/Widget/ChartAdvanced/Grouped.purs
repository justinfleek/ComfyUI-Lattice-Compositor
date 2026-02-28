-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // element // widget // chart-advanced // grouped
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Grouped Bar Chart — Multiple bars per category for comparison.
-- |
-- | ## Design Philosophy
-- |
-- | A grouped bar chart displays multiple series side-by-side within each
-- | category. Each category has one bar per series, making it easy to compare
-- | values across series within each category.
-- |
-- | Common uses:
-- | - Comparing metrics across different products/regions
-- | - Year-over-year comparisons by month
-- | - A/B test results with multiple variants
-- |
-- | Pure Element output — no framework dependencies.

module Hydrogen.Element.Compound.Widget.ChartAdvanced.Grouped
  ( -- * Types
    GroupedBarData
  , GroupedBarConfig
  
  -- * Defaults
  , defaultGroupedBarConfig
  
  -- * Rendering
  , groupedBarChart
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (==)
  , (<>)
  , (<=)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Array (foldl, index, length, mapWithIndex)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Hydrogen.Element.Compound.Widget.Chart.Helpers (arrayMin, arrayMax)
import Hydrogen.Math.Core as Math
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grouped bar chart data.
-- |
-- | Each category has multiple values (one per series).
type GroupedBarData =
  { category :: String
  , values :: Array Number  -- ^ One value per series
  }

-- | Grouped bar chart configuration.
type GroupedBarConfig =
  { title :: Maybe String
  , width :: Number
  , height :: Number
  , seriesNames :: Array String
  , seriesColors :: Array String
  , horizontal :: Boolean
  , className :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default grouped bar configuration.
defaultGroupedBarConfig :: GroupedBarConfig
defaultGroupedBarConfig =
  { title: Nothing
  , width: 400.0
  , height: 200.0
  , seriesNames: []
  , seriesColors: ["#3B82F6", "#22C55E", "#FBBF24", "#8B5CF6", "#F43F5E"]
  , horizontal: false
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a grouped bar chart.
-- |
-- | Multiple bars per category, side by side for comparison.
groupedBarChart :: forall msg. GroupedBarConfig -> Array GroupedBarData -> E.Element msg
groupedBarChart cfg dataPoints =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    padding = 40.0
    plotWidth = cfg.width - padding * 2.0
    plotHeight = cfg.height - padding * 2.0
    
    numCategories = length dataPoints
    numSeries = case index dataPoints 0 of
      Nothing -> 0
      Just d -> length d.values
    
    -- Calculate dimensions
    categoryWidth = if numCategories <= 0 then 50.0 else plotWidth / toNumber numCategories
    barWidth = if numSeries <= 0 then 20.0 else (categoryWidth * 0.8) / toNumber numSeries
    
    -- Get value range
    allValues = foldl (\acc d -> acc <> d.values) [] dataPoints
    maxVal = arrayMax allValues
    minVal = Math.min 0.0 (arrayMin allValues)  -- Include 0 in range
    range = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
    
    scaleY :: Number -> Number
    scaleY v = padding + plotHeight - ((v - minVal) / range) * plotHeight
    
    baseline = scaleY 0.0
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ ("w-full h-full " <> cfg.className)
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      [ -- Baseline
        E.line_
          [ E.attr "x1" (show padding)
          , E.attr "y1" (show baseline)
          , E.attr "x2" (show (cfg.width - padding))
          , E.attr "y2" (show baseline)
          , E.attr "stroke" "currentColor"
          , E.attr "stroke-opacity" "0.2"
          ]
      -- Category groups
      , E.g_
          [ E.class_ "grouped-bars" ]
          (mapWithIndex (renderCategoryGroup cfg padding categoryWidth barWidth scaleY baseline) dataPoints)
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single category group with multiple bars.
renderCategoryGroup :: forall msg.
  GroupedBarConfig ->
  Number ->
  Number ->
  Number ->
  (Number -> Number) ->
  Number ->
  Int ->
  GroupedBarData ->
  E.Element msg
renderCategoryGroup cfg padding categoryWidth barWidth scaleY baseline catIdx catData =
  let
    catX = padding + toNumber catIdx * categoryWidth + categoryWidth * 0.1
  in
    E.g_
      []
      ([ -- Category label
         E.text_
           [ E.attr "x" (show (catX + categoryWidth * 0.4))
           , E.attr "y" (show (cfg.height - 10.0))
           , E.attr "text-anchor" "middle"
           , E.attr "font-size" "10"
           , E.attr "fill" "currentColor"
           , E.attr "fill-opacity" "0.7"
           ]
           [ E.text catData.category ]
       ] <> mapWithIndex (renderGroupedBar cfg catX barWidth scaleY baseline) catData.values)

-- | Render a single bar within a group.
renderGroupedBar :: forall msg.
  GroupedBarConfig ->
  Number ->
  Number ->
  (Number -> Number) ->
  Number ->
  Int ->
  Number ->
  E.Element msg
renderGroupedBar cfg catX barWidth scaleY baseline seriesIdx value =
  let
    x = catX + toNumber seriesIdx * barWidth
    yTop = scaleY value
    barHeight = baseline - yTop
    color = fromMaybe "#3B82F6" (index cfg.seriesColors seriesIdx)
  in
    E.rect_
      [ E.attr "x" (show x)
      , E.attr "y" (show (if value > 0.0 then yTop else baseline))
      , E.attr "width" (show (barWidth * 0.9))
      , E.attr "height" (show (Math.abs barHeight))
      , E.attr "fill" color
      , E.attr "rx" "2"
      , E.style "filter" ("drop-shadow(0 0 8px " <> color <> "60)")
      ]
