-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // element // widget // chart-advanced // waterfall
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Waterfall Chart — Shows cumulative effect of sequential values.
-- |
-- | ## Design Philosophy
-- |
-- | A waterfall chart displays how an initial value is affected by a series
-- | of positive or negative values. Each bar "floats" showing the running
-- | total, with positive values going up and negative values going down.
-- |
-- | Common uses:
-- | - Financial statements (revenue → expenses → profit)
-- | - Inventory tracking (starting → additions → subtractions → ending)
-- | - Project timelines with milestones
-- |
-- | Pure Element output — no framework dependencies.

module Hydrogen.Element.Compound.Widget.ChartAdvanced.Waterfall
  ( -- * Types
    WaterfallData
  , WaterfallConfig
  
  -- * Defaults
  , defaultWaterfallConfig
  
  -- * Rendering
  , waterfallChart
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

-- | Waterfall chart data point.
-- |
-- | Each bar shows the delta from the previous cumulative value.
-- | Positive values go up, negative values go down.
type WaterfallData =
  { label :: String
  , value :: Number       -- ^ Delta value (positive or negative)
  , isTotal :: Boolean    -- ^ If true, shows as total bar (different styling)
  }

-- | Waterfall chart configuration.
type WaterfallConfig =
  { title :: Maybe String
  , width :: Number
  , height :: Number
  , positiveColor :: String
  , negativeColor :: String
  , totalColor :: String
  , showConnectors :: Boolean
  , className :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default waterfall configuration.
defaultWaterfallConfig :: WaterfallConfig
defaultWaterfallConfig =
  { title: Nothing
  , width: 400.0
  , height: 200.0
  , positiveColor: "#22C55E"  -- Neon green
  , negativeColor: "#EF4444"  -- Neon red
  , totalColor: "#3B82F6"     -- Blue
  , showConnectors: true
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a waterfall chart.
-- |
-- | Shows cumulative effect of sequential positive/negative values.
-- | Bars float to show running total.
waterfallChart :: forall msg. WaterfallConfig -> Array WaterfallData -> E.Element msg
waterfallChart cfg dataPoints =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    padding = 40.0
    plotWidth = cfg.width - padding * 2.0
    plotHeight = cfg.height - padding * 2.0
    numBars = length dataPoints
    barWidth = if numBars <= 0 then 30.0 else (plotWidth / toNumber numBars) * 0.7
    barGap = if numBars <= 0 then 10.0 else (plotWidth / toNumber numBars) * 0.3
    
    -- Calculate cumulative values and range
    cumulativeValues = calculateCumulative dataPoints
    minVal = arrayMin cumulativeValues
    maxVal = arrayMax cumulativeValues
    range = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
    
    -- Scale Y value to plot coordinates
    scaleY :: Number -> Number
    scaleY v = padding + plotHeight - ((v - minVal) / range) * plotHeight
    
    baseline = scaleY 0.0
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ ("w-full h-full " <> cfg.className)
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      [ -- Axis
        E.line_
          [ E.attr "x1" (show padding)
          , E.attr "y1" (show baseline)
          , E.attr "x2" (show (cfg.width - padding))
          , E.attr "y2" (show baseline)
          , E.attr "stroke" "currentColor"
          , E.attr "stroke-opacity" "0.2"
          ]
      -- Bars
      , E.g_
          [ E.class_ "waterfall-bars" ]
          (mapWithIndex (renderWaterfallBar cfg padding barWidth barGap scaleY cumulativeValues) dataPoints)
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate cumulative values for waterfall.
calculateCumulative :: Array WaterfallData -> Array Number
calculateCumulative dataPoints =
  let
    go :: { running :: Number, values :: Array Number } -> WaterfallData -> { running :: Number, values :: Array Number }
    go acc d =
      if d.isTotal
        then { running: d.value, values: acc.values <> [d.value] }
        else 
          let newRunning = acc.running + d.value
          in { running: newRunning, values: acc.values <> [newRunning] }
    
    result = foldl go { running: 0.0, values: [] } dataPoints
  in
    result.values

-- | Render a single waterfall bar.
renderWaterfallBar :: forall msg. 
  WaterfallConfig -> 
  Number -> 
  Number -> 
  Number -> 
  (Number -> Number) -> 
  Array Number -> 
  Int -> 
  WaterfallData -> 
  E.Element msg
renderWaterfallBar cfg padding barWidth barGap scaleY cumulatives idx d =
  let
    x = padding + toNumber idx * (barWidth + barGap) + barGap / 2.0
    
    -- Get cumulative before and after
    prevCumulative = if idx == 0 then 0.0 else fromMaybe 0.0 (index cumulatives (idx - 1))
    currCumulative = fromMaybe 0.0 (index cumulatives idx)
    
    -- Bar position
    yTop = scaleY (Math.max prevCumulative currCumulative)
    yBottom = scaleY (Math.min prevCumulative currCumulative)
    barHeight = yBottom - yTop
    
    -- Color based on positive/negative/total
    color = if d.isTotal 
            then cfg.totalColor
            else if d.value > 0.0 then cfg.positiveColor else cfg.negativeColor
  in
    E.g_
      []
      [ -- Bar with glow
        E.rect_
          [ E.attr "x" (show x)
          , E.attr "y" (show yTop)
          , E.attr "width" (show barWidth)
          , E.attr "height" (show (Math.max 1.0 barHeight))
          , E.attr "fill" color
          , E.attr "rx" "2"
          , E.style "filter" ("drop-shadow(0 0 6px " <> color <> "80)")
          ]
      -- Label
      , E.text_
          [ E.attr "x" (show (x + barWidth / 2.0))
          , E.attr "y" (show (cfg.height - 10.0))
          , E.attr "text-anchor" "middle"
          , E.attr "font-size" "10"
          , E.attr "fill" "currentColor"
          , E.attr "fill-opacity" "0.7"
          ]
          [ E.text d.label ]
      ]
