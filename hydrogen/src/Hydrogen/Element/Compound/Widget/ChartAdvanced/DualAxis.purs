-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // element // widget // chart-advanced // dual-axis
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dual Axis Chart — Line + Column on same chart with two Y-axes.
-- |
-- | ## Design Philosophy
-- |
-- | A dual axis chart combines a line chart and column chart on the same
-- | visualization, with each using its own Y-axis scale. This allows
-- | comparison of two metrics with different units or magnitudes.
-- |
-- | Common uses:
-- | - Revenue (columns) vs Growth Rate (line)
-- | - Temperature (line) vs Precipitation (columns)
-- | - Sales Volume (columns) vs Conversion Rate (line)
-- |
-- | Pure Element output — no framework dependencies.

module Hydrogen.Element.Compound.Widget.ChartAdvanced.DualAxis
  ( -- * Types
    DualAxisData
  , DualAxisConfig
  
  -- * Defaults
  , defaultDualAxisConfig
  
  -- * Rendering
  , dualAxisChart
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

import Data.Array (foldl, length, mapWithIndex)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing))
import Hydrogen.Element.Compound.Widget.Chart.Helpers (arrayMin, arrayMax)
import Hydrogen.Math.Core as Math
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dual axis chart data.
-- |
-- | Shows line data on primary Y-axis and column data on secondary Y-axis.
type DualAxisData =
  { categories :: Array String
  , lineSeries :: Array Number   -- ^ Values for line (primary Y-axis)
  , columnSeries :: Array Number -- ^ Values for columns (secondary Y-axis)
  , lineLabel :: String
  , columnLabel :: String
  }

-- | Dual axis chart configuration.
type DualAxisConfig =
  { title :: Maybe String
  , width :: Number
  , height :: Number
  , lineColor :: String
  , columnColor :: String
  , className :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default dual axis configuration.
defaultDualAxisConfig :: DualAxisConfig
defaultDualAxisConfig =
  { title: Nothing
  , width: 400.0
  , height: 200.0
  , lineColor: "#3B82F6"   -- Blue
  , columnColor: "#22C55E" -- Green
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a dual axis chart (line + column).
-- |
-- | Combines line chart and column chart on same axes.
dualAxisChart :: forall msg. DualAxisConfig -> DualAxisData -> E.Element msg
dualAxisChart cfg ddata =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    padding = 50.0
    plotWidth = cfg.width - padding * 2.0
    plotHeight = cfg.height - padding * 2.0
    
    numPoints = length ddata.categories
    columnWidth = if numPoints <= 0 then 20.0 else (plotWidth / toNumber numPoints) * 0.6
    
    -- Scale for columns
    maxColumn = arrayMax ddata.columnSeries
    scaleColumn :: Number -> Number
    scaleColumn v = if maxColumn == 0.0 then 0.0 else (v / maxColumn) * plotHeight
    
    -- Scale for line
    maxLine = arrayMax ddata.lineSeries
    minLine = arrayMin ddata.lineSeries
    lineRange = if maxLine - minLine == 0.0 then 1.0 else maxLine - minLine
    scaleLine :: Number -> Number
    scaleLine v = padding + plotHeight - ((v - minLine) / lineRange) * plotHeight
    
    baseline = padding + plotHeight
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ ("w-full h-full " <> cfg.className)
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      [ -- Columns (render first, behind line)
        E.g_
          [ E.class_ "dual-columns" ]
          (mapWithIndex (renderDualColumn cfg padding columnWidth plotWidth baseline scaleColumn numPoints) ddata.columnSeries)
      
      -- Line
      , E.path_
          [ E.attr "d" (generateDualLinePath padding plotWidth scaleLine numPoints ddata.lineSeries)
          , E.attr "fill" "none"
          , E.attr "stroke" cfg.lineColor
          , E.attr "stroke-width" "2"
          , E.style "filter" ("drop-shadow(0 0 6px " <> cfg.lineColor <> "80)")
          ]
      
      -- Line points
      , E.g_
          [ E.class_ "dual-line-points" ]
          (mapWithIndex (renderDualLinePoint cfg padding plotWidth scaleLine numPoints) ddata.lineSeries)
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a column in dual axis chart.
renderDualColumn :: forall msg.
  DualAxisConfig ->
  Number ->
  Number ->
  Number ->
  Number ->
  (Number -> Number) ->
  Int ->
  Int ->
  Number ->
  E.Element msg
renderDualColumn cfg padding columnWidth plotWidth baseline scaleColumn numPoints idx value =
  let
    divisor = Math.max 1.0 (toNumber (numPoints - 1))
    x = padding + (toNumber idx / divisor) * plotWidth - columnWidth / 2.0
    height = scaleColumn value
    y = baseline - height
  in
    E.rect_
      [ E.attr "x" (show x)
      , E.attr "y" (show y)
      , E.attr "width" (show columnWidth)
      , E.attr "height" (show height)
      , E.attr "fill" cfg.columnColor
      , E.attr "fill-opacity" "0.7"
      , E.attr "rx" "2"
      , E.style "filter" ("drop-shadow(0 0 6px " <> cfg.columnColor <> "40)")
      ]

-- | Generate path data for dual axis line.
generateDualLinePath :: Number -> Number -> (Number -> Number) -> Int -> Array Number -> String
generateDualLinePath padding plotWidth scaleLine numPoints values =
  let
    divisor = Math.max 1.0 (toNumber (numPoints - 1))
    pathParts = mapWithIndex (\idx v ->
      let 
        x = padding + (toNumber idx / divisor) * plotWidth
        y = scaleLine v
      in 
        if idx == 0
          then "M " <> show x <> " " <> show y
          else "L " <> show x <> " " <> show y
    ) values
  in
    foldl (\acc part -> acc <> " " <> part) "" pathParts

-- | Render a point on the dual axis line.
renderDualLinePoint :: forall msg.
  DualAxisConfig ->
  Number ->
  Number ->
  (Number -> Number) ->
  Int ->
  Int ->
  Number ->
  E.Element msg
renderDualLinePoint cfg padding plotWidth scaleLine numPoints idx value =
  let
    divisor = Math.max 1.0 (toNumber (numPoints - 1))
    x = padding + (toNumber idx / divisor) * plotWidth
    y = scaleLine value
  in
    E.circle_
      [ E.attr "cx" (show x)
      , E.attr "cy" (show y)
      , E.attr "r" "4"
      , E.attr "fill" cfg.lineColor
      , E.style "filter" ("drop-shadow(0 0 4px " <> cfg.lineColor <> "80)")
      ]
