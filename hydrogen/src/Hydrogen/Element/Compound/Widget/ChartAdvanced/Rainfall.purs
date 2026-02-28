-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // element // widget // chart-advanced // rainfall
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Rainfall Chart — Dual distribution visualization.
-- |
-- | ## Design Philosophy
-- |
-- | A rainfall chart shows two distributions meeting at a center axis.
-- | Lines extend left and right from the center, with length proportional
-- | to the values. Creates a distinctive "rainfall" visual pattern.
-- |
-- | Common uses:
-- | - Monthly vs yearly comparisons
-- | - Before/after distributions
-- | - Bidirectional histograms
-- | - Population pyramids (age distribution)
-- |
-- | Pure Element output — no framework dependencies.

module Hydrogen.Element.Compound.Widget.ChartAdvanced.Rainfall
  ( -- * Types
    RainfallData
  , RainfallConfig
  
  -- * Defaults
  , defaultRainfallConfig
  
  -- * Rendering
  , rainfallChart
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (==)
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Array (length, mapWithIndex)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing))
import Hydrogen.Element.Compound.Widget.Chart.Helpers (arrayMax)
import Hydrogen.Math.Core as Math
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rainfall/distribution chart data.
-- |
-- | Shows two distributions (left and right) meeting at center.
type RainfallData =
  { leftValues :: Array Number   -- ^ Left distribution (e.g., Monthly)
  , rightValues :: Array Number  -- ^ Right distribution (e.g., Yearly)
  , leftLabel :: String
  , rightLabel :: String
  }

-- | Rainfall chart configuration.
type RainfallConfig =
  { title :: Maybe String
  , width :: Number
  , height :: Number
  , leftColor :: String
  , rightColor :: String
  , className :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default rainfall configuration.
defaultRainfallConfig :: RainfallConfig
defaultRainfallConfig =
  { title: Nothing
  , width: 400.0
  , height: 200.0
  , leftColor: "#FBBF24"   -- Yellow/amber
  , rightColor: "#8B5CF6"  -- Purple
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a rainfall/distribution chart.
-- |
-- | Shows two distributions as fine lines tapering to/from center.
rainfallChart :: forall msg. RainfallConfig -> RainfallData -> E.Element msg
rainfallChart cfg rdata =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    padding = 20.0
    centerX = cfg.width / 2.0
    plotHeight = cfg.height - padding * 2.0
    halfWidth = (cfg.width - padding * 2.0) / 2.0
    
    numLeftLines = length rdata.leftValues
    numRightLines = length rdata.rightValues
    
    maxLeft = arrayMax rdata.leftValues
    maxRight = arrayMax rdata.rightValues
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ ("w-full h-full " <> cfg.className)
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      [ -- Left distribution (grows left from center)
        E.g_
          [ E.class_ "rainfall-left" ]
          (mapWithIndex (renderRainfallLine cfg.leftColor centerX halfWidth plotHeight padding numLeftLines maxLeft true) rdata.leftValues)
      
      -- Right distribution (grows right from center)
      , E.g_
          [ E.class_ "rainfall-right" ]
          (mapWithIndex (renderRainfallLine cfg.rightColor centerX halfWidth plotHeight padding numRightLines maxRight false) rdata.rightValues)
      
      -- Labels
      , E.text_
          [ E.attr "x" (show (padding + 10.0))
          , E.attr "y" (show (cfg.height - 5.0))
          , E.attr "font-size" "10"
          , E.attr "fill" cfg.leftColor
          ]
          [ E.text rdata.leftLabel ]
      , E.text_
          [ E.attr "x" (show (cfg.width - padding - 10.0))
          , E.attr "y" (show (cfg.height - 5.0))
          , E.attr "text-anchor" "end"
          , E.attr "font-size" "10"
          , E.attr "fill" cfg.rightColor
          ]
          [ E.text rdata.rightLabel ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single rainfall distribution line.
renderRainfallLine :: forall msg.
  String ->
  Number ->
  Number ->
  Number ->
  Number ->
  Int ->
  Number ->
  Boolean ->
  Int ->
  Number ->
  E.Element msg
renderRainfallLine color centerX halfWidth plotHeight padding numLines maxVal isLeft idx value =
  let
    -- Y position distributed vertically
    divisor = Math.max 1.0 (toNumber (numLines - 1))
    y = padding + (toNumber idx / divisor) * plotHeight
    
    -- Line length based on value
    lineLength = if maxVal == 0.0 then 0.0 else (value / maxVal) * halfWidth
    
    -- X positions
    x1 = if isLeft then centerX else centerX
    x2 = if isLeft then centerX - lineLength else centerX + lineLength
  in
    E.line_
      [ E.attr "x1" (show x1)
      , E.attr "y1" (show y)
      , E.attr "x2" (show x2)
      , E.attr "y2" (show y)
      , E.attr "stroke" color
      , E.attr "stroke-width" "1.5"
      , E.attr "stroke-opacity" "0.7"
      , E.style "filter" ("drop-shadow(0 0 3px " <> color <> "60)")
      ]
