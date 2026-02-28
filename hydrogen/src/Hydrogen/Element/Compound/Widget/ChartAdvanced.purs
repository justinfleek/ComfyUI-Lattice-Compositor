-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // widget // chart-advanced
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Advanced Chart Types — Waterfall, Grouped, Stacked, Rainfall, DualAxis.
-- |
-- | ## Design Philosophy
-- |
-- | These chart types extend the base Chart module with more complex
-- | visualizations commonly seen in business dashboards and KPI widgets.
-- |
-- | Implements chart types from COMPASS bento reference PNGs:
-- | - Waterfall: Shows cumulative effect of sequential values
-- | - GroupedBar: Multiple bars per category for comparison
-- | - StackedBar/Column: Stacked segments showing composition
-- | - Rainfall: Dual distribution (bidirectional histogram)
-- | - DualAxis: Line + Column on same chart with two Y-axes
-- |
-- | Pure Element output — no framework dependencies.
-- |
-- | ## Module Structure
-- |
-- | - ChartAdvanced.Waterfall: Waterfall chart types and renderer
-- | - ChartAdvanced.Grouped: Grouped bar chart
-- | - ChartAdvanced.Stacked: Stacked bar/column charts
-- | - ChartAdvanced.Rainfall: Rainfall/distribution chart
-- | - ChartAdvanced.DualAxis: Dual axis chart (line + column)

module Hydrogen.Element.Compound.Widget.ChartAdvanced
  ( -- * Waterfall Chart (re-exported)
    module Waterfall
  
  -- * Grouped Bar Chart (re-exported)
  , module Grouped
  
  -- * Stacked Bar/Column Chart (re-exported)
  , module Stacked
  
  -- * Rainfall/Distribution Chart (re-exported)
  , module Rainfall
  
  -- * Dual Axis Chart (re-exported)
  , module DualAxis
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- Re-export from submodules using module aliases
import Hydrogen.Element.Compound.Widget.ChartAdvanced.Waterfall
  ( WaterfallData
  , WaterfallConfig
  , defaultWaterfallConfig
  , waterfallChart
  ) as Waterfall

import Hydrogen.Element.Compound.Widget.ChartAdvanced.Grouped
  ( GroupedBarData
  , GroupedBarConfig
  , defaultGroupedBarConfig
  , groupedBarChart
  ) as Grouped

import Hydrogen.Element.Compound.Widget.ChartAdvanced.Stacked
  ( StackedData
  , StackedConfig
  , defaultStackedConfig
  , stackedBarChart
  , stackedColumnChart
  ) as Stacked

import Hydrogen.Element.Compound.Widget.ChartAdvanced.Rainfall
  ( RainfallData
  , RainfallConfig
  , defaultRainfallConfig
  , rainfallChart
  ) as Rainfall

import Hydrogen.Element.Compound.Widget.ChartAdvanced.DualAxis
  ( DualAxisData
  , DualAxisConfig
  , defaultDualAxisConfig
  , dualAxisChart
  ) as DualAxis
