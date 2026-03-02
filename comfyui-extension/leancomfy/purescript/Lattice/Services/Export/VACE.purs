-- | Lattice.Services.Export.VACE - VACE control video export
-- |
-- | Generates control videos for VACE (Video Animation Control Engine) and
-- | similar motion-controllable video generation systems.
-- |
-- | Features:
-- | - Shapes following spline paths with arc-length parameterization
-- | - Speed calculated from pathLength / duration
-- | - White shapes on black background output
-- | - Multiple shape types and easing functions
-- |
-- | Source: ui/src/services/export/vaceControlExport.ts

module Lattice.Services.Export.VACE
  ( module Types
  , module Exporter
  ) where

import Lattice.Services.Export.VACE.Types as Types
import Lattice.Services.Export.VACE.Exporter as Exporter
