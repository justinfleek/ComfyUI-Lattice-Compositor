-- |
-- Module      : Lattice.Types.PrecisionLimits
-- Description : Domain-specific precision limits and validation
-- 
--                                                                  // critical
-- - Physics forces: Lower precision (simulation tolerance)
-- - 3D coordinates: High precision (exact positioning)
-- - Data visualization: Medium precision (human-readable)
-- - UI display: Lower precision (pixel-aligned)
--
-- All precision limits are enforced at validation boundaries.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Types.PrecisionLimits
  ( -- Precision domains
    PrecisionDomain(..)
  -- Precision limits per domain
  , getPrecisionDecimals
  , getPrecisionEpsilon
  -- Validation functions
  , validatePrecision
  , normalizePrecision
  -- Constants
  , precisionPhysicsForces
  , precision3DCoordinates
  , precisionDataVisualization
  , precisionUIDisplay
  , precisionExportFormats
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Primitives (validateFinite)
import Lattice.Utils.NumericSafety (roundTo)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // precision // domains
-- ════════════════════════════════════════════════════════════════════════════

-- | Precision domain classification
-- Each domain has different precision requirements based on use case
data PrecisionDomain
  = PrecisionPhysicsForces      -- Forces, velocities, accelerations (simulation tolerance)
  | Precision3DCoordinates      -- Exact 3D positions, z-depth (high precision)
  | PrecisionDataVisualization  -- Chart data, statistics (human-readable)
  | PrecisionUIDisplay          -- UI sliders, pixel positions (pixel-aligned)
  | PrecisionExportFormats      -- Export to external formats (format-dependent)
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // precision // limits
-- ════════════════════════════════════════════════════════════════════════════

-- | Get maximum decimal places for a domain
-- Returns: Maximum decimal places allowed (values beyond this are rounded)
getPrecisionDecimals :: PrecisionDomain -> Int
getPrecisionDecimals domain = case domain of
  PrecisionPhysicsForces -> 3      -- Forces: 0.001 precision (milli-units)
  Precision3DCoordinates -> 6      -- 3D coords: 0.000001 precision (micrometer-level)
  PrecisionDataVisualization -> 2 -- Charts: 0.01 precision (human-readable)
  PrecisionUIDisplay -> 1         -- UI: 0.1 precision (pixel-aligned)
  PrecisionExportFormats -> 4     -- Export: 0.0001 precision (format-dependent)

-- | Get epsilon (tolerance) for approximate comparisons
-- Returns: Maximum difference considered "equal" for this domain
getPrecisionEpsilon :: PrecisionDomain -> Double
getPrecisionEpsilon domain = case domain of
  PrecisionPhysicsForces -> 0.001      -- 1 milli-unit tolerance
  Precision3DCoordinates -> 0.000001  -- 1 micrometer tolerance
  PrecisionDataVisualization -> 0.01   -- 1 cent tolerance
  PrecisionUIDisplay -> 0.1            -- 1 pixel tolerance
  PrecisionExportFormats -> 0.0001    -- Format-dependent tolerance

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // precision // constants
-- ════════════════════════════════════════════════════════════════════════════

-- | Physics forces precision: 3 decimal places (0.001)
-- Use for: Force magnitudes, velocities, accelerations, particle forces
precisionPhysicsForces :: Int
precisionPhysicsForces = 3

-- | 3D coordinates precision: 6 decimal places (0.000001)
-- Use for: Position.x/y/z, rotation angles, z-depth, camera positions
precision3DCoordinates :: Int
precision3DCoordinates = 6

-- | Data visualization precision: 2 decimal places (0.01)
-- Use for: Chart data points, statistics, percentages, data asset values
precisionDataVisualization :: Int
precisionDataVisualization = 2

-- | UI display precision: 1 decimal place (0.1)
-- Use for: Slider values, pixel positions, UI coordinates
precisionUIDisplay :: Int
precisionUIDisplay = 1

-- | Export formats precision: 4 decimal places (0.0001)
-- Use for: Export to external formats (ComfyUI, MotionCtrl, etc.)
precisionExportFormats :: Int
precisionExportFormats = 4

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // validation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Validate that a value has acceptable precision for a domain
-- Returns: True if value is within precision limits, False otherwise
-- Note: This checks if the value has MORE precision than allowed (should be normalized)
validatePrecision :: PrecisionDomain -> Double -> Bool
validatePrecision domain value =
  if not (validateFinite value)
    then False
    else
      let
        decimals = getPrecisionDecimals domain
        normalized = normalizePrecision domain value
        -- Check if normalization changed the value significantly
        epsilon = getPrecisionEpsilon domain
        diff = abs (value - normalized)
      in
        diff < epsilon

-- | Normalize a value to the precision required for a domain
-- Returns: Value rounded to appropriate decimal places
normalizePrecision :: PrecisionDomain -> Double -> Double
normalizePrecision domain value =
  if not (validateFinite value)
    then 0.0  -- Invalid values default to 0
    else
      let
        decimals = getPrecisionDecimals domain
      in
        roundTo value decimals

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // domain
-- ════════════════════════════════════════════════════════════════════════════

-- | Validate physics force value (3 decimal places)
validatePhysicsForce :: Double -> Either Text Double
validatePhysicsForce value =
  if not (validateFinite value)
    then Left "Physics force must be finite"
    else
      let normalized = normalizePrecision PrecisionPhysicsForces value
      in Right normalized

-- | Validate 3D coordinate value (6 decimal places)
validate3DCoordinate :: Double -> Either Text Double
validate3DCoordinate value =
  if not (validateFinite value)
    then Left "3D coordinate must be finite"
    else
      let normalized = normalizePrecision Precision3DCoordinates value
      in Right normalized

-- | Validate data visualization value (2 decimal places)
validateDataVisualization :: Double -> Either Text Double
validateDataVisualization value =
  if not (validateFinite value)
    then Left "Data visualization value must be finite"
    else
      let normalized = normalizePrecision PrecisionDataVisualization value
      in Right normalized

-- | Validate UI display value (1 decimal place)
validateUIDisplay :: Double -> Either Text Double
validateUIDisplay value =
  if not (validateFinite value)
    then Left "UI display value must be finite"
    else
      let normalized = normalizePrecision PrecisionUIDisplay value
      in Right normalized

-- | Validate export format value (4 decimal places)
validateExportFormat :: Double -> Either Text Double
validateExportFormat value =
  if not (validateFinite value)
    then Left "Export format value must be finite"
    else
      let normalized = normalizePrecision PrecisionExportFormats value
      in Right normalized
