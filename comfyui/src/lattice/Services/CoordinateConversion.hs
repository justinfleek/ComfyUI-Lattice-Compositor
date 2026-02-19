-- |
-- Module      : Lattice.Services.CoordinateConversion
-- Description : Pure coordinate conversion functions for geometric transformations
-- 
-- Migrated from ui/src/services/expressions/coordinateConversion.ts
-- Pure geometric calculations for coordinate space conversions
-- Note: Parent transform recursion handled separately (requires context)
--

module Lattice.Services.CoordinateConversion
  ( -- 3D orientation
    lookAt
  , orientToPathFromTangent
  -- Transform data types
  , LayerTransform(..)
  -- Coordinate conversion (pure math, no parent recursion)
  , toCompLocal
  , fromCompLocal
  , toWorldLocal
  , fromWorldLocal
  ) where

import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Utils.NumericSafety
  ( safeDivide
  , safeSqrt
  )
import Lattice.Utils.ArrayUtils (safeArrayGet)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Transform matrix for coordinate conversion
-- Note: Parent transform handled separately (not included here for purity)
data LayerTransform = LayerTransform
  { layerTransformPosition :: [Double]
  , layerTransformScale :: [Double]
  , layerTransformRotation :: [Double]
  , layerTransformAnchor :: [Double]
  } deriving (Eq, Show)

-- | Safe array element access with default
safeGet :: [Double] -> Int -> Double -> Double
safeGet arr idx defaultVal =
  let val = safeArrayGet arr idx defaultVal
  in if isFinite val then val else defaultVal

-- ════════════════════════════════════════════════════════════════════════════
-- 3D ORIENTATION FUNCTIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | Calculate rotation to face a target point
-- Pure function: same inputs → same outputs
-- Returns [xRotation, yRotation, zRotation] in degrees
lookAt :: [Double] -> [Double] -> [Double]
lookAt fromPoint toPoint =
  let dx = safeGet toPoint 0 0 - safeGet fromPoint 0 0
      dy = safeGet toPoint 1 0 - safeGet fromPoint 1 0
      dz = safeGet toPoint 2 0 - safeGet fromPoint 2 0
      -- Calculate yaw (Y rotation) and pitch (X rotation)
      yaw = atan2 dx dz * 180 / pi
      dist = safeSqrt (dx * dx + dz * dz) 0.0
      pitch = (-atan2 dy dist) * 180 / pi
  in [pitch, yaw, 0]

-- | Auto-orient layer along motion path using tangent vector
-- Pure function: same inputs → same outputs
-- Returns [xRotation, yRotation, zRotation] in degrees
orientToPathFromTangent :: [Double] -> [Double]
orientToPathFromTangent tangentVector =
  let dx = safeGet tangentVector 0 0
      dy = safeGet tangentVector 1 0
      dz = safeGet tangentVector 2 1  -- Default to 1 if missing
      yaw = atan2 dx dz * 180 / pi
      dist = safeSqrt (dx * dx + dz * dz) 0.0
      pitch = (-atan2 dy dist) * 180 / pi
  in [pitch, yaw, 0]

-- ════════════════════════════════════════════════════════════════════════════
--                                     // coordinate // conversion // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert point from layer space to composition space (local transform only)
-- Pure function: same inputs → same outputs
-- Does NOT handle parent transforms (caller must handle recursion)
toCompLocal :: [Double] -> LayerTransform -> [Double]
toCompLocal point transform =
  let px = safeGet point 0 0
      py = safeGet point 1 0
      pz = safeGet point 2 0
      position = layerTransformPosition transform
      scale = layerTransformScale transform
      rotation = layerTransformRotation transform
      anchor = layerTransformAnchor transform
      -- Apply anchor offset
      x0 = px - safeGet anchor 0 0
      y0 = py - safeGet anchor 1 0
      z0 = pz - safeGet anchor 2 0
      -- Apply scale (preserve intentional 0)
      sx = safeGet scale 0 100 / 100
      sy = safeGet scale 1 100 / 100
      sz = safeGet scale 2 100 / 100
      x1 = x0 * sx
      y1 = y0 * sy
      z1 = z0 * sz
      -- Apply rotation (Z, then Y, then X - matching AE order)
      rz = (safeGet rotation 2 (safeGet rotation 0 0)) * pi / 180
      ry = safeGet rotation 1 0 * pi / 180
      rx = safeGet rotation 0 0 * pi / 180
      -- Rotate around Z
      x2 = x1 * cos rz - y1 * sin rz
      y2 = x1 * sin rz + y1 * cos rz
      z2 = z1
      -- Rotate around Y (3D only)
      x3 = x2 * cos ry + z2 * sin ry
      y3 = y2
      z3 = -x2 * sin ry + z2 * cos ry
      -- Rotate around X (3D only)
      x4 = x3
      y4 = y3 * cos rx - z3 * sin rx
      z4 = y3 * sin rx + z3 * cos rx
      -- Apply position offset
      x5 = x4 + safeGet position 0 0
      y5 = y4 + safeGet position 1 0
      z5 = z4 + safeGet position 2 0
  in if length point == 2 then [x5, y5] else [x5, y5, z5]

-- | Convert point from composition space to layer space (local transform only)
-- Pure function: same inputs → same outputs
-- Does NOT handle parent transforms (caller must handle recursion)
fromCompLocal :: [Double] -> LayerTransform -> [Double]
fromCompLocal point transform =
  let px = safeGet point 0 0
      py = safeGet point 1 0
      pz = safeGet point 2 0
      position = layerTransformPosition transform
      scale = layerTransformScale transform
      rotation = layerTransformRotation transform
      anchor = layerTransformAnchor transform
      -- Subtract position
      x0 = px - safeGet position 0 0
      y0 = py - safeGet position 1 0
      z0 = pz - safeGet position 2 0
      -- Inverse rotation (X, then Y, then Z - reverse order)
      rx = (-safeGet rotation 0 0) * pi / 180
      ry = (-safeGet rotation 1 0) * pi / 180
      rz = (-safeGet rotation 2 (safeGet rotation 0 0)) * pi / 180
      -- Rotate around X (inverse)
      x1 = x0
      y1 = y0 * cos rx - z0 * sin rx
      z1 = y0 * sin rx + z0 * cos rx
      -- Rotate around Y (inverse)
      x2 = x1 * cos ry + z1 * sin ry
      y2 = y1
      z2 = -x1 * sin ry + z1 * cos ry
      -- Rotate around Z (inverse)
      x3 = x2 * cos rz - y2 * sin rz
      y3 = x2 * sin rz + y2 * cos rz
      z3 = z2
      -- Inverse scale (with division by zero protection)
      sx = safeGet scale 0 100 / 100
      sy = safeGet scale 1 100 / 100
      sz = safeGet scale 2 100 / 100
      x4 = safeDivide x3 sx x3  -- If sx === 0, return x3 unchanged
      y4 = safeDivide y3 sy y3  -- If sy === 0, return y3 unchanged
      z4 = safeDivide z3 sz z3  -- If sz === 0, return z3 unchanged
      -- Add anchor
      x5 = x4 + safeGet anchor 0 0
      y5 = y4 + safeGet anchor 1 0
      z5 = z4 + safeGet anchor 2 0
  in if length point == 2 then [x5, y5] else [x5, y5, z5]

-- | Convert point from layer space to world (3D) space (local transform only)
-- Pure function: same inputs → same outputs
-- Alias for toCompLocal in 3D context
toWorldLocal :: [Double] -> LayerTransform -> [Double]
toWorldLocal point transform =
  let point3D = if length point == 2 then point ++ [0] else point
  in toCompLocal point3D transform

-- | Convert point from world space to layer space (local transform only)
-- Pure function: same inputs → same outputs
-- Alias for fromCompLocal in 3D context
fromWorldLocal :: [Double] -> LayerTransform -> [Double]
fromWorldLocal point transform =
  let point3D = if length point == 2 then point ++ [0] else point
  in fromCompLocal point3D transform
