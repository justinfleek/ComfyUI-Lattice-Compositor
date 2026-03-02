{-|
  Lattice.Services.SVGExtrusion.CapProfile - Cap Profile Mathematics

  Pure mathematical functions for generating cap profile curves:
  - Fillet (quarter-circle) profile
  - Convex (outward bulging) profile
  - Concave (inward scooped) profile
  - Stepped (terraced) profile

  These profiles define the edge shape for 3D extrusion caps,
  similar to Cinema 4D/Blender fillet caps.

  Source: ui/src/services/svgExtrusion.ts (lines 166-251)
-}

module Lattice.Services.SVGExtrusion.CapProfile
  ( -- * Types
    Point2D(..)
  , CapProfileType(..)
    -- * Profile Generation
  , flatProfile
  , filletProfile
  , convexProfile
  , concaveProfile
  , stepsProfile
  , scaleCustomProfile
  , generateCapProfile
    -- * Utilities
  , requiresCurveGeneration
  , minSegmentsFor
  , clampSegments
  ) where

import Data.Vector (Vector)
import qualified Data.Vector as V

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D point for profile curves
data Point2D = Point2D
  { pointX :: !Double
  , pointY :: !Double
  } deriving (Show, Eq)

-- | Cap profile type
data CapProfileType
  = Flat      -- ^ Standard flat cap (no rounding)
  | Fillet    -- ^ Quarter-circle rounded edge
  | Convex    -- ^ Outward bulging profile
  | Concave   -- ^ Inward scooped profile
  | Steps     -- ^ Stepped/terraced profile
  | Custom    -- ^ Custom profile curve
  deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Flat Profile
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate flat cap profile (just start and end points).
flatProfile :: Double -> Vector Point2D
flatProfile depth = V.fromList
  [ Point2D 0.0 0.0
  , Point2D 0.0 depth
  ]

-- ────────────────────────────────────────────────────────────────────────────
-- Fillet Profile
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate quarter-circle fillet profile.
--
--   Creates a smooth rounded edge transition.
filletProfile :: Double -> Double -> Int -> Vector Point2D
filletProfile radius depth segments = V.generate (segments + 1) mkPoint
  where
    mkPoint i =
      let t = fromIntegral i / fromIntegral segments
          angle = (pi / 2.0) * t
          x = radius * (1.0 - cos angle)
          y = depth * sin angle
      in Point2D x y

-- ────────────────────────────────────────────────────────────────────────────
-- Convex Profile
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate convex (outward bulging) profile.
--
--   Uses sine curve to create outward bulge.
convexProfile :: Double -> Double -> Int -> Vector Point2D
convexProfile radius depth segments = V.generate (segments + 1) mkPoint
  where
    mkPoint i =
      let t = fromIntegral i / fromIntegral segments
          -- Bulge outward using sine curve
          bulge = sin (pi * t) * radius * 0.5
          x = negate bulge  -- Negative = outward
          y = depth * t
      in Point2D x y

-- ────────────────────────────────────────────────────────────────────────────
-- Concave Profile
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate concave (inward scooped) profile.
--
--   Uses parabolic/sine curve to create inward scoop.
concaveProfile :: Double -> Double -> Int -> Vector Point2D
concaveProfile radius depth segments = V.generate (segments + 1) mkPoint
  where
    mkPoint i =
      let t = fromIntegral i / fromIntegral segments
          -- Scoop inward using sine curve
          scoop = sin (pi * t) * radius
          x = scoop  -- Positive = inward
          y = depth * t
      in Point2D x y

-- ────────────────────────────────────────────────────────────────────────────
-- Steps Profile
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate stepped/terraced profile.
--
--   Creates a staircase-like profile with flat steps and vertical risers.
stepsProfile :: Double -> Double -> Int -> Vector Point2D
stepsProfile radius depth segments = V.fromList (buildSteps 0 [])
  where
    stepCount = max 2 (segments `div` 2)
    stepHeight = depth / fromIntegral stepCount
    stepWidth = radius / fromIntegral stepCount

    buildSteps :: Int -> [Point2D] -> [Point2D]
    buildSteps i acc
      | i > stepCount = reverse acc
      | otherwise =
          let iFloat = fromIntegral i
              stepPt = Point2D (iFloat * stepWidth) (iFloat * stepHeight)
              acc' = stepPt : acc
          in if i < stepCount
             then let riserPt = Point2D (iFloat * stepWidth) ((iFloat + 1.0) * stepHeight)
                  in buildSteps (i + 1) (riserPt : acc')
             else buildSteps (i + 1) acc'

-- ────────────────────────────────────────────────────────────────────────────
-- Custom Profile
-- ────────────────────────────────────────────────────────────────────────────

-- | Scale custom profile points to the desired radius and depth.
scaleCustomProfile :: Vector Point2D -> Double -> Double -> Vector Point2D
scaleCustomProfile customPoints radius depth =
  V.map (\p -> Point2D (pointX p * radius) (pointY p * depth)) customPoints

-- ────────────────────────────────────────────────────────────────────────────
-- Profile Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate cap profile curve based on type.
generateCapProfile
  :: CapProfileType
  -> Double           -- ^ Profile radius (horizontal extent)
  -> Double           -- ^ Profile depth (vertical extent)
  -> Int              -- ^ Number of segments for curved profiles
  -> Maybe (Vector Point2D)  -- ^ Optional custom profile
  -> Vector Point2D
generateCapProfile profileType radius depth segments customProfile =
  case profileType of
    Flat -> flatProfile depth
    Fillet -> filletProfile radius depth segments
    Convex -> convexProfile radius depth segments
    Concave -> concaveProfile radius depth segments
    Steps -> stepsProfile radius depth segments
    Custom -> case customProfile of
      Just pts | V.length pts >= 2 -> scaleCustomProfile pts radius depth
      _ -> filletProfile radius depth segments  -- Fallback

-- ────────────────────────────────────────────────────────────────────────────
-- Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if profile type requires curve generation.
requiresCurveGeneration :: CapProfileType -> Bool
requiresCurveGeneration Flat = False
requiresCurveGeneration _ = True

-- | Get minimum segments for a profile type.
minSegmentsFor :: CapProfileType -> Int
minSegmentsFor Flat = 1
minSegmentsFor Fillet = 4
minSegmentsFor Convex = 4
minSegmentsFor Concave = 4
minSegmentsFor Steps = 4
minSegmentsFor Custom = 2

-- | Clamp segments to valid range.
clampSegments :: Int -> CapProfileType -> Int
clampSegments segments profileType =
  let minSeg = minSegmentsFor profileType
  in max minSeg (min 32 segments)
