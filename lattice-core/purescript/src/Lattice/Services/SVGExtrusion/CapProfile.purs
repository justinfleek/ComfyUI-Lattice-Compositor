{-
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
  ( Point2D
  , CapProfileType(..)
  , flatProfile
  , filletProfile
  , convexProfile
  , concaveProfile
  , stepsProfile
  , scaleCustomProfile
  , generateCapProfile
  , requiresCurveGeneration
  , minSegmentsFor
  , clampSegments
  ) where

import Prelude

import Data.Array ((..), snoc)
import Data.Foldable (foldl)
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(..))
import Math (cos, sin, pi)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D point for profile curves
type Point2D = { x :: Number, y :: Number }

-- | Cap profile type
data CapProfileType
  = Flat      -- Standard flat cap (no rounding)
  | Fillet    -- Quarter-circle rounded edge
  | Convex    -- Outward bulging profile
  | Concave   -- Inward scooped profile
  | Steps     -- Stepped/terraced profile
  | Custom    -- Custom profile curve

derive instance eqCapProfileType :: Eq CapProfileType

-- ────────────────────────────────────────────────────────────────────────────
-- Flat Profile
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate flat cap profile (just start and end points).
flatProfile :: Number -> Array Point2D
flatProfile depth =
  [ { x: 0.0, y: 0.0 }
  , { x: 0.0, y: depth }
  ]

-- ────────────────────────────────────────────────────────────────────────────
-- Fillet Profile
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate quarter-circle fillet profile.
filletProfile :: Number -> Number -> Int -> Array Point2D
filletProfile radius depth segments =
  map mkPoint (0 .. segments)
  where
    mkPoint i =
      let t = Int.toNumber i / Int.toNumber segments
          angle = (pi / 2.0) * t
          x = radius * (1.0 - cos angle)
          y = depth * sin angle
      in { x, y }

-- ────────────────────────────────────────────────────────────────────────────
-- Convex Profile
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate convex (outward bulging) profile.
convexProfile :: Number -> Number -> Int -> Array Point2D
convexProfile radius depth segments =
  map mkPoint (0 .. segments)
  where
    mkPoint i =
      let t = Int.toNumber i / Int.toNumber segments
          bulge = sin (pi * t) * radius * 0.5
          x = negate bulge
          y = depth * t
      in { x, y }

-- ────────────────────────────────────────────────────────────────────────────
-- Concave Profile
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate concave (inward scooped) profile.
concaveProfile :: Number -> Number -> Int -> Array Point2D
concaveProfile radius depth segments =
  map mkPoint (0 .. segments)
  where
    mkPoint i =
      let t = Int.toNumber i / Int.toNumber segments
          scoop = sin (pi * t) * radius
          x = scoop
          y = depth * t
      in { x, y }

-- ────────────────────────────────────────────────────────────────────────────
-- Steps Profile
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate stepped/terraced profile.
stepsProfile :: Number -> Number -> Int -> Array Point2D
stepsProfile radius depth segments =
  let stepCount = max 2 (segments / 2)
      stepHeight = depth / Int.toNumber stepCount
      stepWidth = radius / Int.toNumber stepCount

      buildSteps :: Int -> Array Point2D -> Array Point2D
      buildSteps i acc
        | i > stepCount = acc
        | otherwise =
            let iFloat = Int.toNumber i
                stepPt = { x: iFloat * stepWidth, y: iFloat * stepHeight }
                acc' = snoc acc stepPt
            in if i < stepCount
               then let riserPt = { x: iFloat * stepWidth, y: (iFloat + 1.0) * stepHeight }
                    in buildSteps (i + 1) (snoc acc' riserPt)
               else buildSteps (i + 1) acc'
  in buildSteps 0 []

-- ────────────────────────────────────────────────────────────────────────────
-- Custom Profile
-- ────────────────────────────────────────────────────────────────────────────

-- | Scale custom profile points to the desired radius and depth.
scaleCustomProfile :: Array Point2D -> Number -> Number -> Array Point2D
scaleCustomProfile customPoints radius depth =
  map (\p -> { x: p.x * radius, y: p.y * depth }) customPoints

-- ────────────────────────────────────────────────────────────────────────────
-- Profile Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate cap profile curve based on type.
generateCapProfile
  :: CapProfileType
  -> Number
  -> Number
  -> Int
  -> Maybe (Array Point2D)
  -> Array Point2D
generateCapProfile profileType radius depth segments customProfile =
  case profileType of
    Flat -> flatProfile depth
    Fillet -> filletProfile radius depth segments
    Convex -> convexProfile radius depth segments
    Concave -> concaveProfile radius depth segments
    Steps -> stepsProfile radius depth segments
    Custom -> case customProfile of
      Just pts | length pts >= 2 -> scaleCustomProfile pts radius depth
      _ -> filletProfile radius depth segments

  where
    length :: forall a. Array a -> Int
    length arr = foldl (\acc _ -> acc + 1) 0 arr

-- ────────────────────────────────────────────────────────────────────────────
-- Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if profile type requires curve generation.
requiresCurveGeneration :: CapProfileType -> Boolean
requiresCurveGeneration Flat = false
requiresCurveGeneration _ = true

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
