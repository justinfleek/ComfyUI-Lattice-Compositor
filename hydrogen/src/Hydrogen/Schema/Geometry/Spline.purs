-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // geometry // spline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spline — Catmull-Rom and B-Spline curves for smooth interpolation.
-- |
-- | This is the leader module that re-exports all Spline submodules.
-- |
-- | ## Submodules
-- |
-- | - Spline.Types: CatmullRomSpline, BSpline types and constructors
-- | - Spline.Segments: Segment counting and extraction
-- | - Spline.Evaluation: Point and tangent evaluation at parameter t
-- | - Spline.Conversion: Convert to Bezier curves
-- | - Spline.Geometry: Arc length and bounding box
-- | - Spline.Sampling: Sample points and tangents
-- | - Spline.Subspline: Extract portions of splines
-- | - Spline.Validation: Check spline validity
-- | - Spline.PointAccess: First/last control points
-- | - Spline.ArcLength: Arc length parameterization
-- | - Spline.Helpers: Internal math utilities
-- |
-- | ## Design Philosophy
-- |
-- | While Bezier curves define shape through control points (some off-curve),
-- | splines provide different tradeoffs:
-- |
-- | - **Catmull-Rom**: Interpolating spline that passes through ALL control points.
-- |   Perfect for smooth paths through waypoints, camera motion, character animation.
-- |
-- | - **B-Spline**: Approximating spline with local control. Moving one point
-- |   only affects nearby curve segments. Ideal for modeling and design work.

module Hydrogen.Schema.Geometry.Spline
  ( -- * Re-exports from Types
    module Types
  
    -- * Re-exports from Segments
  , module Segments
  
    -- * Re-exports from Evaluation
  , module Evaluation
  
    -- * Re-exports from Conversion
  , module Conversion
  
    -- * Re-exports from Geometry
  , module Geometry
  
    -- * Re-exports from Sampling
  , module Sampling
  
    -- * Re-exports from Subspline
  , module Subspline
  
    -- * Re-exports from Validation
  , module Validation
  
    -- * Re-exports from PointAccess
  , module PointAccess
  
    -- * Re-exports from ArcLength
  , module ArcLength
  
    -- * Legacy Accessors (for backwards compatibility)
  , splinePoints
  , splineIsClosed
  , splineTension
  , bSplinePoints
  , bSplineIsClosed
  ) where

import Hydrogen.Schema.Geometry.Spline.Types
  ( CatmullRomSpline(CatmullRomSpline)
  , catmullRomSpline
  , catmullRomClosed
  , catmullRomTension
  , getCatmullRomPoints
  , getCatmullRomClosed
  , getCatmullRomTensionValue
  , BSpline(BSpline)
  , bSpline
  , bSplineClosed
  , getBSplinePoints
  , getBSplineClosed
  ) as Types

import Hydrogen.Schema.Geometry.Spline.Segments
  ( catmullRomSegmentCount
  , catmullRomSegment
  , bSplineSegmentCount
  , bSplineSegment
  ) as Segments

import Hydrogen.Schema.Geometry.Spline.Evaluation
  ( catmullRomPointAt
  , catmullRomTangentAt
  , bSplinePointAt
  , bSplineTangentAt
  ) as Evaluation

import Hydrogen.Schema.Geometry.Spline.Conversion
  ( catmullRomToBeziers
  , bSplineToBeziers
  ) as Conversion

import Hydrogen.Schema.Geometry.Spline.Geometry
  ( catmullRomLength
  , bSplineLength
  , catmullRomBoundingBox
  , bSplineBoundingBox
  ) as Geometry

import Hydrogen.Schema.Geometry.Spline.Sampling
  ( sampleCatmullRom
  , sampleBSpline
  , sampleCatmullRomTangents
  , sampleBSplineTangents
  ) as Sampling

import Hydrogen.Schema.Geometry.Spline.Subspline
  ( catmullRomSubspline
  , catmullRomHead
  , catmullRomTail
  , bSplineSubspline
  , bSplineHead
  , bSplineTail
  ) as Subspline

import Hydrogen.Schema.Geometry.Spline.Validation
  ( isValidCatmullRom
  , isValidBSpline
  ) as Validation

import Hydrogen.Schema.Geometry.Spline.PointAccess
  ( catmullRomFirstPoint
  , catmullRomLastPoint
  , bSplineFirstPoint
  , bSplineLastPoint
  ) as PointAccess

import Hydrogen.Schema.Geometry.Spline.ArcLength
  ( catmullRomPointAtLength
  , bSplinePointAtLength
  ) as ArcLength

-- Re-import Types for legacy accessors
import Hydrogen.Schema.Geometry.Spline.Types as T
import Hydrogen.Schema.Geometry.Point (Point2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // legacy accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get control points of Catmull-Rom spline.
-- | (Legacy name, use getCatmullRomPoints for clarity)
splinePoints :: T.CatmullRomSpline -> Array Point2D
splinePoints = T.getCatmullRomPoints

-- | Check if Catmull-Rom spline is closed.
-- | (Legacy name, use getCatmullRomClosed for clarity)
splineIsClosed :: T.CatmullRomSpline -> Boolean
splineIsClosed = T.getCatmullRomClosed

-- | Get tension parameter of Catmull-Rom spline.
-- | (Legacy name, use getCatmullRomTensionValue for clarity)
splineTension :: T.CatmullRomSpline -> Number
splineTension = T.getCatmullRomTensionValue

-- | Get control points of B-spline.
-- | (Legacy name, use getBSplinePoints for clarity)
bSplinePoints :: T.BSpline -> Array Point2D
bSplinePoints = T.getBSplinePoints

-- | Check if B-spline is closed.
-- | (Legacy name, use getBSplineClosed for clarity)
bSplineIsClosed :: T.BSpline -> Boolean
bSplineIsClosed = T.getBSplineClosed
