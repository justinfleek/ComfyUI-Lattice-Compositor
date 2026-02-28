-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // geometry // mesh2d // sampling
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mesh2D color sampling and interpolation functions.
-- |
-- | ## Barycentric Interpolation
-- |
-- | - `barycentricWeights`: Compute barycentric coordinates for a point in a triangle
-- | - `interpolateColor`: Interpolate RGB colors using barycentric weights
-- |
-- | ## Triangle Sampling
-- |
-- | - `sampleTriangleAt`: Sample color at a point within a triangle
-- | - `findAndSampleTriangle`: Find containing triangle and sample

module Hydrogen.Schema.Geometry.Mesh2D.Sampling
  ( -- * Barycentric
    BarycentricWeights
  , barycentricWeights
  
  -- * Color Interpolation
  , interpolateColor
  , lerpColor
  
  -- * Triangle Sampling
  , sampleTriangleAt
  , findAndSampleTriangle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( bind
  , (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  , (>)
  , (<)
  , (&&)
  )

import Data.Array (length, index)
import Data.Int (round) as Int
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Color.Channel (channel)
import Hydrogen.Schema.Color.Channel (toNumber) as Channel
import Hydrogen.Schema.Color.RGB (RGB, rgbFromChannels, red, green, blue)
import Hydrogen.Schema.Geometry.Point (Point2D(Point2D))

import Hydrogen.Schema.Geometry.Mesh2D.Vertex 
  ( MeshVertex2D
  , getPosition
  , getColor
  , unwrapVertexIndex
  )

import Hydrogen.Schema.Geometry.Mesh2D.Triangle
  ( TriangleIndices(TriangleIndices)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // barycentric
-- ═════════════════════════════════════════════════════════════════════════════

-- | Barycentric weights for a point within a triangle.
-- |
-- | Weights sum to 1.0 for points inside the triangle.
-- | Negative weights indicate the point is outside.
type BarycentricWeights = { u :: Number, v :: Number, w :: Number }

-- | Compute barycentric weights for a point in a triangle.
-- |
-- | Given a point P and triangle vertices A, B, C, computes weights
-- | such that P = u*A + v*B + w*C (where u + v + w = 1).
-- |
-- | If any weight is negative, the point is outside the triangle.
barycentricWeights :: Point2D -> Point2D -> Point2D -> Point2D -> BarycentricWeights
barycentricWeights (Point2D p) (Point2D a) (Point2D b) (Point2D c) =
  let
    -- Vectors from A to other points
    v0x = c.x - a.x
    v0y = c.y - a.y
    v1x = b.x - a.x
    v1y = b.y - a.y
    v2x = p.x - a.x
    v2y = p.y - a.y
    
    -- Dot products
    dot00 = v0x * v0x + v0y * v0y
    dot01 = v0x * v1x + v0y * v1y
    dot02 = v0x * v2x + v0y * v2y
    dot11 = v1x * v1x + v1y * v1y
    dot12 = v1x * v2x + v1y * v2y
    
    -- Barycentric coordinates via Cramer's rule
    invDenom = 1.0 / (dot00 * dot11 - dot01 * dot01)
    u' = (dot11 * dot02 - dot01 * dot12) * invDenom
    v' = (dot00 * dot12 - dot01 * dot02) * invDenom
    w' = 1.0 - u' - v'
  in
    { u: w', v: v', w: u' }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // color interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interpolate color using barycentric weights.
-- |
-- | Computes weighted average of three vertex colors.
interpolateColor :: BarycentricWeights -> RGB -> RGB -> RGB -> RGB
interpolateColor weights ca cb cc =
  let
    ra = Channel.toNumber (red ca)
    ga = Channel.toNumber (green ca)
    ba = Channel.toNumber (blue ca)
    rb = Channel.toNumber (red cb)
    gb = Channel.toNumber (green cb)
    bb = Channel.toNumber (blue cb)
    rc = Channel.toNumber (red cc)
    gc = Channel.toNumber (green cc)
    bc = Channel.toNumber (blue cc)
    
    rFinal = ra * weights.u + rb * weights.v + rc * weights.w
    gFinal = ga * weights.u + gb * weights.v + gc * weights.w
    bFinal = ba * weights.u + bb * weights.v + bc * weights.w
  in
    rgbFromChannels
      (channel (clampInt 0 255 (roundToInt rFinal)))
      (channel (clampInt 0 255 (roundToInt gFinal)))
      (channel (clampInt 0 255 (roundToInt bFinal)))

-- | Linear interpolation between two RGB colors.
-- |
-- | t = 0.0 returns first color, t = 1.0 returns second color.
lerpColor :: Number -> RGB -> RGB -> RGB
lerpColor t c1 c2 =
  let
    r1 = Channel.toNumber (red c1)
    g1 = Channel.toNumber (green c1)
    b1 = Channel.toNumber (blue c1)
    r2 = Channel.toNumber (red c2)
    g2 = Channel.toNumber (green c2)
    b2 = Channel.toNumber (blue c2)
    rFinal = r1 + (r2 - r1) * t
    gFinal = g1 + (g2 - g1) * t
    bFinal = b1 + (b2 - b1) * t
  in
    rgbFromChannels 
      (channel (roundToInt rFinal))
      (channel (roundToInt gFinal))
      (channel (roundToInt bFinal))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // triangle sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample color at point within a specific triangle.
-- |
-- | Returns Nothing if point is outside the triangle or vertices invalid.
sampleTriangleAt :: Point2D -> Array MeshVertex2D -> TriangleIndices -> Maybe RGB
sampleTriangleAt pt verts (TriangleIndices tri) = do
  va <- index verts (unwrapVertexIndex tri.a)
  vb <- index verts (unwrapVertexIndex tri.b)
  vc <- index verts (unwrapVertexIndex tri.c)
  
  let weights = barycentricWeights pt (getPosition va) (getPosition vb) (getPosition vc)
  
  -- Check if point is inside triangle (all weights >= 0)
  if weights.u >= 0.0 && weights.v >= 0.0 && weights.w >= 0.0
    then Just (interpolateColor weights (getColor va) (getColor vb) (getColor vc))
    else Nothing

-- | Find triangle containing point and sample its color.
-- |
-- | Iterates through triangles until one contains the point.
findAndSampleTriangle :: Point2D -> Array MeshVertex2D -> Array TriangleIndices -> Maybe RGB
findAndSampleTriangle pt verts tris =
  findFirst (\tri -> sampleTriangleAt pt verts tri) tris

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Round Number to Int using standard rounding.
roundToInt :: Number -> Int
roundToInt = Int.round

-- | Clamp Int to range.
clampInt :: Int -> Int -> Int -> Int
clampInt lo hi x = if x < lo then lo else if x > hi then hi else x

-- | Find first element satisfying predicate and returning Just.
findFirst :: forall a b. (a -> Maybe b) -> Array a -> Maybe b
findFirst f arr = findFirstImpl f arr 0 (length arr)

findFirstImpl :: forall a b. (a -> Maybe b) -> Array a -> Int -> Int -> Maybe b
findFirstImpl f arr idx len =
  if idx >= len
    then Nothing
    else case index arr idx of
      Nothing -> Nothing
      Just x -> case f x of
        Just result -> Just result
        Nothing -> findFirstImpl f arr (idx + 1) len
