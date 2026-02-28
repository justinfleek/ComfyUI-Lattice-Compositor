-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // mesh-gradient // svg
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SVG rendering for mesh gradients.
-- |
-- | Provides polygon-based SVG rendering as a fallback for browsers
-- | without WebGPU support. For production quality, use WebGPU/Canvas targets.
-- |
-- | ## Rendering Strategy
-- |
-- | Each triangle in the mesh is rendered as an SVG polygon with
-- | averaged vertex colors as fill. Higher subdivision counts produce
-- | smoother gradients at the cost of more polygons.

module Hydrogen.Element.Compound.MeshGradient.SVG
  ( renderMeshAsSVG
  , renderTriangle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , bind
  , (<>)
  , (+)
  , (==)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB (RGB, rgbToLegacyCss)
import Hydrogen.Schema.Geometry.Mesh2D
  ( Mesh2D
  , MeshVertex2D
  , TriangleIndices
  , getVertices
  , getTriangles
  , getPosition
  , getColor
  , triangleToArray
  , lerpVertex
  , meshVertex2DColored
  )
import Hydrogen.Schema.Geometry.Point (getX, getY, point2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render mesh as SVG polygons.
-- |
-- | This is the fallback/intermediate representation. For production use,
-- | WebGPU or Canvas targets provide better quality.
renderMeshAsSVG :: forall msg. Int -> Int -> Mesh2D -> E.Element msg
renderMeshAsSVG w h meshData =
  let
    widthStr = show w
    heightStr = show h
    viewBox = "0 0 " <> widthStr <> " " <> heightStr
    
    vertices = getVertices meshData
    triangles = getTriangles meshData
    
    -- Render each triangle as a polygon
    triangleElements = foldl (\acc tri -> acc <> [renderTriangle vertices tri]) [] triangles
  in
    E.svg_
      [ E.attr "width" widthStr
      , E.attr "height" heightStr
      , E.attr "viewBox" viewBox
      , E.attr "preserveAspectRatio" "none"
      , E.ariaHidden true
      ]
      triangleElements

-- | Render a single triangle.
renderTriangle :: forall msg. Array MeshVertex2D -> TriangleIndices -> E.Element msg
renderTriangle vertices tri =
  let
    indices = triangleToArray tri
    
    -- Get vertices (with bounds checking)
    maybeVerts = getTriangleVerts vertices indices
  in
    case maybeVerts of
      Nothing -> E.empty
      Just verts -> 
        let
          -- Build polygon points
          points = buildPolygonPoints verts.v0 verts.v1 verts.v2
          
          -- Average color for fill (simple approach)
          avgColor = averageColors (getColor verts.v0) (getColor verts.v1) (getColor verts.v2)
        in
          E.svgElement "polygon"
            [ E.attr "points" points
            , E.attr "fill" (rgbToLegacyCss avgColor)
            , E.attr "stroke" (rgbToLegacyCss avgColor)
            , E.attr "stroke-width" "0.5"
            ]
            []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get triangle vertices from array.
getTriangleVerts :: Array MeshVertex2D -> Array Int 
                 -> Maybe { v0 :: MeshVertex2D, v1 :: MeshVertex2D, v2 :: MeshVertex2D }
getTriangleVerts vertices indices =
  case indices of
    [i0, i1, i2] -> do
      v0 <- indexArray i0 vertices
      v1 <- indexArray i1 vertices
      v2 <- indexArray i2 vertices
      Just { v0, v1, v2 }
    _ -> Nothing

-- | Safe array index.
indexArray :: forall a. Int -> Array a -> Maybe a
indexArray i arr = 
  let
    result = foldl (\acc x -> 
      case acc.found of
        Just _ -> acc
        Nothing -> 
          if acc.idx == i 
            then { idx: acc.idx + 1, found: Just x }
            else { idx: acc.idx + 1, found: Nothing }
    ) { idx: 0, found: Nothing } arr
  in
    result.found

-- | Build SVG polygon points string.
buildPolygonPoints :: MeshVertex2D -> MeshVertex2D -> MeshVertex2D -> String
buildPolygonPoints v0 v1 v2 =
  let
    p0 = getPosition v0
    p1 = getPosition v1
    p2 = getPosition v2
  in
    show (getX p0) <> "," <> show (getY p0) <> " " <>
    show (getX p1) <> "," <> show (getY p1) <> " " <>
    show (getX p2) <> "," <> show (getY p2)

-- | Average three colors.
-- |
-- | Uses lerp to blend: first blend c1 and c2, then blend with c3.
averageColors :: RGB -> RGB -> RGB -> RGB
averageColors c1 c2 c3 = 
  let
    -- Blend c1 and c2 at 50%
    blend12 = lerpRGB 0.5 c1 c2
    -- Blend result with c3 at 33% (to get 1/3 weight each)
    blend123 = lerpRGB 0.333333 blend12 c3
  in
    blend123

-- | Linear interpolation of RGB colors via mesh vertex.
lerpRGB :: Number -> RGB -> RGB -> RGB
lerpRGB t c1 c2 =
  let
    v1 = meshVertex2DColored (point2D 0.0 0.0) c1
    v2 = meshVertex2DColored (point2D 1.0 1.0) c2
    interpolated = lerpVertex t v1 v2
  in
    getColor interpolated
