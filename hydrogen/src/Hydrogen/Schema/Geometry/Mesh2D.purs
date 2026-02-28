-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // geometry // mesh2d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mesh2D — 2D triangulated mesh for gradient rendering and deformation.
-- |
-- | ## Architecture
-- |
-- | A 2D mesh is pure data describing:
-- | - Vertices with position, color, and texture coordinates
-- | - Triangulation as index triplets
-- | - Bounds for culling
-- |
-- | This data is interpreted by rendering targets (WebGPU, Canvas, SVG).
-- | The mesh itself is completely target-agnostic.
-- |
-- | ## Composition
-- |
-- | Follows the Schema atom → molecule → compound pattern:
-- | - **Atoms**: VertexIndex (bounded Int), UV coordinates
-- | - **Molecules**: MeshVertex2D (position + color + UV), TriangleIndices
-- | - **Compounds**: Mesh2D (vertices + triangles + bounds)
-- |
-- | ## Submodules
-- |
-- | This module re-exports from specialized submodules:
-- | - `Mesh2D.Vertex`: Vertex types and operations
-- | - `Mesh2D.Triangle`: Triangle indices and triangulation
-- | - `Mesh2D.Bounds`: Axis-aligned bounding box
-- | - `Mesh2D.Sampling`: Color sampling and interpolation
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D)
-- | - Schema.Color.RGB (RGB, RGBA)

module Hydrogen.Schema.Geometry.Mesh2D
  ( -- * Re-exported from submodules
    module Vertex
  , module Triangle
  , module Bounds
  , module Sampling
  
  -- * Compounds
  , Mesh2D(Mesh2D)
  , emptyMesh2D
  , mesh2DFromVertices
  , mesh2DFromQuad
  , mesh2DFromGrid
  
  -- * Mesh2D Accessors
  , getVertices
  , getTriangles
  , vertexCount
  , triangleCount
  , getBounds
  , getVertex
  , getTriangle
  
  -- * Mesh2D Operations
  , addVertex
  , addTriangle
  , updateVertex
  , removeTriangle
  , subdivide
  , computeBounds
  
  -- * UV Sampling
  , sampleAtUV
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , pure
  , bind
  , (+)
  , (/)
  , (<>)
  , (==)
  , (/=)
  , (>=)
  , (<)
  , ($)
  , (#)
  , (||)
  )

import Data.Array (length, index, snoc, mapWithIndex, filter, range, concat)
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Geometry.Point (Point2D, point2D)

-- Re-exports from submodules (using `as` for module re-export pattern)
import Hydrogen.Schema.Geometry.Mesh2D.Vertex 
  ( VertexIndex(VertexIndex)
  , vertexIndex
  , unwrapVertexIndex
  , UV(UV)
  , uv
  , uvOrigin
  , uvTopRight
  , uvBottomLeft
  , uvBottomRight
  , getU
  , getV
  , MeshVertex2D(MeshVertex2D)
  , meshVertex2D
  , meshVertex2DColored
  , meshVertex2DTextured
  , getPosition
  , getColor
  , getUV
  , setPosition
  , setColor
  , setUV
  , lerpVertex
  ) as Vertex

import Hydrogen.Schema.Geometry.Mesh2D.Triangle
  ( TriangleIndices(TriangleIndices)
  , triangleIndices
  , getIndexA
  , getIndexB
  , getIndexC
  , triangleToArray
  , isValidTriangle
  , isDegenerate
  , triangulateQuad
  , triangulateGrid
  ) as Triangle

import Hydrogen.Schema.Geometry.Mesh2D.Bounds
  ( Bounds2D(Bounds2D)
  , bounds2D
  , boundsEmpty
  , boundsFromPoints
  , boundsCenter
  , boundsSize
  , boundsContains
  , boundsIntersects
  , expandBoundsWithPoint
  ) as Bounds

import Hydrogen.Schema.Geometry.Mesh2D.Sampling
  ( BarycentricWeights
  , barycentricWeights
  , interpolateColor
  , lerpColor
  , sampleTriangleAt
  , findAndSampleTriangle
  ) as Sampling

-- Internal imports (unqualified for implementation use)
import Hydrogen.Schema.Geometry.Mesh2D.Vertex
  ( VertexIndex
  , unwrapVertexIndex
  , uv
  , uvOrigin
  , uvTopRight
  , uvBottomLeft
  , uvBottomRight
  , MeshVertex2D
  , meshVertex2D
  , getPosition
  , lerpVertex
  )

import Hydrogen.Schema.Geometry.Mesh2D.Triangle
  ( TriangleIndices(TriangleIndices)
  , triangleIndices
  , isValidTriangle
  , triangulateQuad
  , triangulateGrid
  )

import Hydrogen.Schema.Geometry.Mesh2D.Bounds
  ( Bounds2D
  , boundsEmpty
  , boundsFromPoints
  , expandBoundsWithPoint
  )

import Hydrogen.Schema.Geometry.Mesh2D.Sampling (findAndSampleTriangle)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // mesh2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 2D triangulated mesh.
-- |
-- | Pure data describing geometry for rendering.
-- | Vertices are stored in an array, triangles reference them by index.
newtype Mesh2D = Mesh2D
  { vertices :: Array MeshVertex2D
  , triangles :: Array TriangleIndices
  , bounds :: Bounds2D
  }

derive instance eqMesh2D :: Eq Mesh2D

instance showMesh2D :: Show Mesh2D where
  show (Mesh2D m) = "(Mesh2D vertices:" <> show (length m.vertices)
    <> " triangles:" <> show (length m.triangles)
    <> " bounds:" <> show m.bounds <> ")"

-- | Empty mesh with no vertices or triangles.
emptyMesh2D :: Mesh2D
emptyMesh2D = Mesh2D
  { vertices: []
  , triangles: []
  , bounds: boundsEmpty
  }

-- | Create mesh from vertices (no triangulation).
mesh2DFromVertices :: Array MeshVertex2D -> Mesh2D
mesh2DFromVertices verts = Mesh2D
  { vertices: verts
  , triangles: []
  , bounds: boundsFromPoints (map getPosition verts)
  }

-- | Create mesh from a quad (4 vertices, 2 triangles).
-- |
-- | Vertices should be in order: top-left, top-right, bottom-left, bottom-right.
-- | Colors are interpolated bilinearly across the quad.
mesh2DFromQuad 
  :: Point2D -> Point2D -> Point2D -> Point2D 
  -> RGB -> RGB -> RGB -> RGB 
  -> Mesh2D
mesh2DFromQuad tl tr bl br colTL colTR colBL colBR =
  let
    vertices =
      [ meshVertex2D tl colTL uvOrigin
      , meshVertex2D tr colTR uvTopRight
      , meshVertex2D bl colBL uvBottomLeft
      , meshVertex2D br colBR uvBottomRight
      ]
    triangles = triangulateQuad
  in
    Mesh2D
      { vertices: vertices
      , triangles: triangles
      , bounds: boundsFromPoints [tl, tr, bl, br]
      }

-- | Create mesh from a grid of points with colors.
-- |
-- | Creates a subdivided quad mesh for smoother gradient interpolation.
-- | Rows and cols specify subdivision count (minimum 1).
mesh2DFromGrid
  :: Int                  -- ^ columns
  -> Int                  -- ^ rows
  -> (Number -> Number -> Point2D)   -- ^ position function (u, v) -> position
  -> (Number -> Number -> RGB)       -- ^ color function (u, v) -> color
  -> Mesh2D
mesh2DFromGrid cols rows positionFn colorFn =
  let
    -- Clamp to minimum 1
    c = if cols < 1 then 1 else cols
    r = if rows < 1 then 1 else rows
    
    -- Generate vertices
    vertices = concat $ map (\row ->
      map (\col ->
        let u' = Int.toNumber col / Int.toNumber c
            v' = Int.toNumber row / Int.toNumber r
            pos = positionFn u' v'
            col' = colorFn u' v'
        in meshVertex2D pos col' (uv u' v')
      ) (range 0 c)
    ) (range 0 r)
    
    -- Generate triangle indices
    triangles = triangulateGrid c r
    
    -- Compute bounds
    bounds' = boundsFromPoints (map getPosition vertices)
  in
    Mesh2D
      { vertices: vertices
      , triangles: triangles
      , bounds: bounds'
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // mesh2d accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all vertices.
getVertices :: Mesh2D -> Array MeshVertex2D
getVertices (Mesh2D m) = m.vertices

-- | Get all triangles.
getTriangles :: Mesh2D -> Array TriangleIndices
getTriangles (Mesh2D m) = m.triangles

-- | Get vertex count.
vertexCount :: Mesh2D -> Int
vertexCount (Mesh2D m) = length m.vertices

-- | Get triangle count.
triangleCount :: Mesh2D -> Int
triangleCount (Mesh2D m) = length m.triangles

-- | Get mesh bounds.
getBounds :: Mesh2D -> Bounds2D
getBounds (Mesh2D m) = m.bounds

-- | Get vertex at index.
getVertex :: Int -> Mesh2D -> Maybe MeshVertex2D
getVertex idx (Mesh2D m) = index m.vertices idx

-- | Get triangle at index.
getTriangle :: Int -> Mesh2D -> Maybe TriangleIndices
getTriangle idx (Mesh2D m) = index m.triangles idx

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // mesh2d operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a vertex to the mesh.
addVertex :: MeshVertex2D -> Mesh2D -> Mesh2D
addVertex vert (Mesh2D m) = 
  let
    newVerts = snoc m.vertices vert
    newBounds = expandBoundsWithPoint m.bounds (getPosition vert)
  in
    Mesh2D (m { vertices = newVerts, bounds = newBounds })

-- | Add a triangle to the mesh.
addTriangle :: TriangleIndices -> Mesh2D -> Mesh2D
addTriangle tri (Mesh2D m) =
  if isValidTriangle (length m.vertices) tri
    then Mesh2D (m { triangles = snoc m.triangles tri })
    else Mesh2D m  -- Invalid triangle, return unchanged

-- | Update vertex at index.
updateVertex :: Int -> MeshVertex2D -> Mesh2D -> Mesh2D
updateVertex idx newVert (Mesh2D m) =
  case updateAt idx newVert m.vertices of
    Just newVerts -> Mesh2D 
      { vertices: newVerts
      , triangles: m.triangles
      , bounds: boundsFromPoints (map getPosition newVerts)
      }
    Nothing -> Mesh2D m

-- | Remove triangle at index.
removeTriangle :: Int -> Mesh2D -> Mesh2D
removeTriangle idx (Mesh2D m) =
  let
    newTris = removeAt idx m.triangles
  in
    Mesh2D (m { triangles = newTris })

-- | Recompute bounds from vertices.
computeBounds :: Mesh2D -> Mesh2D
computeBounds (Mesh2D m) = Mesh2D
  (m { bounds = boundsFromPoints (map getPosition m.vertices) })

-- | Subdivide each triangle into 4 smaller triangles.
-- |
-- | Creates new vertices at edge midpoints.
subdivide :: Mesh2D -> Mesh2D
subdivide (Mesh2D m) =
  let
    -- For each triangle, add midpoint vertices and create 4 sub-triangles
    result = foldlArray subdivideTri 
      { verts: m.vertices, tris: [] } 
      m.triangles
  in
    Mesh2D
      { vertices: result.verts
      , triangles: result.tris
      , bounds: boundsFromPoints (map getPosition result.verts)
      }
  where
    subdivideTri :: { verts :: Array MeshVertex2D, tris :: Array TriangleIndices }
                 -> TriangleIndices
                 -> { verts :: Array MeshVertex2D, tris :: Array TriangleIndices }
    subdivideTri state (TriangleIndices tri) =
      case getVertexTriple state.verts tri of
        Nothing -> state  -- Invalid triangle
        Just { va, vb, vc } ->
          let
            -- Create midpoint vertices
            vab = lerpVertex 0.5 va vb
            vbc = lerpVertex 0.5 vb vc
            vca = lerpVertex 0.5 vc va
            
            -- Add midpoint vertices
            baseIdx = length state.verts
            newVerts = state.verts <> [vab, vbc, vca]
            
            -- Original vertex indices
            iA = unwrapVertexIndex tri.a
            iB = unwrapVertexIndex tri.b
            iC = unwrapVertexIndex tri.c
            
            -- Midpoint indices
            iAB = baseIdx
            iBC = baseIdx + 1
            iCA = baseIdx + 2
            
            -- Create 4 sub-triangles
            newTris = 
              [ triangleIndices iA iAB iCA    -- Corner A
              , triangleIndices iAB iB iBC    -- Corner B
              , triangleIndices iCA iBC iC    -- Corner C
              , triangleIndices iAB iBC iCA   -- Center
              ]
          in
            { verts: newVerts
            , tris: state.tris <> newTris
            }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // uv sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample color at UV coordinates in the mesh.
-- |
-- | Finds the triangle containing the point and interpolates vertex colors.
sampleAtUV :: Number -> Number -> Mesh2D -> Maybe RGB
sampleAtUV u' v' (Mesh2D m) =
  let 
    targetPoint = point2D u' v'
  in
    findAndSampleTriangle targetPoint m.vertices m.triangles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fold left over array.
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f initial arr = foldlArrayImpl f initial arr 0 (length arr)

foldlArrayImpl :: forall a b. (b -> a -> b) -> b -> Array a -> Int -> Int -> b
foldlArrayImpl f acc arr idx len =
  if idx >= len
    then acc
    else case index arr idx of
      Nothing -> acc
      Just x -> foldlArrayImpl f (f acc x) arr (idx + 1) len

-- | Get vertex triple from indices.
getVertexTriple :: Array MeshVertex2D 
                -> { a :: VertexIndex, b :: VertexIndex, c :: VertexIndex }
                -> Maybe { va :: MeshVertex2D, vb :: MeshVertex2D, vc :: MeshVertex2D }
getVertexTriple verts tri = do
  va <- index verts (unwrapVertexIndex tri.a)
  vb <- index verts (unwrapVertexIndex tri.b)
  vc <- index verts (unwrapVertexIndex tri.c)
  pure { va, vb, vc }

-- | Update element at index in array.
updateAt :: forall a. Int -> a -> Array a -> Maybe (Array a)
updateAt idx val arr =
  if idx < 0 || idx >= length arr
    then Nothing
    else Just (mapWithIndex (\i x -> if i == idx then val else x) arr)

-- | Remove element at index from array.
removeAt :: forall a. Int -> Array a -> Array a
removeAt idx arr = 
  mapWithIndex (\i x -> { idx: i, val: x }) arr
    # filter (\r -> r.idx /= idx)
    # map (\r -> r.val)
