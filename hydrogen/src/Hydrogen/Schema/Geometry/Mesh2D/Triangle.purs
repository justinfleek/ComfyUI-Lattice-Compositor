-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // geometry // mesh2d // triangle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mesh2D triangle types and triangulation functions.
-- |
-- | ## Molecules
-- |
-- | - `TriangleIndices`: Three vertex indices defining a triangle
-- |
-- | ## Triangulation
-- |
-- | - `triangulateQuad`: Split quad into 2 triangles
-- | - `triangulateGrid`: Generate indices for N×M grid

module Hydrogen.Schema.Geometry.Mesh2D.Triangle
  ( -- * Types
    TriangleIndices(TriangleIndices)
  , triangleIndices
  , getIndexA
  , getIndexB
  , getIndexC
  , triangleToArray
  , isValidTriangle
  , isDegenerate
  
  -- * Triangulation
  , triangulateQuad
  , triangulateGrid
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , (+)
  , (-)
  , (*)
  , (<>)
  , (==)
  , (>=)
  , (<)
  , (&&)
  , (||)
  , ($)
  )

import Data.Array (concat, range)

import Hydrogen.Schema.Geometry.Mesh2D.Vertex 
  ( VertexIndex
  , vertexIndex
  , unwrapVertexIndex
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // triangle indices
-- ═════════════════════════════════════════════════════════════════════════════

-- | Triangle defined by three vertex indices.
-- |
-- | Indices reference vertices in a Mesh2D vertex array.
-- | Winding order is counter-clockwise for front-facing triangles.
newtype TriangleIndices = TriangleIndices
  { a :: VertexIndex
  , b :: VertexIndex
  , c :: VertexIndex
  }

derive instance eqTriangleIndices :: Eq TriangleIndices

instance showTriangleIndices :: Show TriangleIndices where
  show (TriangleIndices t) = "(TriangleIndices a:" 
    <> show t.a <> " b:" 
    <> show t.b <> " c:" 
    <> show t.c <> ")"

-- | Create triangle indices.
triangleIndices :: Int -> Int -> Int -> TriangleIndices
triangleIndices a' b' c' = TriangleIndices
  { a: vertexIndex a'
  , b: vertexIndex b'
  , c: vertexIndex c'
  }

-- | Get index A.
getIndexA :: TriangleIndices -> VertexIndex
getIndexA (TriangleIndices t) = t.a

-- | Get index B.
getIndexB :: TriangleIndices -> VertexIndex
getIndexB (TriangleIndices t) = t.b

-- | Get index C.
getIndexC :: TriangleIndices -> VertexIndex
getIndexC (TriangleIndices t) = t.c

-- | Convert to array of indices.
triangleToArray :: TriangleIndices -> Array Int
triangleToArray (TriangleIndices t) = 
  [ unwrapVertexIndex t.a
  , unwrapVertexIndex t.b
  , unwrapVertexIndex t.c
  ]

-- | Check if triangle indices are valid for a mesh of given size.
isValidTriangle :: Int -> TriangleIndices -> Boolean
isValidTriangle vertCount (TriangleIndices t) =
  let
    a' = unwrapVertexIndex t.a
    b' = unwrapVertexIndex t.b
    c' = unwrapVertexIndex t.c
  in
    a' >= 0 && a' < vertCount &&
    b' >= 0 && b' < vertCount &&
    c' >= 0 && c' < vertCount

-- | Check if triangle is degenerate (has repeated indices).
isDegenerate :: TriangleIndices -> Boolean
isDegenerate (TriangleIndices t) =
  t.a == t.b || t.b == t.c || t.c == t.a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // triangulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Triangulate a quad (2 triangles).
-- |
-- | Assumes vertices at indices 0, 1, 2, 3 in order:
-- | - 0: top-left
-- | - 1: top-right
-- | - 2: bottom-left
-- | - 3: bottom-right
triangulateQuad :: Array TriangleIndices
triangulateQuad =
  [ triangleIndices 0 2 1  -- Top-left triangle (0, 2, 1)
  , triangleIndices 1 2 3  -- Bottom-right triangle (1, 2, 3)
  ]

-- | Triangulate a grid of vertices.
-- |
-- | Creates 2 triangles per cell, with (cols+1) * (rows+1) vertices.
triangulateGrid :: Int -> Int -> Array TriangleIndices
triangulateGrid cols rows =
  let
    -- Vertices per row
    stride = cols + 1
  in
    concat $ map (\row ->
      concat $ map (\col ->
        let 
          tl = row * stride + col
          tr = tl + 1
          bl = tl + stride
          br = bl + 1
        in
          [ triangleIndices tl bl tr
          , triangleIndices tr bl br
          ]
      ) (range 0 (cols - 1))
    ) (range 0 (rows - 1))

