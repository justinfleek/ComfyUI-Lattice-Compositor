{-
  Lattice.Services.SVGExtrusion.Simplify - Vertex Simplification Mathematics

  Pure mathematical functions for geometry simplification:
  - Vertex welding (merging close vertices)
  - Tolerance-based rounding
  - Index remapping

  Source: ui/src/services/svgExtrusion.ts (lines 1185-1239)
-}

module Lattice.Services.SVGExtrusion.Simplify
  ( Vertex3D
  , SimplifiedGeometry
  , roundToTolerance
  , roundVertex
  , vertexKey
  , weldVertices
  , remapIndices
  , isDegenerateTriangle
  , removeDegenerateTriangles
  , simplifyGeometry
  , simplificationStats
  ) where

import Prelude

import Data.Array (length, mapWithIndex, snoc, (!!))
import Data.Foldable (foldl)
import Data.Int (round, toNumber) as Int
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 3D vertex position
type Vertex3D =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Simplified geometry result
type SimplifiedGeometry =
  { positions :: Array Number      -- Flattened x,y,z values
  , indices :: Array Int           -- Triangle indices
  , originalToNew :: Array Int     -- Mapping from original to new vertex index
  }

--------------------------------------------------------------------------------
-- Tolerance Rounding
--------------------------------------------------------------------------------

-- | Round a value to the nearest tolerance step.
roundToTolerance :: Number -> Number -> Number
roundToTolerance v tolerance
  | tolerance <= 0.0 = v
  | otherwise = Int.toNumber (Int.round (v / tolerance)) * tolerance

-- | Round a 3D vertex to tolerance grid.
roundVertex :: Vertex3D -> Number -> Vertex3D
roundVertex vertex tolerance =
  { x: roundToTolerance vertex.x tolerance
  , y: roundToTolerance vertex.y tolerance
  , z: roundToTolerance vertex.z tolerance
  }

-- | Create a string key for a vertex (for deduplication).
vertexKey :: Vertex3D -> String
vertexKey vertex =
  show vertex.x <> "," <> show vertex.y <> "," <> show vertex.z

--------------------------------------------------------------------------------
-- Vertex Welding
--------------------------------------------------------------------------------

-- | Weld state during processing
type WeldState =
  { positions :: Array Number
  , seenKeys :: Map String Int
  , indexMap :: Array Int
  , nextIndex :: Int
  }

-- | Weld vertices by merging those within tolerance.
weldVertices :: Array Vertex3D -> Number -> SimplifiedGeometry
weldVertices vertices tolerance =
  let initialState :: WeldState
      initialState =
        { positions: []
        , seenKeys: Map.empty
        , indexMap: []
        , nextIndex: 0
        }

      processVertex :: WeldState -> Vertex3D -> WeldState
      processVertex state vertex =
        let rounded = roundVertex vertex tolerance
            key = vertexKey rounded
        in case Map.lookup key state.seenKeys of
          Just existingIndex ->
            state { indexMap = snoc state.indexMap existingIndex }
          Nothing ->
            let newIndex = state.nextIndex
                newPositions = snoc (snoc (snoc state.positions rounded.x) rounded.y) rounded.z
                newSeenKeys = Map.insert key newIndex state.seenKeys
            in { positions: newPositions
               , seenKeys: newSeenKeys
               , indexMap: snoc state.indexMap newIndex
               , nextIndex: newIndex + 1
               }

      finalState = foldl processVertex initialState vertices

  in { positions: finalState.positions
     , indices: []
     , originalToNew: finalState.indexMap
     }

-- | Remap triangle indices using the vertex mapping.
remapIndices :: Array Int -> Array Int -> Array Int
remapIndices originalIndices indexMap =
  map remap originalIndices
  where
    remap oldIdx =
      fromMaybe oldIdx (indexMap !! oldIdx)

--------------------------------------------------------------------------------
-- Degenerate Triangle Removal
--------------------------------------------------------------------------------

-- | Check if a triangle is degenerate (has repeated vertices).
isDegenerateTriangle :: Int -> Int -> Int -> Boolean
isDegenerateTriangle i0 i1 i2 = i0 == i1 || i1 == i2 || i0 == i2

-- | Remove degenerate triangles from index array.
removeDegenerateTriangles :: Array Int -> Array Int
removeDegenerateTriangles indices =
  let triCount = length indices / 3

      process :: Int -> Array Int -> Array Int
      process i acc
        | i >= triCount = acc
        | otherwise =
            let base = i * 3
                i0 = fromMaybe 0 (indices !! base)
                i1 = fromMaybe 0 (indices !! (base + 1))
                i2 = fromMaybe 0 (indices !! (base + 2))
            in if isDegenerateTriangle i0 i1 i2
               then process (i + 1) acc
               else process (i + 1) (snoc (snoc (snoc acc i0) i1) i2)
  in process 0 []

--------------------------------------------------------------------------------
-- Full Pipeline
--------------------------------------------------------------------------------

-- | Simplify geometry by welding vertices and removing degenerate triangles.
simplifyGeometry :: Array Vertex3D -> Array Int -> Number -> SimplifiedGeometry
simplifyGeometry vertices indices tolerance =
  let welded = weldVertices vertices tolerance
      remappedIndices = remapIndices indices welded.originalToNew
      cleanIndices = removeDegenerateTriangles remappedIndices
  in welded { indices = cleanIndices }

-- | Calculate simplification statistics.
--   Returns (new vertex count, reduction percentage)
simplificationStats :: Int -> SimplifiedGeometry -> Tuple Int Number
simplificationStats originalVertexCount simplified =
  let newCount = length simplified.positions / 3
      reduction = if originalVertexCount > 0
                  then (1.0 - Int.toNumber newCount / Int.toNumber originalVertexCount) * 100.0
                  else 0.0
  in Tuple newCount reduction
