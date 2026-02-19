{-|
  Lattice.Services.SVGExtrusion.Simplify - Vertex Simplification Mathematics

  Pure mathematical functions for geometry simplification:
  - Vertex welding (merging close vertices)
  - Tolerance-based rounding
  - Index remapping

  Source: ui/src/services/svgExtrusion.ts (lines 1185-1239)
-}

module Lattice.Services.SVGExtrusion.Simplify
  ( -- * Types
    Vertex3D(..)
  , SimplifiedGeometry(..)
    -- * Tolerance Rounding
  , roundToTolerance
  , roundVertex
  , vertexKey
    -- * Vertex Welding
  , weldVertices
  , remapIndices
    -- * Degenerate Removal
  , isDegenerateTriangle
  , removeDegenerateTriangles
    -- * Full Pipeline
  , simplifyGeometry
  , simplificationStats
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Foldable (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 3D vertex position
data Vertex3D = Vertex3D
  { vertexX :: !Double
  , vertexY :: !Double
  , vertexZ :: !Double
  } deriving (Show, Eq)

-- | Simplified geometry result
data SimplifiedGeometry = SimplifiedGeometry
  { sgPositions :: !(Vector Double)    -- ^ Flattened x,y,z values
  , sgIndices :: !(Vector Int)         -- ^ Triangle indices
  , sgOriginalToNew :: !(Vector Int)   -- ^ Mapping from original to new vertex index
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Tolerance Rounding
--------------------------------------------------------------------------------

-- | Round a value to the nearest tolerance step.
--
--   This is the key to vertex welding - vertices within tolerance
--   will round to the same value.
roundToTolerance :: Double -> Double -> Double
roundToTolerance v tolerance
  | tolerance <= 0.0 = v
  | otherwise = fromIntegral (round (v / tolerance) :: Int) * tolerance

-- | Round a 3D vertex to tolerance grid.
roundVertex :: Vertex3D -> Double -> Vertex3D
roundVertex vertex tolerance = Vertex3D
  { vertexX = roundToTolerance (vertexX vertex) tolerance
  , vertexY = roundToTolerance (vertexY vertex) tolerance
  , vertexZ = roundToTolerance (vertexZ vertex) tolerance
  }

-- | Create a string key for a vertex (for deduplication).
vertexKey :: Vertex3D -> String
vertexKey vertex =
  show (vertexX vertex) ++ "," ++ show (vertexY vertex) ++ "," ++ show (vertexZ vertex)

--------------------------------------------------------------------------------
-- Vertex Welding
--------------------------------------------------------------------------------

-- | Weld state during processing
data WeldState = WeldState
  { wsPositions :: ![Double]     -- ^ Accumulated positions (reversed)
  , wsSeenKeys :: !(Map String Int)  -- ^ Vertex key -> new index
  , wsIndexMap :: ![Int]         -- ^ Original index -> new index (reversed)
  , wsNextIndex :: !Int          -- ^ Next new vertex index
  }

-- | Weld vertices by merging those within tolerance.
--
--   This is a vertex deduplication algorithm that merges vertices
--   that are closer than the tolerance threshold.
weldVertices :: Vector Vertex3D -> Double -> SimplifiedGeometry
weldVertices vertices tolerance =
  let initialState = WeldState [] Map.empty [] 0

      processVertex :: WeldState -> Vertex3D -> WeldState
      processVertex state vertex =
        let rounded = roundVertex vertex tolerance
            key = vertexKey rounded
        in case Map.lookup key (wsSeenKeys state) of
          Just existingIndex ->
            state { wsIndexMap = existingIndex : wsIndexMap state }
          Nothing ->
            let newIndex = wsNextIndex state
                newPositions = vertexZ rounded : vertexY rounded : vertexX rounded : wsPositions state
                newSeenKeys = Map.insert key newIndex (wsSeenKeys state)
            in WeldState
              { wsPositions = newPositions
              , wsSeenKeys = newSeenKeys
              , wsIndexMap = newIndex : wsIndexMap state
              , wsNextIndex = newIndex + 1
              }

      finalState = V.foldl' processVertex initialState vertices

  in SimplifiedGeometry
    { sgPositions = V.fromList (reverse (wsPositions finalState))
    , sgIndices = V.empty  -- Indices need to be rebuilt from original geometry
    , sgOriginalToNew = V.fromList (reverse (wsIndexMap finalState))
    }

-- | Remap triangle indices using the vertex mapping.
remapIndices :: Vector Int -> Vector Int -> Vector Int
remapIndices originalIndices indexMap = V.map remap originalIndices
  where
    remap oldIdx
      | oldIdx >= 0 && oldIdx < V.length indexMap = indexMap V.! oldIdx
      | otherwise = oldIdx  -- Keep original if out of bounds

--------------------------------------------------------------------------------
-- Degenerate Triangle Removal
--------------------------------------------------------------------------------

-- | Check if a triangle is degenerate (has repeated vertices).
isDegenerateTriangle :: Int -> Int -> Int -> Bool
isDegenerateTriangle i0 i1 i2 = i0 == i1 || i1 == i2 || i0 == i2

-- | Remove degenerate triangles from index array.
--
--   After welding, some triangles may collapse to lines or points.
removeDegenerateTriangles :: Vector Int -> Vector Int
removeDegenerateTriangles indices =
  let triCount = V.length indices `div` 3
      process acc i
        | i >= triCount = acc
        | otherwise =
            let base = i * 3
                i0 = indices V.! base
                i1 = indices V.! (base + 1)
                i2 = indices V.! (base + 2)
            in if isDegenerateTriangle i0 i1 i2
               then process acc (i + 1)
               else process (i2 : i1 : i0 : acc) (i + 1)
  in V.fromList (reverse (process [] 0))

--------------------------------------------------------------------------------
-- Full Pipeline
--------------------------------------------------------------------------------

-- | Simplify geometry by welding vertices and removing degenerate triangles.
simplifyGeometry :: Vector Vertex3D -> Vector Int -> Double -> SimplifiedGeometry
simplifyGeometry vertices indices tolerance =
  let welded = weldVertices vertices tolerance
      remappedIndices = remapIndices indices (sgOriginalToNew welded)
      cleanIndices = removeDegenerateTriangles remappedIndices
  in welded { sgIndices = cleanIndices }

-- | Calculate simplification statistics.
--
--   Returns (new vertex count, reduction percentage)
simplificationStats :: Int -> SimplifiedGeometry -> (Int, Double)
simplificationStats originalVertexCount simplified =
  let newCount = V.length (sgPositions simplified) `div` 3
      reduction = if originalVertexCount > 0
                  then (1.0 - fromIntegral newCount / fromIntegral originalVertexCount) * 100.0
                  else 0.0
  in (newCount, reduction)
