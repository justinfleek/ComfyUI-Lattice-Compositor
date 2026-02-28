-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // gpu // webgpu // forward-plus
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Forward+ (Tiled Forward) Rendering Pipeline
-- |
-- | ## Technique
-- | - Split screen into tiles
-- | - Light culling per tile in compute shader
-- | - Forward render with per-tile light list
-- |
-- | ## Advantages over Deferred
-- | - Transparent objects render correctly
-- | - Less memory bandwidth
-- | - MSAA support
-- |
-- | ## Dependencies
-- | - Prelude
-- | - WebGPU.Types
-- |
-- | ## Dependents
-- | - WebGPU.Render

module Hydrogen.GPU.WebGPU.ForwardPlus
  ( -- Types
    TiledConfig(..)
  , TileSize(..)
  , LightTile(..)
  , TiledLightList(..)
  , ClusteredConfig(..)
  , Cluster(..)
  , CullingMethod(..)
    -- Configuration
  , tiledConfig
  , clusteredConfig
    -- Tiling
  , computeTileCount
  , createLightTile
  , createTiledLightList
    -- Clustering
  , computeClusterCount
  , createCluster
  , clusterLights
    -- Pipeline
  , ForwardPlusPipeline(..)
  , forwardPlusPipeline
  ) where

import Prelude

import Data.Array (catMaybes, mapWithIndex, length, filter, concatMap, range) as Data.Array
import Data.Functor (map) as Data.Functor
import Data.Int (toNumber) as Data.Int
import Data.Maybe (Maybe(..))

import Hydrogen.GPU.Types.Bounded
  ( TileCount
  , tileCount
  , unwrapTileCount
  , Radius
  , radius
  , unwrapRadius
  , PixelDimension
  , pixelDimension
  , unwrapPixelDimension
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // tiled // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tile size options
data TileSize
  = Tile16
  | Tile32
  | Tile64

derive instance eqTileSize :: Eq TileSize
derive instance ordTileSize :: Ord TileSize

-- | Forward+ tiled rendering configuration
-- | Uses bounded tile counts
type TiledConfig =
  { tileSize :: TileSize
  , maxLightsPerTile :: TileCount      -- ^ Max lights per tile [1,∞)
  , useLargeTiles :: Boolean
  , cullingMethod :: CullingMethod
  }

data CullingMethod
  = CPUCulling
  | GPUCulling
  | HybridCulling

derive instance eqCullingMethod :: Eq CullingMethod
derive instance ordCullingMethod :: Ord CullingMethod

-- | Create default tiled config
tiledConfig :: TiledConfig
tiledConfig =
  { tileSize: Tile16
  , maxLightsPerTile: tileCount 256
  , useLargeTiles: false
  , cullingMethod: GPUCulling
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // light // tiles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light tile for forward+ rendering
type LightTile =
  { tileX :: Int
  , tileY :: Int
  , lightIndices :: Array Int
  , lightCount :: Int
  }

-- | Create light tile
createLightTile :: Int -> Int -> LightTile
createLightTile tx ty =
  { tileX: tx
  , tileY: ty
  , lightIndices: []
  , lightCount: 0
  }

-- | Tiled light list (per-tile light data)
-- | Uses bounded tile counts
type TiledLightList =
  { tiles :: Array LightTile
  , tileCountX :: TileCount            -- ^ Horizontal tile count [1,∞)
  , tileCountY :: TileCount            -- ^ Vertical tile count [1,∞)
  , maxLights :: TileCount             -- ^ Maximum total lights [1,∞)
  }

-- | Create tiled light list
createTiledLightList :: Int -> Int -> Int -> TiledLightList
createTiledLightList width height tileSz =
  let tcX = ceilDiv width tileSz
      tcY = ceilDiv height tileSz
      tiles = generateTiles tcX tcY
  in { tiles, tileCountX: tileCount tcX, tileCountY: tileCount tcY, maxLights: tileCount 256 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // clustered // rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clustered forward rendering configuration
-- | Uses bounded tile and cluster counts
type ClusteredConfig =
  { tileSizeX :: TileCount             -- ^ Horizontal tile size [1,∞)
  , tileSizeY :: TileCount             -- ^ Vertical tile size [1,∞)
  , clusterDepthSlices :: TileCount    -- ^ Depth slices [1,∞)
  , maxLightsPerCluster :: TileCount   -- ^ Max lights per cluster [1,∞)
  , useTransparentClustering :: Boolean
  }

-- | Create default clustered config
clusteredConfig :: ClusteredConfig
clusteredConfig =
  { tileSizeX: tileCount 16
  , tileSizeY: tileCount 16
  , clusterDepthSlices: tileCount 16
  , maxLightsPerCluster: tileCount 64
  , useTransparentClustering: true
  }

-- | Cluster for visibility testing
type Cluster =
  { clusterX :: Int
  , clusterY :: Int
  , clusterZ :: Int
  , minZ :: Number
  , maxZ :: Number
  , lightIndices :: Array Int
  , lightCount :: Int
  }

-- | Create cluster
createCluster :: Int -> Int -> Int -> Number -> Number -> Cluster
createCluster cx cy cz minz maxz =
  { clusterX: cx
  , clusterY: cy
  , clusterZ: cz
  , minZ: minz
  , maxZ: maxz
  , lightIndices: []
  , lightCount: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // light // culling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light bounding sphere
type LightBounds =
  { position :: { x :: Number, y :: Number, z :: Number }
  , radius :: Number
  }

-- | Cluster light assignment
clusterLights :: ClusteredConfig -> Cluster -> Array LightBounds -> Cluster
clusterLights config cluster lights =
  let visible = filterLightsByCluster cluster lights
  in cluster { lightIndices = visible, lightCount = length visible }

-- | Filter lights by cluster bounds
filterLightsByCluster :: Cluster -> Array LightBounds -> Array Int
filterLightsByCluster cluster lights =
  Data.Array.mapWithIndex 
    (\idx light -> if lightIntersectsCluster light cluster then Just idx else Nothing)
    lights
  # Data.Array.catMaybes

-- | Check if light intersects cluster
lightIntersectsCluster :: LightBounds -> Cluster -> Boolean
lightIntersectsCluster light cluster =
  let inX = light.position.x >= intToFloat cluster.clusterX - light.radius
      inY = light.position.y >= intToFloat cluster.clusterY - light.radius
      inZ = light.position.z >= cluster.minZ - light.radius
  in inX && inY && inZ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // tile // computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute tile count from resolution
computeTileCount :: Int -> Int -> TileSize -> { x :: Int, y :: Int }
computeTileCount width height tile =
  let size = tileSizeToInt tile
      tx = ceilDiv width size
      ty = ceilDiv height size
  in { x: tx, y: ty }

-- | Convert tile size to integer
tileSizeToInt :: TileSize -> Int
tileSizeToInt = case _ of
  Tile16 -> 16
  Tile32 -> 32
  Tile64 -> 64

-- | Compute cluster count
computeClusterCount :: ClusteredConfig -> { x :: Int, y :: Int, z :: Int }
computeClusterCount config =
  let cx = ceilDiv 1920 (unwrapTileCount config.tileSizeX)
      cy = ceilDiv 1080 (unwrapTileCount config.tileSizeY)
      cz = unwrapTileCount config.clusterDepthSlices
  in { x: cx, y: cy, z: cz }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // forward // plus // pipeline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Forward+ pipeline state
type ForwardPlusPipeline =
  { tiledConfig :: TiledConfig
  , clusteredConfig :: ClusteredConfig
  , lightList :: TiledLightList
  , useClustering :: Boolean
  }

-- | Create forward+ pipeline
forwardPlusPipeline :: Int -> Int -> ForwardPlusPipeline
forwardPlusPipeline width height =
  let tileSize = tileSizeToInt Tile16
      lightList = createTiledLightList width height tileSize
  in { tiledConfig: tiledConfig, clusteredConfig: clusteredConfig, lightList, useClustering: false }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // helper // functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate tiles
generateTiles :: Int -> Int -> Array LightTile
generateTiles tx ty = concatMap (\x -> map (\y -> createLightTile x y) (until ty)) (until tx)

-- | Integer division ceiling
ceilDiv :: Int -> Int -> Int
ceilDiv a b = (a + b - 1) / b

-- | Convert int to float
intToFloat :: Int -> Number
intToFloat = Data.Int.toNumber

-- | Get length of array
length :: forall a. Array a -> Int
length = Data.Array.length

-- | Map over array
map :: forall a b. (a -> b) -> Array a -> Array b
map = Data.Functor.map

-- | Filter array
filter :: forall a. (a -> Boolean) -> Array a -> Array a
filter = Data.Array.filter

-- | Concatenate arrays
concatMap :: forall a b. (a -> Array b) -> Array a -> Array b
concatMap = Data.Array.concatMap

-- | Range operator
until :: Int -> Array Int
until n = if n <= 0 then [] else Data.Array.range 0 (n - 1)

-- | Array append
append :: forall a. Array a -> Array a -> Array a
append a b = a <> b
