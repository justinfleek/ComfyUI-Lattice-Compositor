-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // gpu // types // bounded
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU-specific bounded numeric types.
-- |
-- | These types enforce valid ranges for GPU rendering parameters at the
-- | type level. Invalid states become unrepresentable.
-- |
-- | ## Categories
-- |
-- | - **Unit Interval [0,1]**: metallic, roughness, alpha, UV coordinates
-- | - **Positive Numbers [0,∞)**: intensity, radius, distance
-- | - **Angles [0,2π]**: cone angles in radians
-- | - **Dimensions [1,∞)**: width, height, tile counts
-- | - **Indices [0,∞)**: buffer indices, instance IDs
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Bounded (core clamping functions)
-- |
-- | ## Dependents
-- | - Hydrogen.GPU.WebGPU.DeferredRendering
-- | - Hydrogen.GPU.WebGPU.ForwardPlus
-- | - Hydrogen.GPU.WebGPU.RayTracing

module Hydrogen.GPU.Types.Bounded
  ( -- * Unit Interval Types
    Metallic
  , metallic
  , unwrapMetallic
  , metallicBounds
  , Roughness
  , roughness
  , unwrapRoughness
  , roughnessBounds
  , Alpha
  , alpha
  , unwrapAlpha
  , alphaBounds
  , UVCoord
  , uvCoord
  , unwrapUVCoord
  , uvCoordBounds
  , NormalizedChannel
  , normalizedChannel
  , unwrapNormalizedChannel
  , normalizedChannelBounds
    -- * Positive Number Types
  , Intensity
  , intensity
  , unwrapIntensity
  , intensityBounds
  , Radius
  , radius
  , unwrapRadius
  , radiusBounds
  , Distance
  , distance
  , unwrapDistance
  , distanceBounds
  , IOR
  , ior
  , unwrapIOR
  , iorBounds
    -- * Angle Types
  , ConeAngle
  , coneAngle
  , unwrapConeAngle
  , coneAngleBounds
    -- * Dimension Types
  , PixelDimension
  , pixelDimension
  , unwrapPixelDimension
  , pixelDimensionBounds
  , TileCount
  , tileCount
  , unwrapTileCount
  , tileCountBounds
    -- * Index Types
  , BufferIndex
  , bufferIndex
  , unwrapBufferIndex
  , bufferIndexBounds
  , BounceCount
  , bounceCount
  , unwrapBounceCount
  , bounceCountBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<)
  , (>)
  , (<>)
  )

import Hydrogen.Schema.Bounded (NumberBounds, numberBounds, IntBounds, intBounds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // unit // interval // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metallic factor [0,1]
-- |
-- | 0.0 = dielectric (non-metal), 1.0 = pure metal
-- | Affects Fresnel reflectance calculation in PBR rendering.
newtype Metallic = Metallic Number

derive instance eqMetallic :: Eq Metallic
derive instance ordMetallic :: Ord Metallic

instance showMetallic :: Show Metallic where
  show (Metallic m) = "Metallic " <> show m

-- | Create metallic factor, clamped to [0,1]
metallic :: Number -> Metallic
metallic n
  | n < 0.0 = Metallic 0.0
  | n > 1.0 = Metallic 1.0
  | otherwise = Metallic n

-- | Extract raw value
unwrapMetallic :: Metallic -> Number
unwrapMetallic (Metallic m) = m

-- | Bounds documentation
metallicBounds :: NumberBounds
metallicBounds = numberBounds 0.0 1.0 "metallic" "PBR metallic factor (0=dielectric, 1=metal)"

-- | Roughness factor [0,1]
-- |
-- | 0.0 = perfectly smooth (mirror), 1.0 = completely rough (diffuse)
-- | Controls microfacet distribution in PBR specular calculations.
newtype Roughness = Roughness Number

derive instance eqRoughness :: Eq Roughness
derive instance ordRoughness :: Ord Roughness

instance showRoughness :: Show Roughness where
  show (Roughness r) = "Roughness " <> show r

-- | Create roughness factor, clamped to [0,1]
roughness :: Number -> Roughness
roughness n
  | n < 0.0 = Roughness 0.0
  | n > 1.0 = Roughness 1.0
  | otherwise = Roughness n

-- | Extract raw value
unwrapRoughness :: Roughness -> Number
unwrapRoughness (Roughness r) = r

-- | Bounds documentation
roughnessBounds :: NumberBounds
roughnessBounds = numberBounds 0.0 1.0 "roughness" "PBR roughness factor (0=smooth, 1=rough)"

-- | Alpha/opacity factor [0,1]
-- |
-- | 0.0 = fully transparent, 1.0 = fully opaque
newtype Alpha = Alpha Number

derive instance eqAlpha :: Eq Alpha
derive instance ordAlpha :: Ord Alpha

instance showAlpha :: Show Alpha where
  show (Alpha a) = "Alpha " <> show a

-- | Create alpha factor, clamped to [0,1]
alpha :: Number -> Alpha
alpha n
  | n < 0.0 = Alpha 0.0
  | n > 1.0 = Alpha 1.0
  | otherwise = Alpha n

-- | Extract raw value
unwrapAlpha :: Alpha -> Number
unwrapAlpha (Alpha a) = a

-- | Bounds documentation
alphaBounds :: NumberBounds
alphaBounds = numberBounds 0.0 1.0 "alpha" "Opacity factor (0=transparent, 1=opaque)"

-- | UV texture coordinate [0,1]
-- |
-- | Standard texture coordinates, where (0,0) is typically bottom-left
-- | and (1,1) is top-right. Values outside [0,1] depend on wrap mode.
newtype UVCoord = UVCoord Number

derive instance eqUVCoord :: Eq UVCoord
derive instance ordUVCoord :: Ord UVCoord

instance showUVCoord :: Show UVCoord where
  show (UVCoord u) = "UVCoord " <> show u

-- | Create UV coordinate, clamped to [0,1]
uvCoord :: Number -> UVCoord
uvCoord n
  | n < 0.0 = UVCoord 0.0
  | n > 1.0 = UVCoord 1.0
  | otherwise = UVCoord n

-- | Extract raw value
unwrapUVCoord :: UVCoord -> Number
unwrapUVCoord (UVCoord u) = u

-- | Bounds documentation
uvCoordBounds :: NumberBounds
uvCoordBounds = numberBounds 0.0 1.0 "uvCoord" "Texture coordinate in [0,1]"

-- | Normalized color channel [0,1]
-- |
-- | Linear color space channel value. Used for HDR-capable color representation.
newtype NormalizedChannel = NormalizedChannel Number

derive instance eqNormalizedChannel :: Eq NormalizedChannel
derive instance ordNormalizedChannel :: Ord NormalizedChannel

instance showNormalizedChannel :: Show NormalizedChannel where
  show (NormalizedChannel c) = "NormalizedChannel " <> show c

-- | Create normalized channel, clamped to [0,1]
normalizedChannel :: Number -> NormalizedChannel
normalizedChannel n
  | n < 0.0 = NormalizedChannel 0.0
  | n > 1.0 = NormalizedChannel 1.0
  | otherwise = NormalizedChannel n

-- | Extract raw value
unwrapNormalizedChannel :: NormalizedChannel -> Number
unwrapNormalizedChannel (NormalizedChannel c) = c

-- | Bounds documentation
normalizedChannelBounds :: NumberBounds
normalizedChannelBounds = numberBounds 0.0 1.0 "normalizedChannel" "Linear color channel in [0,1]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // positive // numbers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light intensity [0,∞)
-- |
-- | Measured in candelas or relative units. Zero means no light.
-- | Unbounded above for HDR lighting.
newtype Intensity = Intensity Number

derive instance eqIntensity :: Eq Intensity
derive instance ordIntensity :: Ord Intensity

instance showIntensity :: Show Intensity where
  show (Intensity i) = "Intensity " <> show i

-- | Create intensity, clamped to [0,∞)
intensity :: Number -> Intensity
intensity n
  | n < 0.0 = Intensity 0.0
  | otherwise = Intensity n

-- | Extract raw value
unwrapIntensity :: Intensity -> Number
unwrapIntensity (Intensity i) = i

-- | Bounds documentation (upper bound is practical maximum)
intensityBounds :: NumberBounds
intensityBounds = numberBounds 0.0 100000.0 "intensity" "Light intensity in candelas [0,∞)"

-- | Radius [0,∞)
-- |
-- | Distance from center in world units. Used for light attenuation,
-- | sphere colliders, particle systems.
newtype Radius = Radius Number

derive instance eqRadius :: Eq Radius
derive instance ordRadius :: Ord Radius

instance showRadius :: Show Radius where
  show (Radius r) = "Radius " <> show r

-- | Create radius, clamped to [0,∞)
radius :: Number -> Radius
radius n
  | n < 0.0 = Radius 0.0
  | otherwise = Radius n

-- | Extract raw value
unwrapRadius :: Radius -> Number
unwrapRadius (Radius r) = r

-- | Bounds documentation
radiusBounds :: NumberBounds
radiusBounds = numberBounds 0.0 10000.0 "radius" "Radius in world units [0,∞)"

-- | Distance [0,∞)
-- |
-- | Positive distance measurement in world units. Used for ray t-values,
-- | shadow epsilon, attenuation calculations.
newtype Distance = Distance Number

derive instance eqDistance :: Eq Distance
derive instance ordDistance :: Ord Distance

instance showDistance :: Show Distance where
  show (Distance d) = "Distance " <> show d

-- | Create distance, clamped to [0,∞)
distance :: Number -> Distance
distance n
  | n < 0.0 = Distance 0.0
  | otherwise = Distance n

-- | Extract raw value
unwrapDistance :: Distance -> Number
unwrapDistance (Distance d) = d

-- | Bounds documentation
distanceBounds :: NumberBounds
distanceBounds = numberBounds 0.0 10000.0 "distance" "Distance in world units [0,∞)"

-- | Index of Refraction [1,∞)
-- |
-- | Ratio of light speed in vacuum to speed in medium.
-- | - Air: ~1.0003
-- | - Water: ~1.33
-- | - Glass: ~1.5
-- | - Diamond: ~2.42
newtype IOR = IOR Number

derive instance eqIOR :: Eq IOR
derive instance ordIOR :: Ord IOR

instance showIOR :: Show IOR where
  show (IOR i) = "IOR " <> show i

-- | Create IOR, clamped to [1,∞)
ior :: Number -> IOR
ior n
  | n < 1.0 = IOR 1.0
  | otherwise = IOR n

-- | Extract raw value
unwrapIOR :: IOR -> Number
unwrapIOR (IOR i) = i

-- | Bounds documentation
iorBounds :: NumberBounds
iorBounds = numberBounds 1.0 10.0 "ior" "Index of refraction [1,∞)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // angles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cone angle in radians [0, π]
-- |
-- | Used for spotlight inner/outer cone angles.
-- | 0 = infinitely narrow beam, π = hemisphere
newtype ConeAngle = ConeAngle Number

derive instance eqConeAngle :: Eq ConeAngle
derive instance ordConeAngle :: Ord ConeAngle

instance showConeAngle :: Show ConeAngle where
  show (ConeAngle a) = "ConeAngle " <> show a <> " rad"

-- | Create cone angle, clamped to [0, π]
-- | π ≈ 3.14159
coneAngle :: Number -> ConeAngle
coneAngle n
  | n < 0.0 = ConeAngle 0.0
  | n > 3.14159 = ConeAngle 3.14159
  | otherwise = ConeAngle n

-- | Extract raw value in radians
unwrapConeAngle :: ConeAngle -> Number
unwrapConeAngle (ConeAngle a) = a

-- | Bounds documentation
coneAngleBounds :: NumberBounds
coneAngleBounds = numberBounds 0.0 3.14159 "coneAngle" "Cone angle in radians [0, π]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pixel dimension [1, ∞)
-- |
-- | Width or height in pixels. Must be at least 1.
newtype PixelDimension = PixelDimension Int

derive instance eqPixelDimension :: Eq PixelDimension
derive instance ordPixelDimension :: Ord PixelDimension

instance showPixelDimension :: Show PixelDimension where
  show (PixelDimension d) = "PixelDimension " <> show d <> "px"

-- | Create pixel dimension, clamped to [1, ∞)
pixelDimension :: Int -> PixelDimension
pixelDimension n
  | n < 1 = PixelDimension 1
  | otherwise = PixelDimension n

-- | Extract raw value
unwrapPixelDimension :: PixelDimension -> Int
unwrapPixelDimension (PixelDimension d) = d

-- | Bounds documentation
pixelDimensionBounds :: IntBounds
pixelDimensionBounds = intBounds 1 16384 "pixelDimension" "Dimension in pixels [1, 16384]"

-- | Tile count [1, ∞)
-- |
-- | Number of tiles in tiled/clustered rendering. Must be at least 1.
newtype TileCount = TileCount Int

derive instance eqTileCount :: Eq TileCount
derive instance ordTileCount :: Ord TileCount

instance showTileCount :: Show TileCount where
  show (TileCount t) = "TileCount " <> show t

-- | Create tile count, clamped to [1, ∞)
tileCount :: Int -> TileCount
tileCount n
  | n < 1 = TileCount 1
  | otherwise = TileCount n

-- | Extract raw value
unwrapTileCount :: TileCount -> Int
unwrapTileCount (TileCount t) = t

-- | Bounds documentation
tileCountBounds :: IntBounds
tileCountBounds = intBounds 1 1024 "tileCount" "Tile count [1, 1024]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // indices
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buffer index [0, ∞)
-- |
-- | Non-negative index into GPU buffers. Used for instance IDs,
-- | primitive IDs, BLAS indices.
newtype BufferIndex = BufferIndex Int

derive instance eqBufferIndex :: Eq BufferIndex
derive instance ordBufferIndex :: Ord BufferIndex

instance showBufferIndex :: Show BufferIndex where
  show (BufferIndex i) = "BufferIndex " <> show i

-- | Create buffer index, clamped to [0, ∞)
bufferIndex :: Int -> BufferIndex
bufferIndex n
  | n < 0 = BufferIndex 0
  | otherwise = BufferIndex n

-- | Extract raw value
unwrapBufferIndex :: BufferIndex -> Int
unwrapBufferIndex (BufferIndex i) = i

-- | Bounds documentation
bufferIndexBounds :: IntBounds
bufferIndexBounds = intBounds 0 2147483647 "bufferIndex" "Buffer index [0, max_int]"

-- | Bounce count [0, ∞)
-- |
-- | Number of ray bounces in path tracing. Zero means direct lighting only.
newtype BounceCount = BounceCount Int

derive instance eqBounceCount :: Eq BounceCount
derive instance ordBounceCount :: Ord BounceCount

instance showBounceCount :: Show BounceCount where
  show (BounceCount b) = "BounceCount " <> show b

-- | Create bounce count, clamped to [0, ∞)
bounceCount :: Int -> BounceCount
bounceCount n
  | n < 0 = BounceCount 0
  | otherwise = BounceCount n

-- | Extract raw value
unwrapBounceCount :: BounceCount -> Int
unwrapBounceCount (BounceCount b) = b

-- | Bounds documentation
bounceCountBounds :: IntBounds
bounceCountBounds = intBounds 0 128 "bounceCount" "Ray bounce count [0, 128]"
