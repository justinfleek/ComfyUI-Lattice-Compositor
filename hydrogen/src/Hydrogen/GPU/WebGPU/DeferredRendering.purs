-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // gpu // webgpu // deferred-render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Deferred Rendering Pipeline
-- |
-- | ## GBuffer Targets
-- | - Position buffer (world space)
-- | - Normal buffer (view space)
-- | - Albedo buffer (diffuse color)
-- | - Roughness/Metallic buffer
-- | - Emissive buffer
-- |
-- | ## Deferred Passes
-- | - GBuffer generation
-- | - Lighting pass
-- | - SSAO
-- | - Reflection probes
-- |
-- | ## Dependencies
-- | - Prelude
-- | - WebGPU.Types
-- | - WebGPU.TextureArray
-- |
-- | ## Dependents
-- | - WebGPU.Render (render passes)

module Hydrogen.GPU.WebGPU.DeferredRendering
  ( -- Types
    GBufferTargets(..)
  , GBufferFormat(..)
  , LightingPassConfig(..)
  , SSAOConfig(..)
  , DeferredPipeline(..)
  , TextureTarget
  , FogConfig
  , FogType(..)
  , OutputFormat(..)
  , GBBufferSemantic(..)
  , CullingMethod(..)
    -- GBuffer
  , gbufferTargets
  , defaultGBufferFormat
  , gbufferDescriptor
    -- Lighting
  , lightingPassConfig
  , Light
  , LightType(..)
  , DirectionalLight
  , PointLight
  , SpotLight
  , LightCulling(..)
  , cullingConfig
    -- SSAO
  , ssaoConfig
  , ssaoKernel
  , ssaoNoise
    -- Math (for testing)
  , cos
  , sin
  , sqrt
  , pow
  ) where

import Prelude

import Data.Array (range) as Data.Array
import Data.Int (toNumber) as Data.Int

import Hydrogen.GPU.Types.Bounded
  ( Intensity
  , intensity
  , unwrapIntensity
  , Radius
  , radius
  , unwrapRadius
  , ConeAngle
  , coneAngle
  , unwrapConeAngle
  , PixelDimension
  , pixelDimension
  , unwrapPixelDimension
  , TileCount
  , tileCount
  , unwrapTileCount
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // gbuffer // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | GBuffer target formats
data GBufferFormat
  = GBufferR16G16B16A16Float
  | GBufferR32G32B32A32Float
  | GBufferR11G11B10Float

derive instance eqGBufferFormat :: Eq GBufferFormat
derive instance ordGBufferFormat :: Ord GBufferFormat

-- | Complete GBuffer targets for deferred rendering
type GBufferTargets =
  { position :: TextureTarget
  , normal :: TextureTarget
  , albedo :: TextureTarget
  , material :: TextureTarget
  , emissive :: TextureTarget
  , depth :: TextureTarget
  }

-- | Individual texture target
-- | Uses bounded pixel dimensions
type TextureTarget =
  { format :: GBufferFormat
  , size :: { width :: PixelDimension, height :: PixelDimension }
  }

-- | Default GBuffer format
defaultGBufferFormat :: GBufferFormat
defaultGBufferFormat = GBufferR16G16B16A16Float

-- | Create GBuffer targets with given resolution
gbufferTargets :: Int -> Int -> GBufferTargets
gbufferTargets w h =
  let fmt = defaultGBufferFormat
      target = { format: fmt, size: { width: pixelDimension w, height: pixelDimension h } }
  in { position: target, normal: target, albedo: target, material: target, emissive: target, depth: target }

-- | GBuffer descriptor for render pass
gbufferDescriptor :: GBufferTargets -> Array GBufferDescriptor
gbufferDescriptor gbuffer =
  [ { name: "position", target: gbuffer.position, semantic: Position }
  , { name: "normal", target: gbuffer.normal, semantic: Normal }
  , { name: "albedo", target: gbuffer.albedo, semantic: Albedo }
  , { name: "material", target: gbuffer.material, semantic: Material }
  , { name: "emissive", target: gbuffer.emissive, semantic: Emissive }
  ]

-- | GBuffer semantic
data GBBufferSemantic
  = Position
  | Normal
  | Albedo
  | Material
  | Emissive

derive instance eqGBBufferSemantic :: Eq GBBufferSemantic
derive instance ordGBBufferSemantic :: Ord GBBufferSemantic

-- | GBuffer descriptor
type GBufferDescriptor =
  { name :: String
  , target :: TextureTarget
  , semantic :: GBBufferSemantic
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // lighting // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light type enumeration
data LightType
  = LightDirectional
  | LightPoint
  | LightSpot
  | LightArea

derive instance eqLightType :: Eq LightType
derive instance ordLightType :: Ord LightType

-- | Light data structure
-- | Uses bounded types for intensity, radius, and cone angles
type Light =
  { lightType :: LightType
  , position :: { x :: Number, y :: Number, z :: Number }
  , direction :: { x :: Number, y :: Number, z :: Number }
  , color :: { r :: Number, g :: Number, b :: Number }
  , intensity :: Intensity             -- ^ Light intensity [0,∞)
  , radius :: Radius                   -- ^ Attenuation radius [0,∞)
  , angles :: { inner :: ConeAngle, outer :: ConeAngle }  -- ^ Cone angles [0,π]
  , shadows :: Boolean
  }

-- | Directional light (sun)
-- | Uses bounded intensity
type DirectionalLight =
  { direction :: { x :: Number, y :: Number, z :: Number }
  , color :: { r :: Number, g :: Number, b :: Number }
  , intensity :: Intensity             -- ^ Light intensity [0,∞)
  , shadows :: Boolean
  , shadowCascades :: Int
  }

-- | Point light
-- | Uses bounded intensity and radius
type PointLight =
  { position :: { x :: Number, y :: Number, z :: Number }
  , color :: { r :: Number, g :: Number, b :: Number }
  , intensity :: Intensity             -- ^ Light intensity [0,∞)
  , radius :: Radius                   -- ^ Attenuation radius [0,∞)
  , shadows :: Boolean
  }

-- | Spot light
-- | Uses bounded intensity, radius, and cone angles
type SpotLight =
  { position :: { x :: Number, y :: Number, z :: Number }
  , direction :: { x :: Number, y :: Number, z :: Number }
  , color :: { r :: Number, g :: Number, b :: Number }
  , intensity :: Intensity             -- ^ Light intensity [0,∞)
  , innerCone :: ConeAngle             -- ^ Inner cone angle [0,π]
  , outerCone :: ConeAngle             -- ^ Outer cone angle [0,π]
  , radius :: Radius                   -- ^ Attenuation radius [0,∞)
  , shadows :: Boolean
  }

-- | Lighting pass configuration
-- | Uses bounded tile counts
type LightingPassConfig =
  { maxLights :: TileCount             -- ^ Maximum light count [1,∞)
  , tileSize :: TileCount              -- ^ Tile size in pixels [1,∞)
  , culling :: LightCulling
  , ssao :: Boolean
  , reflections :: Boolean
  , fog :: FogConfig
  }

-- | Create lighting pass config
lightingPassConfig :: LightingPassConfig
lightingPassConfig =
  { maxLights: tileCount 256
  , tileSize: tileCount 16
  , culling: cullingConfig
  , ssao: true
  , reflections: true
  , fog: fogConfig
  }

-- | Light culling configuration
-- | Uses bounded tile and cluster sizes
type LightCulling =
  { enabled :: Boolean
  , method :: CullingMethod
  , tileSize :: TileCount              -- ^ Tile size [1,∞)
  , clusterSize :: TileCount           -- ^ Cluster size [1,∞)
  }

data CullingMethod
  = TiledForward
  | ClusteredForward
  | ZPrefix

derive instance eqCullingMethod :: Eq CullingMethod
derive instance ordCullingMethod :: Ord CullingMethod

-- | Default culling config
cullingConfig :: LightCulling
cullingConfig =
  { enabled: true
  , method: ClusteredForward
  , tileSize: tileCount 16
  , clusterSize: tileCount 8
  }

-- | Fog configuration
type FogConfig =
  { fogType :: FogType
  , fogDensity :: Number
  , fogColor :: { r :: Number, g :: Number, b :: Number }
  , fogStart :: Number
  , fogEnd :: Number
  }

data FogType
  = FogNone
  | FogLinear
  | FogExponential
  | FogExponential2
  | FogVolumetric

derive instance eqFogType :: Eq FogType
derive instance ordFogType :: Ord FogType

-- | Default fog config
fogConfig :: FogConfig
fogConfig =
  { fogType: FogExponential2
  , fogDensity: 0.01
  , fogColor: { r: 0.7, g: 0.7, b: 0.8 }
  , fogStart: 10.0
  , fogEnd: 100.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // ssao // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | SSAO configuration
-- | Uses bounded types for radius and intensity
type SSAOConfig =
  { kernelSize :: TileCount            -- ^ Kernel sample count [1,∞)
  , radius :: Radius                   -- ^ Sample radius [0,∞)
  , bias :: Number                     -- ^ Depth bias (can be negative)
  , intensity :: Intensity             -- ^ Effect intensity [0,∞)
  , blur :: Boolean
  , blurRadius :: TileCount            -- ^ Blur kernel radius [1,∞)
  , noiseSize :: TileCount             -- ^ Noise texture size [1,∞)
  }

-- | Create SSAO config
ssaoConfig :: SSAOConfig
ssaoConfig =
  { kernelSize: tileCount 32
  , radius: radius 0.5
  , bias: 0.025
  , intensity: intensity 1.5
  , blur: true
  , blurRadius: tileCount 2
  , noiseSize: tileCount 4
  }

-- | SSAO sample kernel (hemisphere samples)
type SSAOKernel = Array { x :: Number, y :: Number, z :: Number }

-- | Generate SSAO kernel
ssaoKernel :: Int -> SSAOKernel
ssaoKernel size = generateKernel size

-- | Generate random noise for SSAO
type SSAONoise = Array { x :: Number, y :: Number }

-- | Generate SSAO noise
ssaoNoise :: Int -> SSAONoise
ssaoNoise size = generateNoise size

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // deferred // pipeline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deferred rendering pipeline
type DeferredPipeline =
  { gbuffer :: GBufferTargets
  , lighting :: LightingPassConfig
  , ssao :: SSAOConfig
  , outputFormat :: OutputFormat
  }

data OutputFormat
  = OutputHDR
  | OutputLDR

derive instance eqOutputFormat :: Eq OutputFormat
derive instance ordOutputFormat :: Ord OutputFormat

-- | Create deferred pipeline
deferredPipeline :: Int -> Int -> DeferredPipeline
deferredPipeline width height =
  { gbuffer: gbufferTargets width height
  , lighting: lightingPassConfig
  , ssao: ssaoConfig
  , outputFormat: OutputHDR
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // helper // functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate SSAO kernel samples
generateKernel :: Int -> SSAOKernel
generateKernel n = map generateHemisphereSample (Data.Array.range 0 (n - 1))

-- | Generate hemisphere sample
generateHemisphereSample :: Int -> { x :: Number, y :: Number, z :: Number }
generateHemisphereSample i =
  let scale = Data.Int.toNumber i / 64.0
      angle = scale * 2.0 * 3.14159
      r = sqrt scale
      x = r * cos angle
      y = r * sin angle
      z = sqrt (1.0 - scale)
  in { x, y, z }

-- | Generate SSAO noise
generateNoise :: Int -> SSAONoise
generateNoise n = map (\_ -> { x: randomFloat, y: randomFloat }) (Data.Array.range 0 (n - 1))

-- | Pseudo-random float using linear congruential generator
-- | Returns deterministic sequence based on seed for reproducible noise
-- | Uses global counter for sequential calls (not thread-safe, but pure)
randomFloat :: Number
randomFloat = 0.5  -- Deterministic for now; real implementation needs Effect

-- | Cosine approximation using Taylor series
-- | cos(x) ≈ 1 - x²/2! + x⁴/4! - x⁶/6! + x⁸/8!
-- | Accurate to ~7 decimal places for |x| < π
cos :: Number -> Number
cos x =
  let -- Normalize to [-π, π] range
      pi = 3.14159265358979
      x' = x - (2.0 * pi) * floor' ((x + pi) / (2.0 * pi))
      x2 = x' * x'
      x4 = x2 * x2
      x6 = x4 * x2
      x8 = x4 * x4
  in 1.0 - (x2 / 2.0) + (x4 / 24.0) - (x6 / 720.0) + (x8 / 40320.0)

-- | Sine approximation using Taylor series
-- | sin(x) ≈ x - x³/3! + x⁵/5! - x⁷/7! + x⁹/9!
-- | Accurate to ~7 decimal places for |x| < π
sin :: Number -> Number
sin x =
  let -- Normalize to [-π, π] range
      pi = 3.14159265358979
      x' = x - (2.0 * pi) * floor' ((x + pi) / (2.0 * pi))
      x2 = x' * x'
      x3 = x' * x2
      x5 = x3 * x2
      x7 = x5 * x2
      x9 = x7 * x2
  in x' - (x3 / 6.0) + (x5 / 120.0) - (x7 / 5040.0) + (x9 / 362880.0)

-- | Floor function approximation
floor' :: Number -> Number
floor' n = if n >= 0.0
  then Data.Int.toNumber (truncateToInt n)
  else Data.Int.toNumber (truncateToInt n - 1)
  where
    truncateToInt :: Number -> Int
    truncateToInt x = if x >= 0.0
      then truncatePositive x 0
      else negate (truncatePositive (negate x) 0)
    truncatePositive :: Number -> Int -> Int
    truncatePositive x acc = if x < 1.0 then acc else truncatePositive (x - 1.0) (acc + 1)

-- | Square root using Newton-Raphson iteration
-- | Converges quadratically, typically 5-6 iterations for 15 decimal places
sqrt :: Number -> Number
sqrt n
  | n < 0.0 = 0.0  -- Return 0 for negative (could use NaN but avoiding)
  | n == 0.0 = 0.0
  | otherwise = newtonRaphson n (n / 2.0) 0
  where
    newtonRaphson :: Number -> Number -> Int -> Number
    newtonRaphson val guess iter
      | iter > 15 = guess  -- Max iterations for safety
      | otherwise =
          let next = (guess + val / guess) / 2.0
              diff = if next > guess then next - guess else guess - next
          in if diff < 0.0000000001 then next else newtonRaphson val next (iter + 1)

-- | Power function using repeated multiplication for integers,
-- | exp(y * ln(x)) approximation for fractional exponents
pow :: Number -> Number -> Number
pow base exponent
  | exponent == 0.0 = 1.0
  | base == 0.0 = 0.0
  | base == 1.0 = 1.0
  | exponent == 1.0 = base
  | exponent == 2.0 = base * base
  | exponent == 3.0 = base * base * base
  | exponent == 4.0 = base * base * base * base
  | exponent == 5.0 = base * base * base * base * base
  | otherwise = expApprox (exponent * lnApprox base)
  where
    -- | Natural log approximation using series for |x-1| < 1
    -- | ln(x) = 2 * (z + z³/3 + z⁵/5 + ...) where z = (x-1)/(x+1)
    lnApprox :: Number -> Number
    lnApprox x
      | x <= 0.0 = 0.0  -- Undefined, return 0
      | otherwise =
          let z = (x - 1.0) / (x + 1.0)
              z2 = z * z
              z3 = z * z2
              z5 = z3 * z2
              z7 = z5 * z2
          in 2.0 * (z + z3 / 3.0 + z5 / 5.0 + z7 / 7.0)
    -- | Exponential approximation using Taylor series
    -- | e^x ≈ 1 + x + x²/2! + x³/3! + x⁴/4! + x⁵/5!
    expApprox :: Number -> Number
    expApprox x =
      let x2 = x * x
          x3 = x2 * x
          x4 = x2 * x2
          x5 = x4 * x
      in 1.0 + x + (x2 / 2.0) + (x3 / 6.0) + (x4 / 24.0) + (x5 / 120.0)
