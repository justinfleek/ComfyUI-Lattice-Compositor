-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // webgpu // raytrace
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Ray Tracing and Path Tracing Primitives
-- |
-- | ## Ray Types
-- | - Ray: origin + direction + t bounds
-- | - Hit: position + normal + material + distance
-- |
-- | ## Acceleration Structures
-- | - Top-level TLAS: instance array
-- | - Bottom-level BLAS: geometry
-- |
-- | ## Ray Categories
-- | - Primary rays: camera to scene
-- | - Shadow rays: occlusion tests (point/spot/directional)
-- | - Reflection rays: mirror/glossy surfaces
-- | - Refraction rays: transmission/glass
-- |
-- | ## Path Tracing
-- | - Bounce management
-- | - Russian roulette termination
-- | - Radiance accumulation
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Schema.Spatial (Vec3, Ray)
-- | - Shader.WGSL
-- |
-- | ## Dependents
-- | - WebGPU.Render (ray traced passes)

module Hydrogen.GPU.WebGPU.RayTracing
  ( -- Types
    Vec3(..)
  , Ray3D(..)
  , HitRecord(..)
  , HitAttribute(..)
  , MaterialPoint(..)
    -- Ray construction
  , ray3
  , rayAt
  , reverseRay
  , primaryRay
  , shadowRay
  , reflectionRay
  , refractionRay
    -- Acceleration structures
  , BLASGeometry(..)
  , BLASBuildInput(..)
  , TLASInstance(..)
  , TLASBuildInput(..)
  , AccelerationStructure(..)
  , AccelerationKind(..)
  , BuildInput(..)
  , accelerationStructure
    -- Path tracing
  , PathState(..)
  , pathState
  , PathPayload(..)
  , pathPayload
  , RadianceSample(..)
  , bounceRay
  , russianRoulette
    -- Ray flags
  , RayFlags(..)
  , combineRayFlags
  , RayMask(..)
  , rayMask
    -- Constants
  , rayTMin
  , rayTMax
  , shadowRayEpsilon
  , maxBounces
    -- Vector utilities
  , vec3Normalize
    -- Material defaults
  , defaultMaterial
    -- BRDF functions
  , lambertianBRDF
  , ggxDistribution
  , schlickFresnel
  , fresnel
    -- Material utilities
  , materialRoughness
  , materialAlpha
  , materialIOR
  , makeUV
  , extractUV
  , makeBufferIndex
  , extractBufferIndex
  ) where

import Prelude

import Data.Array (head, length, catMaybes, mapWithIndex) as Data.Array
import Data.Maybe (Maybe(..))

import Hydrogen.GPU.Types.Bounded
  ( Metallic
  , metallic
  , unwrapMetallic
  , Roughness
  , roughness
  , unwrapRoughness
  , Alpha
  , alpha
  , unwrapAlpha
  , UVCoord
  , uvCoord
  , unwrapUVCoord
  , IOR
  , ior
  , unwrapIOR
  , BufferIndex
  , bufferIndex
  , unwrapBufferIndex
  , BounceCount
  , bounceCount
  , unwrapBounceCount
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // math // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Square root approximation (Newton-Raphson)
sqrt' :: Number -> Number
sqrt' x = if x < 0.0 then 0.0 else go 1.0 x
  where
    go :: Number -> Number -> Number
    go guess val = 
      let next = (guess + val / guess) / 2.0
      in if abs (guess - next) < 0.0001 then next else go next val

-- | Absolute value
abs :: Number -> Number
abs x = if x < 0.0 then -x else x

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // vec3 // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D vector for ray tracing
newtype Vec3 = Vec3 { x :: Number, y :: Number, z :: Number }

derive instance eqVec3 :: Eq Vec3
derive instance ordVec3 :: Ord Vec3

-- | Vector arithmetic
vec3 :: Number -> Number -> Number -> Vec3
vec3 x y z = Vec3 { x, y, z }

vec3Zero :: Vec3
vec3Zero = vec3 0.0 0.0 0.0

vec3Add :: Vec3 -> Vec3 -> Vec3
vec3Add (Vec3 a) (Vec3 b) = vec3 (a.x + b.x) (a.y + b.y) (a.z + b.z)

vec3Sub :: Vec3 -> Vec3 -> Vec3
vec3Sub (Vec3 a) (Vec3 b) = vec3 (a.x - b.x) (a.y - b.y) (a.z - b.z)

vec3Mul :: Vec3 -> Number -> Vec3
vec3Mul (Vec3 a) s = vec3 (a.x * s) (a.y * s) (a.z * s)

vec3Dot :: Vec3 -> Vec3 -> Number
vec3Dot (Vec3 a) (Vec3 b) = a.x * b.x + a.y * b.y + a.z * b.z

vec3Length :: Vec3 -> Number
vec3Length v = sqrt' (vec3Dot v v)

vec3Normalize :: Vec3 -> Vec3
vec3Normalize v = vec3Mul v (1.0 / vec3Length v)

vec3Reflect :: Vec3 -> Vec3 -> Vec3
vec3Reflect v n = vec3Sub v (vec3Mul n (2.0 * vec3Dot v n))

vec3Refract :: Vec3 -> Vec3 -> Number -> Vec3
vec3Refract v n eta =
  let cosI = -vec3Dot v n
      sin2T = eta * eta * (1.0 - cosI * cosI)
  in if sin2T > 1.0 then vec3Zero
     else vec3Add (vec3Mul v eta) (vec3Mul n (eta * cosI - sqrt' (1.0 - sin2T)))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // ray // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ray for intersection testing with t bounds
type Ray3D =
  { origin :: Vec3
  , direction :: Vec3
  , tMin :: Number
  , tMax :: Number
  }

-- | Create ray with bounds
ray3 :: Vec3 -> Vec3 -> Number -> Number -> Ray3D
ray3 origin direction tmin tmax =
  { origin, direction, tMin: tmin, tMax: tmax }

-- | Ray at parameter t
rayAt :: Ray3D -> Number -> Vec3
rayAt r t = vec3Add r.origin (vec3Mul r.direction t)

-- | Reverse ray direction
reverseRay :: Ray3D -> Ray3D
reverseRay r = r { direction = vec3Mul r.direction (-1.0) }

-- | Default primary ray
primaryRay :: Ray3D
primaryRay = ray3 vec3Zero (vec3 0.0 0.0 1.0) rayTMin rayTMax

-- | Shadow ray for occlusion testing
shadowRay :: Vec3 -> Vec3 -> Ray3D
shadowRay origin direction = ray3 origin direction shadowRayEpsilon rayTMax

-- | Reflection ray for mirror surfaces
reflectionRay :: HitRecord -> Vec3 -> Ray3D
reflectionRay hit incoming =
  let reflected = vec3Reflect incoming hit.normal
  in ray3 (vec3Add hit.position (vec3Mul hit.normal shadowRayEpsilon)) reflected rayTMin rayTMax

-- | Refraction ray for transmissive surfaces
refractionRay :: HitRecord -> Vec3 -> Number -> Ray3D
refractionRay hit incoming eta =
  let refracted = vec3Refract incoming hit.normal eta
  in ray3 (vec3Add hit.position (vec3Mul hit.normal (-shadowRayEpsilon))) refracted rayTMin rayTMax

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // hit // attributes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hit record from intersection
-- | Uses bounded types for UV coordinates and buffer indices
type HitRecord =
  { position :: Vec3
  , normal :: Vec3
  , t :: Number                        -- ^ Ray parameter (can be negative for behind)
  , uv :: { u :: UVCoord, v :: UVCoord }  -- ^ Texture coordinates [0,1]
  , instanceId :: BufferIndex          -- ^ Instance index in TLAS [0,∞)
  , primitiveId :: BufferIndex         -- ^ Primitive index in BLAS [0,∞)
  , material :: MaterialPoint
  }

-- | Hit attribute for ray query
-- | Uses bounded types for UV coordinates
type HitAttribute =
  { position :: Vec3
  , normal :: Vec3
  , tangent :: Vec3
  , bitangent :: Vec3
  , uv :: { u :: UVCoord, v :: UVCoord }  -- ^ Texture coordinates [0,1]
  }

-- | Material at hit point (PBR properties)
-- | Uses bounded types to ensure valid PBR parameter ranges
type MaterialPoint =
  { baseColor :: Vec3
  , metallic :: Metallic           -- ^ [0,1] dielectric to metal
  , roughness :: Roughness         -- ^ [0,1] smooth to rough
  , reflectance :: Roughness       -- ^ [0,1] using Roughness as unit interval
  , transmission :: Alpha          -- ^ [0,1] opaque to fully transmissive
  , ior :: IOR                     -- ^ [1,∞) index of refraction
  , emissive :: Vec3
  , alpha :: Alpha                 -- ^ [0,1] transparent to opaque
  , flags :: RayFlags
  }

-- | Default material (white diffuse)
defaultMaterial :: MaterialPoint
defaultMaterial =
  { baseColor: vec3 1.0 1.0 1.0
  , metallic: metallic 0.0
  , roughness: roughness 0.5
  , reflectance: roughness 0.5
  , transmission: alpha 0.0
  , ior: ior 1.5
  , emissive: vec3Zero
  , alpha: alpha 1.0
  , flags: combineRayFlags []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // acceleration // structures
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bottom-level acceleration structure geometry type
data BLASGeometry
  = Triangles
  | AABBs
  | Procedural

derive instance eqBLASGeometry :: Eq BLASGeometry
derive instance ordBLASGeometry :: Ord BLASGeometry

-- | Build input for BLAS
type BLASBuildInput =
  { geometryType :: BLASGeometry
  , vertexCount :: BufferIndex       -- ^ Vertex count [0,∞)
  , indexCount :: BufferIndex        -- ^ Index count [0,∞)
  , primitiveCount :: BufferIndex    -- ^ Primitive count [0,∞)
  , transform :: Maybe { matrix :: Array Number }
  }

-- | Instance data for TLAS
-- | Uses bounded indices for BLAS references
type TLASInstance =
  { blasIndex :: BufferIndex         -- ^ Index into BLAS array [0,∞)
  , instanceMask :: RayMask
  , instanceFlags :: RayFlags
  , transform :: Array Number
  , customIndex :: BufferIndex       -- ^ User-defined instance ID [0,∞)
  }

-- | Build input for TLAS
type TLASBuildInput =
  { instances :: Array TLASInstance
  , forceOpaque :: Boolean
  , allowAnyHit :: Boolean
  }

-- | Acceleration structure descriptor
type AccelerationStructure =
  { kind :: AccelerationKind
  , buildInput :: BuildInput
  , size :: Int
  , alignment :: Int
  }

data AccelerationKind = BLAS | TLAS

derive instance eqAccelerationKind :: Eq AccelerationKind
derive instance ordAccelerationKind :: Ord AccelerationKind

data BuildInput = BLASInput BLASBuildInput | TLASInput TLASBuildInput

-- | Create acceleration structure descriptor
accelerationStructure :: AccelerationKind -> BuildInput -> AccelerationStructure
accelerationStructure kind buildInput =
  let sizeAlign = case kind of
        BLAS -> { size: 0, alignment: 256 }
        TLAS -> { size: 0, alignment: 256 }
  in { kind, buildInput, size: sizeAlign.size, alignment: sizeAlign.alignment }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // path // tracing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Path tracing state
type PathState =
  { bounce :: BounceCount
  -- ^ Current bounce number [0,∞)
  , throughput :: Vec3
  -- ^ Path throughput (product of BRDF and cosine terms)
  , radiance :: Vec3
  -- ^ Accumulated radiance
  , pdf :: Number
  -- ^ PDF of last sampled direction
  , flags :: RayFlags
  -- ^ Path flags
  }

-- | Create initial path state
pathState :: PathState
pathState =
  { bounce: bounceCount 0
  , throughput: vec3 1.0 1.0 1.0
  , radiance: vec3Zero
  , pdf: 1.0
  , flags: combineRayFlags []
  }

-- | Per-ray payload for path tracing
type PathPayload =
  { pixelX :: Int
  , pixelY :: Int
  , seed :: Int
  , radiance :: Vec3
  , hitT :: Number
  , flags :: RayFlags
  }

-- | Create path payload
pathPayload :: Int -> Int -> Int -> PathPayload
pathPayload px py sd =
  { pixelX: px
  , pixelY: py
  , seed: sd
  , radiance: vec3Zero
  , hitT: rayTMax
  , flags: combineRayFlags []
  }

-- | Radiance sample result
type RadianceSample =
  { radiance :: Vec3
  , pdf :: Number
  , beta :: Vec3
  -- ^ Throughput for next bounce
  , terminated :: Boolean
  }

-- | Generate next bounce ray
bounceRay :: HitRecord -> PathState -> PathState
bounceRay _hit state =
  let pdf = 1.0 / (2.0 * 3.14159)
      throughput = vec3Mul state.throughput pdf
      nextBounce = bounceCount (unwrapBounceCount state.bounce + 1)
  in state { bounce = nextBounce, throughput = throughput }

-- | Russian roulette termination
russianRoulette :: PathState -> Number -> Boolean
russianRoulette state probability =
  let survival = 1.0 - probability
      b = unwrapBounceCount state.bounce
  in if b > 2 then survival < 0.5 else false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // ray // flags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ray flags for hit group configuration
data RayFlags
  = Opaque
  | NoOpaque
  | TerminateOnFirstHit
  | SkipClosestHitShader
  | SkipAnyHitShader
  | CullBackFacingTriangles
  | CullFrontFacingTriangles
  | CullOpaque
  | CullNoOpaque
  | SkipTriangles
  | SkipAABBs

derive instance eqRayFlags :: Eq RayFlags
derive instance ordRayFlags :: Ord RayFlags

-- | Combine ray flags using priority ordering
-- | In GPU ray tracing, flags are typically combined via bitwise OR.
-- | Since we can't do bitwise ops without FFI, we use priority:
-- | - TerminateOnFirstHit takes precedence (optimization)
-- | - Culling flags take precedence over opacity
-- | - NoOpaque overrides Opaque
-- | For multiple flags, the highest priority flag wins.
combineRayFlags :: Array RayFlags -> RayFlags
combineRayFlags [] = Opaque
combineRayFlags flags = selectHighestPriority flags Opaque
  where
    selectHighestPriority :: Array RayFlags -> RayFlags -> RayFlags
    selectHighestPriority fs current = case Data.Array.head fs of
      Nothing -> current
      Just f -> 
        let rest = dropFirst fs
            next = if flagPriority f > flagPriority current then f else current
        in selectHighestPriority rest next
    
    -- Drop first element of array (safe)
    dropFirst :: Array RayFlags -> Array RayFlags
    dropFirst arr = case Data.Array.length arr of
      0 -> []
      1 -> []
      _ -> unsafeDropFirst arr
    
    -- We know array has at least 2 elements
    unsafeDropFirst :: Array RayFlags -> Array RayFlags
    unsafeDropFirst arr = Data.Array.catMaybes (Data.Array.mapWithIndex (\i x -> if i == 0 then Nothing else Just x) arr)
    
    -- Priority ordering (higher = more important)
    flagPriority :: RayFlags -> Int
    flagPriority = case _ of
      TerminateOnFirstHit -> 100      -- Highest - optimization flag
      SkipClosestHitShader -> 90
      SkipAnyHitShader -> 85
      CullBackFacingTriangles -> 80   -- Culling flags
      CullFrontFacingTriangles -> 75
      CullOpaque -> 70
      CullNoOpaque -> 65
      SkipTriangles -> 60
      SkipAABBs -> 55
      NoOpaque -> 20                  -- Opacity flags
      Opaque -> 10                    -- Default lowest

-- | Ray visibility mask for culling
newtype RayMask = RayMask Int

derive instance eqRayMask :: Eq RayMask
derive instance ordRayMask :: Ord RayMask

-- | Create ray mask
rayMask :: Int -> RayMask
rayMask = RayMask

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum ray t value (avoid self-intersection)
rayTMin :: Number
rayTMin = 0.001

-- | Maximum ray t value (infinity representation)
rayTMax :: Number
rayTMax = 1.0e38

-- | Small offset to avoid self-intersection
shadowRayEpsilon :: Number
shadowRayEpsilon = 0.001

-- | Maximum number of bounces
maxBounces :: Int
maxBounces = 16

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // shading // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lambertian BRDF
lambertianBRDF :: MaterialPoint -> Vec3
lambertianBRDF mat = vec3Mul mat.baseColor (1.0 / 3.14159)

-- | GGX/Trowbridge-Reitz normal distribution
-- | wh: half vector, n: surface normal, roughnessValue: material roughness [0,1]
-- | Note: alpha (roughness squared) is computed internally for correct distribution
ggxDistribution :: Vec3 -> Vec3 -> Number -> Number
ggxDistribution wh n roughnessValue =
  let nDotH = vec3Dot n wh
      -- Alpha is roughness squared, clamped to avoid singularity at 0
      alpha = max 0.001 (roughnessValue * roughnessValue)
      alpha2 = alpha * alpha
      denom = nDotH * nDotH * (alpha2 - 1.0) + 1.0
  in alpha2 / (3.14159 * denom * denom)

-- | Schlick Fresnel approximation
schlickFresnel :: Number -> Number -> Number
schlickFresnel cosTheta f0 = f0 + (1.0 - f0) * pow (1.0 - cosTheta) 5.0

-- | Power function (helper)
-- | Uses repeated multiplication for integer exponents, approximation for fractional
pow :: Number -> Number -> Number
pow base exponent
  | exponent == 0.0 = 1.0
  | exponent == 1.0 = base
  | exponent == 2.0 = base * base
  | exponent == 3.0 = base * base * base
  | exponent == 4.0 = base * base * base * base
  | exponent == 5.0 = base * base * base * base * base  -- Used by Schlick Fresnel
  | otherwise = powApprox base exponent
  where
    -- | Taylor series approximation: base^exp = e^(exp * ln(base))
    -- | For positive base, using ln(1+x) ≈ x - x²/2 + x³/3 for |x| < 1
    powApprox :: Number -> Number -> Number
    powApprox b e
      | b <= 0.0 = 0.0  -- Avoid negative/zero base issues
      | b == 1.0 = 1.0
      | otherwise =
          -- Use exp(e * ln(b)) approximation
          -- ln(b) for b near 1: ln(1+x) ≈ x where x = b - 1
          let x = b - 1.0
              -- For |x| < 1, ln(1+x) ≈ x - x²/2 + x³/3
              lnApprox = x - (x * x / 2.0) + (x * x * x / 3.0)
              -- exp(y) ≈ 1 + y + y²/2 + y³/6 for small y
              y = e * lnApprox
          in 1.0 + y + (y * y / 2.0) + (y * y * y / 6.0)

-- | Calculate Fresnel reflectance using Schlick approximation
-- | Returns RGB fresnel term based on material's F0 (reflectance at normal incidence)
fresnel :: MaterialPoint -> Number -> Vec3
fresnel mat cosTheta =
  let -- F0 is the reflectance at normal incidence, interpolated between dielectric (0.04) and metal (baseColor)
      dielectricF0 = vec3 0.04 0.04 0.04
      m = unwrapMetallic mat.metallic  -- Extract bounded metallic value
      f0 = vec3Add (vec3Mul dielectricF0 (1.0 - m)) (vec3Mul mat.baseColor m)
      -- Schlick approximation: F = F0 + (1 - F0) * (1 - cosTheta)^5
      oneMinusCos = 1.0 - cosTheta
      oneMinusCos5 = pow oneMinusCos 5.0
      oneMinusF0 = vec3Sub (vec3 1.0 1.0 1.0) f0
  in vec3Add f0 (vec3Mul oneMinusF0 oneMinusCos5)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // material // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract roughness value from material
materialRoughness :: MaterialPoint -> Number
materialRoughness mat = unwrapRoughness mat.roughness

-- | Extract alpha (opacity) value from material
materialAlpha :: MaterialPoint -> Number
materialAlpha mat = unwrapAlpha mat.alpha

-- | Extract index of refraction from material
materialIOR :: MaterialPoint -> Number
materialIOR mat = unwrapIOR mat.ior

-- | Create UV coordinate from a number (clamped to [0,1])
makeUV :: Number -> UVCoord
makeUV = uvCoord

-- | Extract UV coordinate value
extractUV :: UVCoord -> Number
extractUV = unwrapUVCoord

-- | Create buffer index with bounds checking
makeBufferIndex :: Int -> BufferIndex
makeBufferIndex = bufferIndex

-- | Extract raw buffer index value
extractBufferIndex :: BufferIndex -> Int
extractBufferIndex = unwrapBufferIndex