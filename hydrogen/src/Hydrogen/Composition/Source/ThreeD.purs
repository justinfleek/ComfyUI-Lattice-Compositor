-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // composition // source // threed
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D Sources — Model, PointCloud, Camera, Light, Particles.
-- |
-- | 3D assets rendered to 2D output.

module Hydrogen.Composition.Source.ThreeD
  ( -- * Model
    ModelSpec
  , ModelFormat(..)
  , model
  
  -- * Point Cloud
  , PointCloudSpec
  , PointCloudFormat(..)
  , PointCloudColoring(..)
  , pointCloud
  
  -- * Camera
  , CameraSpec
  , CameraType(..)
  , camera
  
  -- * Light
  , LightSpec
  , LightType(..)
  , light
  
  -- * Particle System
  , ParticleSystemSpec
  , EmitterShape(..)
  , ParticleForce(..)
  , particleSystem
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  )

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Color.Opacity (Opacity)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // model
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D model format.
data ModelFormat
  = FormatGLTF
  | FormatGLB
  | FormatOBJ
  | FormatFBX
  | FormatUSD
  | FormatDAE

derive instance eqModelFormat :: Eq ModelFormat

instance showModelFormat :: Show ModelFormat where
  show FormatGLTF = "gltf"
  show FormatGLB = "glb"
  show FormatOBJ = "obj"
  show FormatFBX = "fbx"
  show FormatUSD = "usd"
  show FormatDAE = "dae"

-- | 3D model source.
type ModelSpec =
  { assetId :: String
  , format :: ModelFormat
  , opacity :: Opacity
  , animation :: Maybe String   -- Animation name to play
  , animationTime :: Number     -- Animation time
  , castShadows :: Boolean
  , receiveShadows :: Boolean
  }

-- | Create a model source.
model :: String -> ModelFormat -> Opacity -> ModelSpec
model assetId format opacity =
  { assetId, format, opacity
  , animation: Nothing, animationTime: 0.0
  , castShadows: true, receiveShadows: true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // point cloud
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Point cloud format.
data PointCloudFormat
  = FormatPLY
  | FormatPCD
  | FormatLAS
  | FormatLAZ
  | FormatXYZ

derive instance eqPointCloudFormat :: Eq PointCloudFormat

instance showPointCloudFormat :: Show PointCloudFormat where
  show FormatPLY = "ply"
  show FormatPCD = "pcd"
  show FormatLAS = "las"
  show FormatLAZ = "laz"
  show FormatXYZ = "xyz"

-- | Point cloud coloring mode.
data PointCloudColoring
  = ColoringRGB           -- Use embedded colors
  | ColoringHeight        -- Color by height
  | ColoringIntensity     -- Color by intensity
  | ColoringNormal        -- Color by normal direction
  | ColoringSolid RGB     -- Single solid color

derive instance eqPointCloudColoring :: Eq PointCloudColoring

instance showPointCloudColoring :: Show PointCloudColoring where
  show ColoringRGB = "rgb"
  show ColoringHeight = "height"
  show ColoringIntensity = "intensity"
  show ColoringNormal = "normal"
  show (ColoringSolid _) = "solid"

-- | Point cloud source.
type PointCloudSpec =
  { assetId :: String
  , format :: PointCloudFormat
  , coloring :: PointCloudColoring
  , pointSize :: Number         -- Point size in pixels
  , opacity :: Opacity
  , lodEnabled :: Boolean       -- Level of detail
  , maxPoints :: Int            -- Max points to render
  }

-- | Create a point cloud source.
pointCloud :: String -> PointCloudFormat -> PointCloudColoring -> Number -> Opacity -> PointCloudSpec
pointCloud assetId format coloring pointSize opacity =
  { assetId, format, coloring, pointSize, opacity
  , lodEnabled: true, maxPoints: 1000000 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // camera
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Camera type.
data CameraType
  = CameraOneNode       -- Position only
  | CameraTwoNode       -- Position + target

derive instance eqCameraType :: Eq CameraType

instance showCameraType :: Show CameraType where
  show CameraOneNode = "one_node"
  show CameraTwoNode = "two_node"

-- | Camera source (renders 3D scene from camera POV).
type CameraSpec =
  { cameraType :: CameraType
  , fov :: Number               -- Field of view (degrees)
  , nearClip :: Number
  , farClip :: Number
  , dofEnabled :: Boolean       -- Depth of field
  , dofFocusDistance :: Number
  , dofAperture :: Number
  , opacity :: Opacity
  }

-- | Create a camera source.
camera :: CameraType -> Number -> Opacity -> CameraSpec
camera cameraType fov opacity =
  { cameraType, fov, opacity
  , nearClip: 0.1, farClip: 10000.0
  , dofEnabled: false, dofFocusDistance: 100.0, dofAperture: 2.8 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // light
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Light type.
data LightType
  = LightPoint        -- Omnidirectional
  | LightSpot         -- Cone-shaped
  | LightDirectional  -- Sun-like parallel rays
  | LightAmbient      -- Global fill
  | LightArea         -- Rectangle/disc emitter

derive instance eqLightType :: Eq LightType

instance showLightType :: Show LightType where
  show LightPoint = "point"
  show LightSpot = "spot"
  show LightDirectional = "directional"
  show LightAmbient = "ambient"
  show LightArea = "area"

-- | Light source.
type LightSpec =
  { lightType :: LightType
  , color :: RGB
  , intensity :: Number
  , castShadows :: Boolean
  , shadowSoftness :: Number
  , coneAngle :: Number         -- For spot lights
  , opacity :: Opacity
  }

-- | Create a light source.
light :: LightType -> RGB -> Number -> Opacity -> LightSpec
light lightType color intensity opacity =
  { lightType, color, intensity, opacity
  , castShadows: true, shadowSoftness: 0.5, coneAngle: 45.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // particle system
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Emitter shape.
data EmitterShape
  = EmitPoint
  | EmitLine
  | EmitCircle
  | EmitBox
  | EmitSphere
  | EmitCone
  | EmitMesh String       -- Emit from mesh surface
  | EmitDepthMap String   -- Emit based on depth values
  | EmitMask String       -- Emit from mask

derive instance eqEmitterShape :: Eq EmitterShape

instance showEmitterShape :: Show EmitterShape where
  show EmitPoint = "point"
  show EmitLine = "line"
  show EmitCircle = "circle"
  show EmitBox = "box"
  show EmitSphere = "sphere"
  show EmitCone = "cone"
  show (EmitMesh _) = "mesh"
  show (EmitDepthMap _) = "depth_map"
  show (EmitMask _) = "mask"

-- | Particle force type.
data ParticleForce
  = ForceGravity Number         -- Gravity strength
  | ForceWind Number Number     -- Direction and strength
  | ForceTurbulence Number      -- Turbulence strength
  | ForceVortex Number          -- Vortex strength
  | ForceAttractor Number       -- Attractor strength

derive instance eqParticleForce :: Eq ParticleForce

instance showParticleForce :: Show ParticleForce where
  show (ForceGravity _) = "gravity"
  show (ForceWind _ _) = "wind"
  show (ForceTurbulence _) = "turbulence"
  show (ForceVortex _) = "vortex"
  show (ForceAttractor _) = "attractor"

-- | Particle system source.
type ParticleSystemSpec =
  { emitterShape :: EmitterShape
  , birthRate :: Number         -- Particles per second
  , lifetime :: Number          -- Particle lifetime (seconds)
  , startSize :: Number
  , endSize :: Number
  , startColor :: RGB
  , endColor :: RGB
  , startOpacity :: Number
  , endOpacity :: Number
  , forces :: Array ParticleForce
  , opacity :: Opacity
  , maxParticles :: Int
  , motionBlur :: Boolean
  }

-- | Create a particle system source.
particleSystem :: EmitterShape -> Number -> Number -> RGB -> Opacity -> ParticleSystemSpec
particleSystem emitterShape birthRate lifetime startColor opacity =
  { emitterShape, birthRate, lifetime, opacity
  , startSize: 10.0, endSize: 0.0
  , startColor, endColor: startColor
  , startOpacity: 1.0, endOpacity: 0.0
  , forces: [], maxParticles: 10000, motionBlur: false }
