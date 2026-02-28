-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // schema // spatial // scenegraph // environment
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scene Environment — Global rendering settings.
-- |
-- | ## Skybox
-- | Background rendering: cubemap, procedural sky, or solid color.
-- |
-- | ## Fog
-- | Distance-based atmospheric effect. Linear, exponential, or height-based.
-- |
-- | ## PostProcess
-- | Screen-space effects applied after rendering.
-- | Bloom, color grading, anti-aliasing, etc.
-- |
-- | ## Environment
-- | Complete environment configuration combining all settings.

module Hydrogen.Schema.Spatial.SceneGraph.Environment
  ( -- * Skybox
    SkyboxType(..)
  , Skybox(..)
  , cubemapSkybox
  , proceduralSky
  , solidColorSkybox
  
  -- * Fog
  , FogType(..)
  , Fog(..)
  , linearFog
  , exponentialFog
  , heightFog
  , noFog
  
  -- * Post-Processing
  , ToneMappingMode(..)
  , AntiAliasMode(..)
  , BloomSettings(..)
  , ColorGrading(..)
  , PostProcess(..)
  , defaultPostProcess
  
  -- * Environment
  , AmbientMode(..)
  , Environment(..)
  , defaultEnvironment
  , outdoorEnvironment
  , studioEnvironment
  
  -- * Accessors
  , environmentSkybox
  , environmentFog
  , environmentAmbientColor
  , environmentExposure
  , skyboxCubemapId
  , ambientIBLId
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // skybox
-- ═════════════════════════════════════════════════════════════════════════════

-- | Skybox rendering type
data SkyboxType
  = SkyboxCubemap String            -- ^ Cubemap texture ID
  | SkyboxProcedural                -- ^ Procedural sky (sun position, etc.)
  | SkyboxSolidColor (Vec3 Number)  -- ^ Flat color background
  | SkyboxGradient (Vec3 Number) (Vec3 Number)  -- ^ Top to bottom gradient
  | SkyboxNone                      -- ^ Transparent/no background

derive instance eqSkyboxType :: Eq SkyboxType

instance showSkyboxType :: Show SkyboxType where
  show (SkyboxCubemap id) = "Cubemap:" <> id
  show SkyboxProcedural = "Procedural"
  show (SkyboxSolidColor _) = "SolidColor"
  show (SkyboxGradient _ _) = "Gradient"
  show SkyboxNone = "None"

-- | Skybox configuration
newtype Skybox = Skybox
  { skyType :: SkyboxType
  , rotation :: Number              -- ^ Y-axis rotation (radians)
  , intensity :: Number             -- ^ Brightness multiplier
  , blur :: Number                  -- ^ Mip level for reflections (0-1)
  }

derive instance eqSkybox :: Eq Skybox

instance showSkybox :: Show Skybox where
  show (Skybox s) = "Skybox { type: " <> show s.skyType <> " }"

-- | Create cubemap skybox
cubemapSkybox :: String -> Skybox
cubemapSkybox textureId = Skybox
  { skyType: SkyboxCubemap textureId
  , rotation: 0.0
  , intensity: 1.0
  , blur: 0.0
  }

-- | Create procedural sky
proceduralSky :: Skybox
proceduralSky = Skybox
  { skyType: SkyboxProcedural
  , rotation: 0.0
  , intensity: 1.0
  , blur: 0.0
  }

-- | Create solid color skybox
solidColorSkybox :: Vec3 Number -> Skybox
solidColorSkybox color = Skybox
  { skyType: SkyboxSolidColor color
  , rotation: 0.0
  , intensity: 1.0
  , blur: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // fog
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fog calculation type
data FogType
  = FogLinear                       -- ^ Linear falloff (near to far)
  | FogExponential                  -- ^ Exponential falloff
  | FogExponentialSquared           -- ^ Exponential squared (denser)
  | FogHeight                       -- ^ Height-based (ground fog)

derive instance eqFogType :: Eq FogType
derive instance ordFogType :: Ord FogType

instance showFogType :: Show FogType where
  show FogLinear = "Linear"
  show FogExponential = "Exponential"
  show FogExponentialSquared = "ExponentialSquared"
  show FogHeight = "Height"

-- | Fog configuration
newtype Fog = Fog
  { enabled :: Boolean
  , fogType :: FogType
  , color :: Vec3 Number            -- ^ Fog color (linear RGB)
  , near :: Number                  -- ^ Start distance (linear) or density
  , far :: Number                   -- ^ End distance (linear) or falloff
  , height :: Number                -- ^ Ground level (height fog)
  , density :: Number               -- ^ Density factor (exponential)
  }

derive instance eqFog :: Eq Fog

instance showFog :: Show Fog where
  show (Fog f) =
    "Fog { type: " <> show f.fogType <>
    ", enabled: " <> show f.enabled <> " }"

-- | Create linear fog
linearFog :: Vec3 Number -> Number -> Number -> Fog
linearFog color near far = Fog
  { enabled: true
  , fogType: FogLinear
  , color
  , near
  , far
  , height: 0.0
  , density: 0.0
  }

-- | Create exponential fog
exponentialFog :: Vec3 Number -> Number -> Fog
exponentialFog color density = Fog
  { enabled: true
  , fogType: FogExponential
  , color
  , near: 0.0
  , far: 0.0
  , height: 0.0
  , density
  }

-- | Create height-based fog
heightFog :: Vec3 Number -> Number -> Number -> Fog
heightFog color height density = Fog
  { enabled: true
  , fogType: FogHeight
  , color
  , near: 0.0
  , far: 0.0
  , height
  , density
  }

-- | No fog
noFog :: Fog
noFog = Fog
  { enabled: false
  , fogType: FogLinear
  , color: vec3 1.0 1.0 1.0
  , near: 0.0
  , far: 1000.0
  , height: 0.0
  , density: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // post-processing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tone mapping operator
data ToneMappingMode
  = ToneLinear                      -- ^ No tone mapping
  | ToneReinhard                    -- ^ Simple Reinhard
  | ToneACES                        -- ^ ACES filmic
  | ToneFilmic                      -- ^ Uncharted 2 filmic
  | ToneAgX                         -- ^ AgX (Blender 4.0+)

derive instance eqToneMappingMode :: Eq ToneMappingMode
derive instance ordToneMappingMode :: Ord ToneMappingMode

instance showToneMappingMode :: Show ToneMappingMode where
  show ToneLinear = "Linear"
  show ToneReinhard = "Reinhard"
  show ToneACES = "ACES"
  show ToneFilmic = "Filmic"
  show ToneAgX = "AgX"

-- | Anti-aliasing mode
data AntiAliasMode
  = AANone                          -- ^ No anti-aliasing
  | AAFXAA                          -- ^ Fast approximate AA
  | AASMAA                          -- ^ Subpixel morphological AA
  | AATAA                           -- ^ Temporal AA
  | AAMSAA Int                      -- ^ Multisample AA (2, 4, 8)

derive instance eqAntiAliasMode :: Eq AntiAliasMode

instance showAntiAliasMode :: Show AntiAliasMode where
  show AANone = "None"
  show AAFXAA = "FXAA"
  show AASMAA = "SMAA"
  show AATAA = "TAA"
  show (AAMSAA n) = "MSAA" <> show n <> "x"

-- | Bloom effect settings
type BloomSettings =
  { enabled :: Boolean
  , intensity :: Number             -- ^ Bloom strength (0-1)
  , threshold :: Number             -- ^ Brightness threshold
  , radius :: Number                -- ^ Blur radius
  }

-- | Color grading settings
type ColorGrading =
  { enabled :: Boolean
  , saturation :: Number            -- ^ 0 = grayscale, 1 = normal, 2 = vivid
  , contrast :: Number              -- ^ 0 = flat, 1 = normal
  , brightness :: Number            -- ^ Additive brightness
  , gamma :: Number                 -- ^ Gamma correction
  , lift :: Vec3 Number             -- ^ Shadow color shift
  , gain :: Vec3 Number             -- ^ Highlight color shift
  }

-- | Post-processing stack
newtype PostProcess = PostProcess
  { toneMapping :: ToneMappingMode
  , exposure :: Number              -- ^ Exposure value
  , antiAliasing :: AntiAliasMode
  , bloom :: BloomSettings
  , colorGrading :: ColorGrading
  , vignetteIntensity :: Number     -- ^ Edge darkening (0-1)
  , chromaticAberration :: Number   -- ^ Color fringing (0-1)
  , filmGrain :: Number             -- ^ Noise amount (0-1)
  }

derive instance eqPostProcess :: Eq PostProcess

instance showPostProcess :: Show PostProcess where
  show (PostProcess p) =
    "PostProcess { toneMapping: " <> show p.toneMapping <>
    ", exposure: " <> show p.exposure <> " }"

-- | Default post-processing (minimal)
defaultPostProcess :: PostProcess
defaultPostProcess = PostProcess
  { toneMapping: ToneACES
  , exposure: 1.0
  , antiAliasing: AAFXAA
  , bloom: { enabled: false, intensity: 0.5, threshold: 0.9, radius: 0.5 }
  , colorGrading:
      { enabled: false
      , saturation: 1.0
      , contrast: 1.0
      , brightness: 0.0
      , gamma: 1.0
      , lift: vec3 0.0 0.0 0.0
      , gain: vec3 1.0 1.0 1.0
      }
  , vignetteIntensity: 0.0
  , chromaticAberration: 0.0
  , filmGrain: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // environment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ambient lighting mode
data AmbientMode
  = AmbientFlat (Vec3 Number)       -- ^ Flat ambient color
  | AmbientHemisphere (Vec3 Number) (Vec3 Number)  -- ^ Sky/ground colors
  | AmbientIBL String               -- ^ Image-based lighting (cubemap ID)

derive instance eqAmbientMode :: Eq AmbientMode

instance showAmbientMode :: Show AmbientMode where
  show (AmbientFlat _) = "Flat"
  show (AmbientHemisphere _ _) = "Hemisphere"
  show (AmbientIBL id) = "IBL:" <> id

-- | Complete environment configuration
newtype Environment = Environment
  { skybox :: Skybox
  , fog :: Fog
  , ambient :: AmbientMode
  , ambientIntensity :: Number      -- ^ Ambient brightness
  , postProcess :: PostProcess
  , shadowsEnabled :: Boolean
  , reflectionsEnabled :: Boolean
  }

derive instance eqEnvironment :: Eq Environment

instance showEnvironment :: Show Environment where
  show (Environment e) =
    "Environment { skybox: " <> show e.skybox <>
    ", fog: " <> show e.fog <>
    ", ambient: " <> show e.ambient <> " }"

-- | Default environment (neutral studio)
defaultEnvironment :: Environment
defaultEnvironment = Environment
  { skybox: solidColorSkybox (vec3 0.1 0.1 0.1)
  , fog: noFog
  , ambient: AmbientFlat (vec3 0.2 0.2 0.2)
  , ambientIntensity: 1.0
  , postProcess: defaultPostProcess
  , shadowsEnabled: true
  , reflectionsEnabled: true
  }

-- | Outdoor environment preset
outdoorEnvironment :: String -> Environment
outdoorEnvironment skyboxId = Environment
  { skybox: cubemapSkybox skyboxId
  , fog: linearFog (vec3 0.7 0.8 0.9) 100.0 1000.0
  , ambient: AmbientIBL skyboxId
  , ambientIntensity: 0.5
  , postProcess: defaultPostProcess
  , shadowsEnabled: true
  , reflectionsEnabled: true
  }

-- | Studio environment preset
studioEnvironment :: Environment
studioEnvironment = Environment
  { skybox: solidColorSkybox (vec3 0.18 0.18 0.18)
  , fog: noFog
  , ambient: AmbientHemisphere (vec3 0.3 0.3 0.35) (vec3 0.1 0.1 0.08)
  , ambientIntensity: 0.8
  , postProcess: defaultPostProcess
  , shadowsEnabled: true
  , reflectionsEnabled: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get environment skybox
environmentSkybox :: Environment -> Skybox
environmentSkybox (Environment e) = e.skybox

-- | Get environment fog
environmentFog :: Environment -> Fog
environmentFog (Environment e) = e.fog

-- | Get ambient color (simplified, for flat/hemisphere)
environmentAmbientColor :: Environment -> Vec3 Number
environmentAmbientColor (Environment e) =
  case e.ambient of
    AmbientFlat color -> color
    AmbientHemisphere sky _ -> sky  -- Return sky color as primary
    AmbientIBL _ -> vec3 1.0 1.0 1.0  -- Neutral for IBL

-- | Get environment exposure
environmentExposure :: Environment -> Number
environmentExposure (Environment e) =
  let (PostProcess p) = e.postProcess
  in p.exposure

-- | Get skybox cubemap ID if present
-- |
-- | Returns Just the ID if skybox is a cubemap, Nothing otherwise.
skyboxCubemapId :: Skybox -> Maybe String
skyboxCubemapId (Skybox s) = case s.skyType of
  SkyboxCubemap id -> Just id
  _ -> Nothing

-- | Get ambient IBL cubemap ID if present
-- |
-- | Returns Just the ID if ambient mode is IBL, Nothing otherwise.
ambientIBLId :: Environment -> Maybe String
ambientIBLId (Environment e) = case e.ambient of
  AmbientIBL id -> Just id
  _ -> Nothing
