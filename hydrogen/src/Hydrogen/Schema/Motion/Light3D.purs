-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // motion // light-3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Light3D — 3D Light layer for motion graphics compositions.
-- |
-- | Integrates `Schema.Spatial.Light.Types` with the Motion layer system,
-- | adding After Effects-specific properties and layer behavior.
-- |
-- | ## After Effects Light Types
-- |
-- | - **Parallel** (Directional): Sun-like, infinite distance, parallel rays
-- | - **Spot**: Cone-shaped with inner/outer angle and feather
-- | - **Point**: Omnidirectional bulb-like light
-- | - **Ambient**: Base illumination, no direction or position
-- |
-- | ## Architecture
-- |
-- | Mirrors `Lattice.Light3D` from the Haskell backend. The Spatial.Light
-- | module provides the rendering primitives; this module provides the
-- | layer-level properties for animation and composition.
-- |
-- | ## Properties (After Effects Parity)
-- |
-- | - Light type (Parallel, Spot, Point, Ambient)
-- | - Color (SRGB, animatable)
-- | - Intensity (0-400%, animatable)
-- | - Cone Angle (Spot only, 0-180 degrees)
-- | - Cone Feather (Spot only, 0-100%)
-- | - Falloff (None, Smooth, Inverse Square Clamped)
-- | - Falloff Distance (for Smooth/ISC falloff)
-- | - Shadow settings (darkness, diffusion, on/off/only)
-- | - Accepts Shadows (per-layer property)
-- | - Accepts Lights (per-layer property)

module Hydrogen.Schema.Motion.Light3D
  ( -- * Light3D Type
    Light3D(..)
  , defaultLight3D
  , mkLight3D
  
  -- * Light3D ID
  , Light3DId(..)
  , mkLight3DId
  
  -- * Light Type
  , Light3DType(..)
  , allLight3DTypes
  , light3DTypeToString
  , light3DTypeFromString
  , isDirectional
  , isSpot
  , isPoint
  , isAmbient
  
  -- * Falloff Mode
  , LightFalloff(..)
  , allLightFalloffs
  , lightFalloffToString
  , lightFalloffFromString
  
  -- * Shadow Mode
  , ShadowMode(..)
  , allShadowModes
  , shadowModeToString
  , shadowModeFromString
  
  -- * Shadow Settings
  , LightShadowSettings(..)
  , defaultShadowSettings
  , shadowsOff
  , shadowsOn
  , shadowsOnly
  
  -- * Cone Settings (Spot Only)
  , ConeSettings(..)
  , defaultConeSettings
  , mkConeSettings
  
  -- * Falloff Settings
  , FalloffSettings(..)
  , noFalloff
  , smoothFalloff
  , inverseSquareFalloff
  
  -- * Accessors
  , light3DId
  , light3DType
  , light3DColor
  , light3DIntensity
  , light3DConeSettings
  , light3DFalloffSettings
  , light3DShadowSettings
  , light3DPosition
  , light3DPointOfInterest
  
  -- * Operations
  , setIntensity
  , setColor
  , setConeAngle
  , setConeFeather
  , setShadowDarkness
  , enableShadows
  , disableShadows
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Color.SRGB (SRGB, srgb)
import Hydrogen.Schema.Dimension.Device (Pixel(Pixel))
import Hydrogen.Schema.Dimension.Percentage 
  ( Percent
  , percent
  , IntensityPercent
  , fullIntensity
  )
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)
import Hydrogen.Schema.Spatial.SpotAngle (SpotAngle, spotAngle)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // light3d // id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a Light3D layer.
newtype Light3DId = Light3DId String

derive instance eqLight3DId :: Eq Light3DId
derive instance ordLight3DId :: Ord Light3DId

instance showLight3DId :: Show Light3DId where
  show (Light3DId id) = "Light3D:" <> id

-- | Smart constructor for Light3DId.
mkLight3DId :: String -> Maybe Light3DId
mkLight3DId "" = Nothing
mkLight3DId s = Just (Light3DId s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // light3d // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of light source (After Effects categories).
data Light3DType
  = LT3DParallel     -- ^ Directional/sun light (infinite distance, parallel rays)
  | LT3DSpot         -- ^ Spot light (cone-shaped with angle and feather)
  | LT3DPoint        -- ^ Point light (omnidirectional, bulb-like)
  | LT3DAmbient      -- ^ Ambient light (base illumination, no direction)

derive instance eqLight3DType :: Eq Light3DType
derive instance ordLight3DType :: Ord Light3DType

instance showLight3DType :: Show Light3DType where
  show = light3DTypeToString

-- | All light types for UI enumeration.
allLight3DTypes :: Array Light3DType
allLight3DTypes = [LT3DParallel, LT3DSpot, LT3DPoint, LT3DAmbient]

-- | Convert to string representation.
light3DTypeToString :: Light3DType -> String
light3DTypeToString LT3DParallel = "Parallel"
light3DTypeToString LT3DSpot = "Spot"
light3DTypeToString LT3DPoint = "Point"
light3DTypeToString LT3DAmbient = "Ambient"

-- | Parse from string.
light3DTypeFromString :: String -> Maybe Light3DType
light3DTypeFromString "Parallel" = Just LT3DParallel
light3DTypeFromString "parallel" = Just LT3DParallel
light3DTypeFromString "Spot" = Just LT3DSpot
light3DTypeFromString "spot" = Just LT3DSpot
light3DTypeFromString "Point" = Just LT3DPoint
light3DTypeFromString "point" = Just LT3DPoint
light3DTypeFromString "Ambient" = Just LT3DAmbient
light3DTypeFromString "ambient" = Just LT3DAmbient
light3DTypeFromString _ = Nothing

-- | Is this a directional/parallel light?
isDirectional :: Light3DType -> Boolean
isDirectional LT3DParallel = true
isDirectional _ = false

-- | Is this a spot light?
isSpot :: Light3DType -> Boolean
isSpot LT3DSpot = true
isSpot _ = false

-- | Is this a point light?
isPoint :: Light3DType -> Boolean
isPoint LT3DPoint = true
isPoint _ = false

-- | Is this an ambient light?
isAmbient :: Light3DType -> Boolean
isAmbient LT3DAmbient = true
isAmbient _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // light // falloff
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light intensity falloff mode.
-- |
-- | Determines how light intensity decreases with distance from source.
data LightFalloff
  = LFNone              -- ^ No falloff (constant intensity)
  | LFSmooth            -- ^ Linear falloff to zero at falloff distance
  | LFInverseSquare     -- ^ Physically accurate inverse square (clamped)

derive instance eqLightFalloff :: Eq LightFalloff
derive instance ordLightFalloff :: Ord LightFalloff

instance showLightFalloff :: Show LightFalloff where
  show = lightFalloffToString

-- | All falloff modes for UI enumeration.
allLightFalloffs :: Array LightFalloff
allLightFalloffs = [LFNone, LFSmooth, LFInverseSquare]

-- | Convert to string.
lightFalloffToString :: LightFalloff -> String
lightFalloffToString LFNone = "None"
lightFalloffToString LFSmooth = "Smooth"
lightFalloffToString LFInverseSquare = "Inverse Square Clamped"

-- | Parse from string.
lightFalloffFromString :: String -> Maybe LightFalloff
lightFalloffFromString "None" = Just LFNone
lightFalloffFromString "none" = Just LFNone
lightFalloffFromString "Smooth" = Just LFSmooth
lightFalloffFromString "smooth" = Just LFSmooth
lightFalloffFromString "Inverse Square Clamped" = Just LFInverseSquare
lightFalloffFromString "inverse square clamped" = Just LFInverseSquare
lightFalloffFromString "inversesquare" = Just LFInverseSquare
lightFalloffFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // shadow // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shadow casting mode.
data ShadowMode
  = SMOff       -- ^ No shadows
  | SMOn        -- ^ Cast shadows and illuminate
  | SMOnly      -- ^ Cast shadows only, no illumination

derive instance eqShadowMode :: Eq ShadowMode
derive instance ordShadowMode :: Ord ShadowMode

instance showShadowMode :: Show ShadowMode where
  show = shadowModeToString

-- | All shadow modes for UI enumeration.
allShadowModes :: Array ShadowMode
allShadowModes = [SMOff, SMOn, SMOnly]

-- | Convert to string.
shadowModeToString :: ShadowMode -> String
shadowModeToString SMOff = "Off"
shadowModeToString SMOn = "On"
shadowModeToString SMOnly = "Only"

-- | Parse from string.
shadowModeFromString :: String -> Maybe ShadowMode
shadowModeFromString "Off" = Just SMOff
shadowModeFromString "off" = Just SMOff
shadowModeFromString "On" = Just SMOn
shadowModeFromString "on" = Just SMOn
shadowModeFromString "Only" = Just SMOnly
shadowModeFromString "only" = Just SMOnly
shadowModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // shadow // settings
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shadow settings for a light.
-- |
-- | All properties are animatable.
newtype LightShadowSettings = LightShadowSettings
  { mode :: ShadowMode            -- ^ Shadow casting mode
  , darkness :: Percent           -- ^ Shadow darkness (0-100%, clamps)
  , diffusion :: Pixel            -- ^ Shadow softness/spread (0+, clamps)
  }

derive instance eqLightShadowSettings :: Eq LightShadowSettings

instance showLightShadowSettings :: Show LightShadowSettings where
  show (LightShadowSettings s) =
    "ShadowSettings { mode: " <> show s.mode <>
    ", darkness: " <> show s.darkness <> " }"

-- | Default shadow settings (shadows on, 100% darkness, no diffusion).
defaultShadowSettings :: LightShadowSettings
defaultShadowSettings = LightShadowSettings
  { mode: SMOn
  , darkness: percent 100.0
  , diffusion: Pixel 0.0
  }

-- | Shadows disabled.
shadowsOff :: LightShadowSettings
shadowsOff = LightShadowSettings
  { mode: SMOff
  , darkness: percent 0.0
  , diffusion: Pixel 0.0
  }

-- | Shadows enabled with default settings.
shadowsOn :: Percent -> Pixel -> LightShadowSettings
shadowsOn darkness diffusion = LightShadowSettings
  { mode: SMOn
  , darkness: darkness
  , diffusion: diffusion
  }

-- | Shadow only mode (no illumination).
shadowsOnly :: Percent -> Pixel -> LightShadowSettings
shadowsOnly darkness diffusion = LightShadowSettings
  { mode: SMOnly
  , darkness: darkness
  , diffusion: diffusion
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // cone // settings
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cone settings for spot lights.
-- |
-- | Only applies when Light3DType = LT3DSpot.
newtype ConeSettings = ConeSettings
  { angle :: SpotAngle        -- ^ Cone angle in degrees (0-180, clamps)
  , feather :: Percent        -- ^ Cone edge feather (0-100%, clamps)
  }

derive instance eqConeSettings :: Eq ConeSettings

instance showConeSettings :: Show ConeSettings where
  show (ConeSettings c) =
    "ConeSettings { angle: " <> show c.angle <>
    ", feather: " <> show c.feather <> " }"

-- | Default cone settings (90 degree cone, 50% feather).
defaultConeSettings :: ConeSettings
defaultConeSettings = ConeSettings
  { angle: spotAngle 90.0
  , feather: percent 50.0
  }

-- | Create cone settings with bounds validation.
mkConeSettings :: Number -> Number -> ConeSettings
mkConeSettings angle' feather' = ConeSettings
  { angle: spotAngle angle'
  , feather: percent feather'
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // falloff // settings
-- ═════════════════════════════════════════════════════════════════════════════

-- | Falloff settings for lights with range.
-- |
-- | Only applies when falloff mode is not None.
newtype FalloffSettings = FalloffSettings
  { mode :: LightFalloff
  , distance :: Pixel         -- ^ Falloff distance in pixels (0+)
  }

derive instance eqFalloffSettings :: Eq FalloffSettings

instance showFalloffSettings :: Show FalloffSettings where
  show (FalloffSettings f) =
    "FalloffSettings { mode: " <> show f.mode <>
    ", distance: " <> show f.distance <> " }"

-- | No falloff (constant intensity).
noFalloff :: FalloffSettings
noFalloff = FalloffSettings
  { mode: LFNone
  , distance: Pixel 0.0
  }

-- | Smooth linear falloff.
smoothFalloff :: Pixel -> FalloffSettings
smoothFalloff dist = FalloffSettings
  { mode: LFSmooth
  , distance: dist
  }

-- | Physically accurate inverse square falloff.
inverseSquareFalloff :: Pixel -> FalloffSettings
inverseSquareFalloff dist = FalloffSettings
  { mode: LFInverseSquare
  , distance: dist
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // light3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 3D Light layer for motion graphics.
-- |
-- | All numeric properties are animatable. This type integrates with the
-- | LayerType.LTLight variant in the Motion layer system.
newtype Light3D = Light3D
  { id :: Light3DId
  , lightType :: Light3DType
  , color :: SRGB                        -- ^ Light color (animatable)
  , intensity :: IntensityPercent        -- ^ Intensity 0-400% (animatable, clamps)
  , position :: Vec3 Number              -- ^ Position in 3D space (animatable)
  , pointOfInterest :: Vec3 Number       -- ^ Target point (for Spot) (animatable)
  , coneSettings :: ConeSettings         -- ^ Spot light cone (only for Spot)
  , falloffSettings :: FalloffSettings   -- ^ Distance falloff
  , shadowSettings :: LightShadowSettings -- ^ Shadow behavior
  }

derive instance eqLight3D :: Eq Light3D

instance showLight3D :: Show Light3D where
  show (Light3D l) =
    "Light3D { id: " <> show l.id <>
    ", type: " <> show l.lightType <>
    ", intensity: " <> show l.intensity <> " }"

-- | Default Light3D (Point light, white, 100% intensity).
defaultLight3D :: Light3DId -> Light3D
defaultLight3D lightId = Light3D
  { id: lightId
  , lightType: LT3DPoint
  , color: srgb 255 255 255
  , intensity: fullIntensity
  , position: vec3 0.0 0.0 (-500.0)
  , pointOfInterest: vec3 0.0 0.0 0.0
  , coneSettings: defaultConeSettings
  , falloffSettings: noFalloff
  , shadowSettings: defaultShadowSettings
  }

-- | Create a Light3D with specified type.
mkLight3D :: Light3DId -> Light3DType -> SRGB -> IntensityPercent -> Light3D
mkLight3D lightId lightType' color' intensity' =
  let base = defaultLight3D lightId
      (Light3D baseRec) = base
  in Light3D baseRec
       { lightType = lightType'
       , color = color'
       , intensity = intensity'
       }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get light ID.
light3DId :: Light3D -> Light3DId
light3DId (Light3D l) = l.id

-- | Get light type.
light3DType :: Light3D -> Light3DType
light3DType (Light3D l) = l.lightType

-- | Get light color.
light3DColor :: Light3D -> SRGB
light3DColor (Light3D l) = l.color

-- | Get light intensity (0-400%).
light3DIntensity :: Light3D -> IntensityPercent
light3DIntensity (Light3D l) = l.intensity

-- | Get cone settings (relevant for Spot lights).
light3DConeSettings :: Light3D -> ConeSettings
light3DConeSettings (Light3D l) = l.coneSettings

-- | Get falloff settings.
light3DFalloffSettings :: Light3D -> FalloffSettings
light3DFalloffSettings (Light3D l) = l.falloffSettings

-- | Get shadow settings.
light3DShadowSettings :: Light3D -> LightShadowSettings
light3DShadowSettings (Light3D l) = l.shadowSettings

-- | Get position in 3D space.
light3DPosition :: Light3D -> Vec3 Number
light3DPosition (Light3D l) = l.position

-- | Get point of interest (target).
light3DPointOfInterest :: Light3D -> Vec3 Number
light3DPointOfInterest (Light3D l) = l.pointOfInterest

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set light intensity (0-400%, clamped).
setIntensity :: IntensityPercent -> Light3D -> Light3D
setIntensity intensity' (Light3D l) =
  Light3D l { intensity = intensity' }

-- | Set light color.
setColor :: SRGB -> Light3D -> Light3D
setColor color' (Light3D l) =
  Light3D l { color = color' }

-- | Set cone angle (for Spot lights, 0-180 degrees).
setConeAngle :: SpotAngle -> Light3D -> Light3D
setConeAngle angle' (Light3D l) =
  let (ConeSettings cone) = l.coneSettings
  in Light3D l { coneSettings = ConeSettings cone { angle = angle' } }

-- | Set cone feather (for Spot lights, 0-100%).
setConeFeather :: Percent -> Light3D -> Light3D
setConeFeather feather' (Light3D l) =
  let (ConeSettings cone) = l.coneSettings
  in Light3D l { coneSettings = ConeSettings cone { feather = feather' } }

-- | Set shadow darkness (0-100%).
setShadowDarkness :: Percent -> Light3D -> Light3D
setShadowDarkness darkness' (Light3D l) =
  let (LightShadowSettings shadow) = l.shadowSettings
  in Light3D l { shadowSettings = LightShadowSettings shadow { darkness = darkness' } }

-- | Enable shadows.
enableShadows :: Light3D -> Light3D
enableShadows (Light3D l) =
  let (LightShadowSettings shadow) = l.shadowSettings
  in Light3D l { shadowSettings = LightShadowSettings shadow { mode = SMOn } }

-- | Disable shadows.
disableShadows :: Light3D -> Light3D
disableShadows (Light3D l) =
  let (LightShadowSettings shadow) = l.shadowSettings
  in Light3D l { shadowSettings = LightShadowSettings shadow { mode = SMOff } }


