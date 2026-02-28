-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // spatial // light // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Light Types — Complete set of 3D light sources.
-- |
-- | Light types for physically-based and stylized rendering:
-- |
-- | ## Directional
-- | Parallel rays from infinite distance (sun, moon).
-- | Position is irrelevant; only direction matters.
-- |
-- | ## Point
-- | Omnidirectional light from a point (bulb, candle).
-- | Intensity falls off with distance squared.
-- |
-- | ## Spot
-- | Cone-shaped light from a point (flashlight, stage light).
-- | Has inner angle (full intensity) and outer angle (falloff).
-- |
-- | ## Area
-- | Light emitting from a surface (softbox, window).
-- | Produces soft shadows. More expensive to compute.
-- |
-- | ## Hemisphere
-- | Ambient lighting from sky/ground (outdoor ambient).
-- | Two colors: sky above, ground below.
-- |
-- | ## Probe
-- | Environment reflection captured at a point (IBL).
-- | Used for specular reflections and ambient lighting.
-- |
-- | ## IES
-- | Photometric light profile from real fixture measurements.
-- | Defines complex light distribution patterns.

module Hydrogen.Schema.Spatial.Light.Types
  ( -- * Light Types
    DirectionalLight(..)
  , PointLight(..)
  , SpotLight(..)
  , AreaLight(..)
  , AreaShape(..)
  , HemisphereLight(..)
  , ProbeLight(..)
  , IESLight(..)
  , IESProfile(..)
  
  -- * Unified Light
  , Light(..)
  
  -- * Constructors
  , directional
  , directionalWithShadow
  , point
  , pointWithShadow
  , spot
  , spotWithShadow
  , areaRect
  , areaDisc
  , hemisphere
  , probe
  , ies
  
  -- * Accessors
  , lightColor
  , lightIntensity
  , castsShadow
  , lightRange
  
  -- * Operations
  , attenuate
  , spotFalloff
  , scaleIntensity
  , combineIntensities
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)
import Hydrogen.Schema.Spatial.LightIntensity (LightIntensity)
import Hydrogen.Schema.Spatial.LightIntensity (unwrapLightIntensity, lightIntensity) as LI
import Hydrogen.Schema.Spatial.LightRange (LightRange, unwrapLightRange)
import Hydrogen.Schema.Spatial.SpotAngle (SpotAngle, unwrapSpotAngle)
import Hydrogen.Schema.Spatial.SpotSoftness (SpotSoftness)
import Hydrogen.Schema.Spatial.ShadowBias (ShadowBias)
import Hydrogen.Schema.Spatial.ShadowStrength (ShadowStrength)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // directional light
-- ═════════════════════════════════════════════════════════════════════════════

-- | Directional light (sun, moon)
-- |
-- | All rays are parallel. No position, only direction.
-- | Intensity does not fall off with distance.
newtype DirectionalLight = DirectionalLight
  { direction :: Vec3 Number      -- ^ Direction light travels (normalized)
  , color :: Vec3 Number          -- ^ RGB color (0-1 per channel)
  , intensity :: LightIntensity
  , castShadow :: Boolean
  , shadowBias :: Maybe ShadowBias
  , shadowStrength :: Maybe ShadowStrength
  }

derive instance eqDirectionalLight :: Eq DirectionalLight

instance showDirectionalLight :: Show DirectionalLight where
  show (DirectionalLight l) =
    "DirectionalLight { direction: " <> show l.direction <>
    ", intensity: " <> show l.intensity <> " }"

-- | Create a directional light (no shadow configuration)
directional :: Vec3 Number -> Vec3 Number -> LightIntensity -> DirectionalLight
directional direction color intensity = DirectionalLight
  { direction
  , color
  , intensity
  , castShadow: true
  , shadowBias: Nothing
  , shadowStrength: Nothing
  }

-- | Create a directional light with shadow configuration
directionalWithShadow
  :: Vec3 Number
  -> Vec3 Number
  -> LightIntensity
  -> ShadowBias
  -> ShadowStrength
  -> DirectionalLight
directionalWithShadow direction color intensity bias strength = DirectionalLight
  { direction
  , color
  , intensity
  , castShadow: true
  , shadowBias: Just bias
  , shadowStrength: Just strength
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // point light
-- ═════════════════════════════════════════════════════════════════════════════

-- | Point light (bulb, candle)
-- |
-- | Emits light equally in all directions from a point.
-- | Intensity falls off with distance squared (physically accurate).
newtype PointLight = PointLight
  { position :: Vec3 Number
  , color :: Vec3 Number
  , intensity :: LightIntensity
  , range :: LightRange           -- ^ Maximum influence distance
  , castShadow :: Boolean
  , shadowBias :: Maybe ShadowBias
  }

derive instance eqPointLight :: Eq PointLight

instance showPointLight :: Show PointLight where
  show (PointLight l) =
    "PointLight { position: " <> show l.position <>
    ", intensity: " <> show l.intensity <>
    ", range: " <> show l.range <> " }"

-- | Create a point light (no shadow)
point :: Vec3 Number -> Vec3 Number -> LightIntensity -> LightRange -> PointLight
point position color intensity range = PointLight
  { position
  , color
  , intensity
  , range
  , castShadow: false
  , shadowBias: Nothing
  }

-- | Create a point light with shadow configuration
pointWithShadow
  :: Vec3 Number
  -> Vec3 Number
  -> LightIntensity
  -> LightRange
  -> ShadowBias
  -> PointLight
pointWithShadow position color intensity range bias = PointLight
  { position
  , color
  , intensity
  , range
  , castShadow: true
  , shadowBias: Just bias
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // spot light
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spot light (flashlight, stage light)
-- |
-- | Cone-shaped light with inner and outer angles.
-- | Full intensity within inner angle, falls off to zero at outer angle.
newtype SpotLight = SpotLight
  { position :: Vec3 Number
  , direction :: Vec3 Number
  , color :: Vec3 Number
  , intensity :: LightIntensity
  , range :: LightRange
  , innerAngle :: SpotAngle       -- ^ Full intensity cone
  , outerAngle :: SpotAngle       -- ^ Zero intensity cone
  , softness :: Maybe SpotSoftness
  , castShadow :: Boolean
  , shadowBias :: Maybe ShadowBias
  }

derive instance eqSpotLight :: Eq SpotLight

instance showSpotLight :: Show SpotLight where
  show (SpotLight l) =
    "SpotLight { position: " <> show l.position <>
    ", direction: " <> show l.direction <>
    ", innerAngle: " <> show l.innerAngle <>
    ", outerAngle: " <> show l.outerAngle <> " }"

-- | Create a spot light (default shadow)
spot :: Vec3 Number -> Vec3 Number -> Vec3 Number -> LightIntensity -> LightRange -> SpotAngle -> SpotAngle -> SpotLight
spot position direction color intensity range innerAngle outerAngle = SpotLight
  { position
  , direction
  , color
  , intensity
  , range
  , innerAngle
  , outerAngle
  , softness: Nothing
  , castShadow: true
  , shadowBias: Nothing
  }

-- | Create a spot light with shadow configuration
spotWithShadow
  :: Vec3 Number
  -> Vec3 Number
  -> Vec3 Number
  -> LightIntensity
  -> LightRange
  -> SpotAngle
  -> SpotAngle
  -> ShadowBias
  -> SpotLight
spotWithShadow position direction color intensity range innerAngle outerAngle bias = SpotLight
  { position
  , direction
  , color
  , intensity
  , range
  , innerAngle
  , outerAngle
  , softness: Nothing
  , castShadow: true
  , shadowBias: Just bias
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // area shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape of area light
data AreaShape
  = Rectangle { width :: Number, height :: Number }
  | Disc { radius :: Number }
  | Sphere { radius :: Number }

derive instance eqAreaShape :: Eq AreaShape

instance showAreaShape :: Show AreaShape where
  show (Rectangle r) = "Rectangle " <> show r.width <> "x" <> show r.height
  show (Disc d) = "Disc r=" <> show d.radius
  show (Sphere s) = "Sphere r=" <> show s.radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // area light
-- ═════════════════════════════════════════════════════════════════════════════

-- | Area light (softbox, window)
-- |
-- | Light emitting from a surface. Produces realistic soft shadows.
-- | More expensive to compute than point/spot lights.
newtype AreaLight = AreaLight
  { position :: Vec3 Number
  , direction :: Vec3 Number      -- ^ Normal of light surface
  , color :: Vec3 Number
  , intensity :: LightIntensity
  , shape :: AreaShape
  , twoSided :: Boolean           -- ^ Emit from both sides
  , castShadow :: Boolean
  }

derive instance eqAreaLight :: Eq AreaLight

instance showAreaLight :: Show AreaLight where
  show (AreaLight l) =
    "AreaLight { position: " <> show l.position <>
    ", shape: " <> show l.shape <> " }"

-- | Create a rectangular area light
areaRect :: Vec3 Number -> Vec3 Number -> Vec3 Number -> LightIntensity -> Number -> Number -> AreaLight
areaRect position direction color intensity width height = AreaLight
  { position
  , direction
  , color
  , intensity
  , shape: Rectangle { width, height }
  , twoSided: false
  , castShadow: true
  }

-- | Create a disc-shaped area light
areaDisc :: Vec3 Number -> Vec3 Number -> Vec3 Number -> LightIntensity -> Number -> AreaLight
areaDisc position direction color intensity radius = AreaLight
  { position
  , direction
  , color
  , intensity
  , shape: Disc { radius }
  , twoSided: false
  , castShadow: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // hemisphere light
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hemisphere light (outdoor ambient)
-- |
-- | Simulates sky/ground ambient lighting.
-- | Color blends from sky (above) to ground (below).
newtype HemisphereLight = HemisphereLight
  { skyColor :: Vec3 Number       -- ^ Color from above
  , groundColor :: Vec3 Number    -- ^ Color from below
  , intensity :: LightIntensity
  , upDirection :: Vec3 Number    -- ^ Which way is "up" (default: Y)
  }

derive instance eqHemisphereLight :: Eq HemisphereLight

instance showHemisphereLight :: Show HemisphereLight where
  show (HemisphereLight l) =
    "HemisphereLight { sky: " <> show l.skyColor <>
    ", ground: " <> show l.groundColor <> " }"

-- | Create a hemisphere light
hemisphere :: Vec3 Number -> Vec3 Number -> LightIntensity -> HemisphereLight
hemisphere skyColor groundColor intensity = HemisphereLight
  { skyColor
  , groundColor
  , intensity
  , upDirection: vec3 0.0 1.0 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // probe light
-- ═════════════════════════════════════════════════════════════════════════════

-- | Environment probe (reflection/IBL)
-- |
-- | Captures environment at a point for image-based lighting.
-- | Used for specular reflections and ambient lighting.
newtype ProbeLight = ProbeLight
  { position :: Vec3 Number
  , radius :: Number              -- ^ Influence radius
  , resolution :: Int             -- ^ Cubemap resolution
  , intensity :: LightIntensity
  , boxProjection :: Maybe { min :: Vec3 Number, max :: Vec3 Number }  -- ^ Box for parallax correction
  }

derive instance eqProbeLight :: Eq ProbeLight

instance showProbeLight :: Show ProbeLight where
  show (ProbeLight l) =
    "ProbeLight { position: " <> show l.position <>
    ", radius: " <> show l.radius <>
    ", resolution: " <> show l.resolution <> " }"

-- | Create an environment probe
probe :: Vec3 Number -> Number -> Int -> LightIntensity -> ProbeLight
probe position radius resolution intensity = ProbeLight
  { position
  , radius
  , resolution
  , intensity
  , boxProjection: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // ies profile
-- ═════════════════════════════════════════════════════════════════════════════

-- | IES photometric profile
-- |
-- | Real-world light fixture measurement data.
-- | Reference to external .ies file or inline data.
newtype IESProfile = IESProfile
  { name :: String                -- ^ Profile identifier
  , symmetry :: Int               -- ^ Symmetry type (0-4)
  }

derive instance eqIESProfile :: Eq IESProfile

instance showIESProfile :: Show IESProfile where
  show (IESProfile p) = "IESProfile \"" <> p.name <> "\""

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // ies light
-- ═════════════════════════════════════════════════════════════════════════════

-- | IES photometric light
-- |
-- | Light with intensity distribution defined by IES profile.
-- | Used for architectural lighting simulation.
newtype IESLight = IESLight
  { position :: Vec3 Number
  , direction :: Vec3 Number
  , color :: Vec3 Number
  , intensity :: LightIntensity
  , profile :: IESProfile
  , range :: LightRange
  , castShadow :: Boolean
  }

derive instance eqIESLight :: Eq IESLight

instance showIESLight :: Show IESLight where
  show (IESLight l) =
    "IESLight { position: " <> show l.position <>
    ", profile: " <> show l.profile <> " }"

-- | Create an IES light
ies :: Vec3 Number -> Vec3 Number -> Vec3 Number -> LightIntensity -> IESProfile -> LightRange -> IESLight
ies position direction color intensity profile range = IESLight
  { position
  , direction
  , color
  , intensity
  , profile
  , range
  , castShadow: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // unified light
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unified light type (sum type for all light kinds)
data Light
  = LightDirectional DirectionalLight
  | LightPoint PointLight
  | LightSpot SpotLight
  | LightArea AreaLight
  | LightHemisphere HemisphereLight
  | LightProbe ProbeLight
  | LightIES IESLight

derive instance eqLight :: Eq Light

instance showLight :: Show Light where
  show (LightDirectional l) = show l
  show (LightPoint l) = show l
  show (LightSpot l) = show l
  show (LightArea l) = show l
  show (LightHemisphere l) = show l
  show (LightProbe l) = show l
  show (LightIES l) = show l

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the color of any light
lightColor :: Light -> Vec3 Number
lightColor (LightDirectional (DirectionalLight l)) = l.color
lightColor (LightPoint (PointLight l)) = l.color
lightColor (LightSpot (SpotLight l)) = l.color
lightColor (LightArea (AreaLight l)) = l.color
lightColor (LightHemisphere (HemisphereLight l)) = l.skyColor  -- Primary color
lightColor (LightProbe _) = vec3 1.0 1.0 1.0  -- Probes are neutral
lightColor (LightIES (IESLight l)) = l.color

-- | Get the intensity of any light
lightIntensity :: Light -> LightIntensity
lightIntensity (LightDirectional (DirectionalLight l)) = l.intensity
lightIntensity (LightPoint (PointLight l)) = l.intensity
lightIntensity (LightSpot (SpotLight l)) = l.intensity
lightIntensity (LightArea (AreaLight l)) = l.intensity
lightIntensity (LightHemisphere (HemisphereLight l)) = l.intensity
lightIntensity (LightProbe (ProbeLight l)) = l.intensity
lightIntensity (LightIES (IESLight l)) = l.intensity

-- | Does this light cast shadows?
castsShadow :: Light -> Boolean
castsShadow (LightDirectional (DirectionalLight l)) = l.castShadow
castsShadow (LightPoint (PointLight l)) = l.castShadow
castsShadow (LightSpot (SpotLight l)) = l.castShadow
castsShadow (LightArea (AreaLight l)) = l.castShadow
castsShadow (LightHemisphere _) = false  -- Hemisphere lights don't cast shadows
castsShadow (LightProbe _) = false  -- Probes don't cast shadows
castsShadow (LightIES (IESLight l)) = l.castShadow

-- | Get the range of a light (if applicable)
-- |
-- | Returns Nothing for lights without range (directional, hemisphere, area).
-- | Returns the maximum influence distance for point, spot, and IES lights.
lightRange :: Light -> Maybe LightRange
lightRange (LightDirectional _) = Nothing
lightRange (LightPoint (PointLight l)) = Just l.range
lightRange (LightSpot (SpotLight l)) = Just l.range
lightRange (LightArea _) = Nothing  -- Area lights use shape dimensions instead
lightRange (LightHemisphere _) = Nothing
lightRange (LightProbe _) = Nothing
lightRange (LightIES (IESLight l)) = Just l.range

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate distance attenuation
-- |
-- | Uses physically-based inverse square falloff with range limit.
-- | Returns 0-1 attenuation factor.
attenuate :: Number -> LightRange -> Number
attenuate distance range =
  let maxRange = unwrapLightRange range
      d = if distance < 0.0001 then 0.0001 else distance
      attenuation = 1.0 / (d * d)
      -- Smooth falloff at range edge
      rangeFalloff = 1.0 - clamp ((distance / maxRange) * (distance / maxRange)) 0.0 1.0
  in attenuation * rangeFalloff
  where
  clamp :: Number -> Number -> Number -> Number
  clamp v lo hi
    | v < lo = lo
    | v > hi = hi
    | otherwise = v

-- | Calculate spotlight angular falloff
-- |
-- | Returns 1.0 inside inner cone, 0.0 outside outer cone,
-- | smooth interpolation between.
spotFalloff :: Number -> SpotAngle -> SpotAngle -> Number
spotFalloff angle innerAngle outerAngle =
  let inner = unwrapSpotAngle innerAngle
      outer = unwrapSpotAngle outerAngle
  in if angle <= inner then 1.0
     else if angle >= outer then 0.0
     else smoothstep inner outer angle
  where
  smoothstep :: Number -> Number -> Number -> Number
  smoothstep edge0 edge1 x =
    let t = clamp ((x - edge0) / (edge1 - edge0)) 0.0 1.0
    in t * t * (3.0 - 2.0 * t)
  clamp :: Number -> Number -> Number -> Number
  clamp v lo hi
    | v < lo = lo
    | v > hi = hi
    | otherwise = v

-- | Scale a light intensity by a factor
-- |
-- | Useful for dimming or brightening lights programmatically.
-- | Factor is clamped to non-negative.
scaleIntensity :: Number -> LightIntensity -> LightIntensity
scaleIntensity factor intensity =
  let raw = LI.unwrapLightIntensity intensity
      scaled = raw * (if factor < 0.0 then 0.0 else factor)
  in LI.lightIntensity scaled

-- | Combine two intensities (additive)
-- |
-- | Used when multiple lights contribute to the same point.
combineIntensities :: LightIntensity -> LightIntensity -> LightIntensity
combineIntensities a b =
  let va = LI.unwrapLightIntensity a
      vb = LI.unwrapLightIntensity b
  in LI.lightIntensity (va + vb)

