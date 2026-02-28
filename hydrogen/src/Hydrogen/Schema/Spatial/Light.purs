-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // spatial // light
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Light Compounds — 3D Light source definitions.
-- |
-- | Defines the properties of light sources.
-- | Position and orientation are handled by `Transform3D`.

module Hydrogen.Schema.Spatial.Light
  ( Light(..)
  , ShadowConfig
  , directional
  , point
  , spot
  , ambient
  , hemisphere
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Hydrogen.Schema.Color.SRGB (SRGB)
import Hydrogen.Schema.Spatial.LightIntensity (LightIntensity)
import Hydrogen.Schema.Spatial.LightRange (LightRange)
import Hydrogen.Schema.Spatial.SpotAngle (SpotAngle)
import Hydrogen.Schema.Spatial.ShadowBias (ShadowBias)
import Hydrogen.Schema.Spatial.ShadowStrength (ShadowStrength)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // light
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shadow configuration for lights
type ShadowConfig =
  { bias :: ShadowBias
  , strength :: ShadowStrength
  , resolution :: Int -- Shadow map size (e.g. 1024)
  }

-- | Light source definition
data Light
  = DirectionalLight
      { color :: SRGB
      , intensity :: LightIntensity
      , shadow :: Maybe ShadowConfig
      }
  | PointLight
      { color :: SRGB
      , intensity :: LightIntensity
      , range :: LightRange
      , shadow :: Maybe ShadowConfig
      }
  | SpotLight
      { color :: SRGB
      , intensity :: LightIntensity
      , range :: LightRange
      , angle :: SpotAngle
      , softness :: Number -- 0-1 penumbra
      , shadow :: Maybe ShadowConfig
      }
  | AmbientLight
      { color :: SRGB
      , intensity :: LightIntensity
      }
  | HemisphereLight
      { skyColor :: SRGB
      , groundColor :: SRGB
      , intensity :: LightIntensity
      }

derive instance eqLight :: Eq Light
derive instance ordLight :: Ord Light
derive instance genericLight :: Generic Light _

instance showLight :: Show Light where
  show (DirectionalLight l) = "(DirectionalLight " <> show l <> ")"
  show (PointLight l) = "(PointLight " <> show l <> ")"
  show (SpotLight l) = "(SpotLight " <> show l <> ")"
  show (AmbientLight l) = "(AmbientLight " <> show l <> ")"
  show (HemisphereLight l) = "(HemisphereLight " <> show l <> ")"

-- | Create directional light (sun-like)
directional :: SRGB -> LightIntensity -> Light
directional color intensity = DirectionalLight { color, intensity, shadow: Nothing }

-- | Create point light (bulb-like)
point :: SRGB -> LightIntensity -> LightRange -> Light
point color intensity range = PointLight { color, intensity, range, shadow: Nothing }

-- | Create spot light (flashlight-like)
spot :: SRGB -> LightIntensity -> LightRange -> SpotAngle -> Light
spot color intensity range angle =
  SpotLight
    { color
    , intensity
    , range
    , angle
    , softness: 0.0
    , shadow: Nothing
    }

-- | Create ambient light (base illumination)
ambient :: SRGB -> LightIntensity -> Light
ambient color intensity = AmbientLight { color, intensity }

-- | Create hemisphere light (sky/ground ambient)
hemisphere :: SRGB -> SRGB -> LightIntensity -> Light
hemisphere skyColor groundColor intensity =
  HemisphereLight { skyColor, groundColor, intensity }
