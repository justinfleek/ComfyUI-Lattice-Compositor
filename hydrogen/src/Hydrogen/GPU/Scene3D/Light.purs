-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // gpu // scene3d // light
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Light3D — Scene lighting definitions.
-- |
-- | ## Light Types
-- | - Ambient: Uniform illumination from all directions
-- | - Directional: Sun-like parallel rays
-- | - Point: Omnidirectional from a point
-- | - Spot: Cone-shaped light
-- | - Hemisphere: Sky + ground ambient
-- |
-- | ## Proof Reference
-- | Attenuation: `proofs/Hydrogen/Light/Attenuation.lean`
-- | Shadow mapping: `proofs/Hydrogen/Light/Shadow.lean`

module Hydrogen.GPU.Scene3D.Light
  ( Light3D
      ( AmbientLight3D
      , DirectionalLight3D
      , PointLight3D
      , SpotLight3D
      , HemisphereLight3D
      )
  , AmbientLightParams
  , ambientLight3D
  , DirectionalLightParams
  , directionalLight3D
  , PointLightParams
  , pointLight3D
  , SpotLightParams
  , spotLight3D
  , HemisphereLightParams
  , hemisphereLight3D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude (class Eq)

import Hydrogen.GPU.Scene3D.Position (Position3D, Direction3D)
import Hydrogen.Schema.Color.RGB (RGBA)
import Hydrogen.Schema.Dimension.Physical.SI (Meter)
import Hydrogen.Schema.Geometry.Angle (Degrees)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // lights
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light source in the scene.
-- |
-- | ## Proof Reference
-- | Attenuation: `proofs/Hydrogen/Light/Attenuation.lean`
-- | Shadow mapping: `proofs/Hydrogen/Light/Shadow.lean`
data Light3D
  = AmbientLight3D AmbientLightParams
  | DirectionalLight3D DirectionalLightParams
  | PointLight3D PointLightParams
  | SpotLight3D SpotLightParams
  | HemisphereLight3D HemisphereLightParams

derive instance eqLight3D :: Eq Light3D

-- | Ambient light (uniform illumination from all directions).
type AmbientLightParams =
  { color :: RGBA
  , intensity :: Number  -- 0.0 to 1.0
  }

ambientLight3D :: AmbientLightParams -> Light3D
ambientLight3D = AmbientLight3D

-- | Directional light (sun-like, parallel rays).
type DirectionalLightParams =
  { color :: RGBA
  , intensity :: Number
  , direction :: Direction3D
  , castShadow :: Boolean
  , shadowMapSize :: Int
  , shadowBias :: Number
  }

directionalLight3D :: DirectionalLightParams -> Light3D
directionalLight3D = DirectionalLight3D

-- | Point light (omnidirectional from a point).
type PointLightParams =
  { color :: RGBA
  , intensity :: Number       -- Candela (physically correct)
  , position :: Position3D
  , distance :: Meter         -- Cutoff distance (0 = infinite)
  , decay :: Number           -- Attenuation exponent (2 = physically correct)
  , castShadow :: Boolean
  }

pointLight3D :: PointLightParams -> Light3D
pointLight3D = PointLight3D

-- | Spot light (cone of light).
type SpotLightParams =
  { color :: RGBA
  , intensity :: Number
  , position :: Position3D
  , target :: Position3D
  , distance :: Meter
  , angle :: Degrees          -- Cone angle (0-90)
  , penumbra :: Number        -- Soft edge (0-1)
  , decay :: Number
  , castShadow :: Boolean
  }

spotLight3D :: SpotLightParams -> Light3D
spotLight3D = SpotLight3D

-- | Hemisphere light (sky + ground ambient).
type HemisphereLightParams =
  { skyColor :: RGBA
  , groundColor :: RGBA
  , intensity :: Number
  }

hemisphereLight3D :: HemisphereLightParams -> Light3D
hemisphereLight3D = HemisphereLight3D
