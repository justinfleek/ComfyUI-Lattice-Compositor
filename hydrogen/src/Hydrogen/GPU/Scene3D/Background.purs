-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // gpu // scene3d // background
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Background3D — Scene background definitions.
-- |
-- | Solid colors, gradients, and environment maps (IBL).

module Hydrogen.GPU.Scene3D.Background
  ( Background3D
      ( SolidBackground
      , GradientBackground
      , EnvironmentBackground
      )
  , EnvironmentMap
  , solidBackground
  , gradientBackground
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude (class Eq)

import Hydrogen.GPU.Scene3D.Position (Direction3D, directionY)
import Hydrogen.Schema.Color.RGB (RGBA)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // background
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scene background.
data Background3D
  = SolidBackground RGBA
  | GradientBackground RGBA RGBA Direction3D  -- top color, bottom color, direction
  | EnvironmentBackground EnvironmentMap

derive instance eqBackground3D :: Eq Background3D

-- | Environment map for reflections and IBL.
type EnvironmentMap =
  { cubeMapId :: Int  -- Reference to loaded cubemap texture
  , intensity :: Number
  }

-- | Solid color background.
solidBackground :: RGBA -> Background3D
solidBackground = SolidBackground

-- | Gradient background (top to bottom by default).
gradientBackground :: RGBA -> RGBA -> Background3D
gradientBackground top bottom = GradientBackground top bottom directionY
