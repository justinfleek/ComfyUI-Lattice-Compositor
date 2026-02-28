-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // material // surface
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Surface - material surface appearance compound.
-- |
-- | Describes how light interacts with a surface, determining its visual
-- | appearance. Used for PBR (Physically Based Rendering) workflows and
-- | UI material design.
-- |
-- | ## Surface Types
-- |
-- | - **Matte**: No reflectivity, diffuse only (paper, cloth)
-- | - **Glossy**: High reflectivity, specular highlight (plastic, wet paint)
-- | - **Metallic**: Metal-like reflection, colored specular (gold, chrome)
-- | - **Satin**: Soft sheen, between matte and glossy (silk, brushed metal)
-- | - **Textured**: Surface with tactile/visual texture (leather, concrete)
-- |
-- | ## PBR Parameters
-- |
-- | - Roughness: 0.0 (mirror) to 1.0 (fully diffuse)
-- | - Metalness: 0.0 (dielectric) to 1.0 (metal)
-- | - Reflectivity: Base reflectivity at normal incidence
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded

module Hydrogen.Schema.Material.Surface
  ( -- * Surface Type
    SurfaceType(..)
  
  -- * Types
  , Surface(Surface)
  , SurfaceConfig
  
  -- * Constructors
  , surface
  , surfaceMatte
  , surfaceGlossy
  , surfaceMetallic
  , surfaceSatin
  , surfaceTextured
  
  -- * Accessors
  , surfaceType
  , roughness
  , metalness
  , reflectivity
  
  -- * Presets
  , paper
  , plastic
  , chrome
  , gold
  , silk
  , leather
  , glass
  , water
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , (<>)
  )

import Hydrogen.Schema.Bounded (clampNumber) as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // surface type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Surface type classification.
data SurfaceType
  = Matte      -- ^ No reflectivity, pure diffuse
  | Glossy     -- ^ High reflectivity, sharp specular
  | Metallic   -- ^ Metal-like, colored specular
  | Satin      -- ^ Soft sheen, blurred reflection
  | Textured   -- ^ Surface with visible texture
  | Custom     -- ^ Custom PBR parameters

derive instance eqSurfaceType :: Eq SurfaceType
derive instance ordSurfaceType :: Ord SurfaceType

instance showSurfaceType :: Show SurfaceType where
  show Matte = "matte"
  show Glossy = "glossy"
  show Metallic = "metallic"
  show Satin = "satin"
  show Textured = "textured"
  show Custom = "custom"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // surface
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration record for creating Surface
type SurfaceConfig =
  { roughness :: Number      -- ^ 0.0 (mirror) to 1.0 (diffuse)
  , metalness :: Number      -- ^ 0.0 (dielectric) to 1.0 (metal)
  , reflectivity :: Number   -- ^ Base reflectivity (0.0 to 1.0)
  }

-- | Surface - material appearance compound.
-- |
-- | Describes PBR material properties for realistic rendering.
newtype Surface = Surface
  { surfaceType :: SurfaceType
  , roughness :: Number        -- ^ 0.0 = mirror, 1.0 = fully diffuse
  , metalness :: Number        -- ^ 0.0 = dielectric, 1.0 = metal
  , reflectivity :: Number     -- ^ F0 reflectivity (0.0-1.0)
  }

derive instance eqSurface :: Eq Surface

instance showSurface :: Show Surface where
  show (Surface s) = 
    "(Surface " <> show s.surfaceType 
      <> " rough:" <> show s.roughness 
      <> " metal:" <> show s.metalness 
      <> " refl:" <> show s.reflectivity
      <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create Surface from custom PBR parameters
surface :: SurfaceConfig -> Surface
surface cfg = Surface
  { surfaceType: Custom
  , roughness: Bounded.clampNumber 0.0 1.0 cfg.roughness
  , metalness: Bounded.clampNumber 0.0 1.0 cfg.metalness
  , reflectivity: Bounded.clampNumber 0.0 1.0 cfg.reflectivity
  }

-- | Create matte surface (pure diffuse, no reflectivity)
surfaceMatte :: Surface
surfaceMatte = Surface
  { surfaceType: Matte
  , roughness: 1.0
  , metalness: 0.0
  , reflectivity: 0.04  -- Typical dielectric F0
  }

-- | Create glossy surface (high reflectivity, sharp specular)
surfaceGlossy :: Surface
surfaceGlossy = Surface
  { surfaceType: Glossy
  , roughness: 0.1
  , metalness: 0.0
  , reflectivity: 0.5
  }

-- | Create metallic surface (metal-like reflection)
surfaceMetallic :: Surface
surfaceMetallic = Surface
  { surfaceType: Metallic
  , roughness: 0.2
  , metalness: 1.0
  , reflectivity: 0.9
  }

-- | Create satin surface (soft sheen)
surfaceSatin :: Surface
surfaceSatin = Surface
  { surfaceType: Satin
  , roughness: 0.5
  , metalness: 0.0
  , reflectivity: 0.2
  }

-- | Create textured surface (visible texture)
surfaceTextured :: Surface
surfaceTextured = Surface
  { surfaceType: Textured
  , roughness: 0.8
  , metalness: 0.0
  , reflectivity: 0.1
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get surface type
surfaceType :: Surface -> SurfaceType
surfaceType (Surface s) = s.surfaceType

-- | Get roughness (0.0 = mirror, 1.0 = diffuse)
roughness :: Surface -> Number
roughness (Surface s) = s.roughness

-- | Get metalness (0.0 = dielectric, 1.0 = metal)
metalness :: Surface -> Number
metalness (Surface s) = s.metalness

-- | Get reflectivity (F0)
reflectivity :: Surface -> Number
reflectivity (Surface s) = s.reflectivity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Paper surface (matte, low reflectivity)
paper :: Surface
paper = Surface
  { surfaceType: Matte
  , roughness: 0.95
  , metalness: 0.0
  , reflectivity: 0.03
  }

-- | Plastic surface (glossy dielectric)
plastic :: Surface
plastic = Surface
  { surfaceType: Glossy
  , roughness: 0.15
  , metalness: 0.0
  , reflectivity: 0.04
  }

-- | Chrome surface (highly reflective metal)
chrome :: Surface
chrome = Surface
  { surfaceType: Metallic
  , roughness: 0.05
  , metalness: 1.0
  , reflectivity: 0.95
  }

-- | Gold surface (warm metallic)
gold :: Surface
gold = Surface
  { surfaceType: Metallic
  , roughness: 0.15
  , metalness: 1.0
  , reflectivity: 0.9
  }

-- | Silk surface (soft satin sheen)
silk :: Surface
silk = Surface
  { surfaceType: Satin
  , roughness: 0.45
  , metalness: 0.0
  , reflectivity: 0.15
  }

-- | Leather surface (textured, slight sheen)
leather :: Surface
leather = Surface
  { surfaceType: Textured
  , roughness: 0.7
  , metalness: 0.0
  , reflectivity: 0.08
  }

-- | Glass surface (transparent, high reflectivity at angles)
glass :: Surface
glass = Surface
  { surfaceType: Glossy
  , roughness: 0.0
  , metalness: 0.0
  , reflectivity: 0.04  -- Glass F0 is ~0.04
  }

-- | Water surface (reflective at grazing angles)
water :: Surface
water = Surface
  { surfaceType: Glossy
  , roughness: 0.0
  , metalness: 0.0
  , reflectivity: 0.02  -- Water F0 is ~0.02
  }
