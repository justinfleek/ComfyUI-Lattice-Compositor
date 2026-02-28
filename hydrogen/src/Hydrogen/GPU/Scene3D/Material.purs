-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // scene3d // material
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Material3D — Surface appearance definitions.
-- |
-- | ## Material Types
-- | - Basic: Unlit, flat color
-- | - Standard: PBR metallic-roughness workflow
-- | - Physical: Advanced PBR with clearcoat, transmission, etc.
-- |
-- | ## Proof Reference
-- | PBR BRDF: `proofs/Hydrogen/Material/BRDF.lean`
-- | - fresnel_schlick
-- | - ggx_distribution
-- | - smith_geometry
-- | - cook_torrance

module Hydrogen.GPU.Scene3D.Material
  ( Material3D
      ( BasicMaterial3D
      , StandardMaterial3D
      , PhysicalMaterial3D
      )
  , BasicMaterialParams
  , basicMaterial3D
  , StandardMaterialParams
  , standardMaterial3D
  , PhysicalMaterialParams
  , physicalMaterial3D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude (class Eq)

import Hydrogen.Schema.Color.RGB (RGBA)
import Hydrogen.Schema.Dimension.Physical.SI (Meter)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // materials
-- ═════════════════════════════════════════════════════════════════════════════

-- | Material defining surface appearance.
-- |
-- | ## Proof Reference
-- | PBR BRDF: `proofs/Hydrogen/Material/BRDF.lean`
-- | - fresnel_schlick
-- | - ggx_distribution
-- | - smith_geometry
-- | - cook_torrance
data Material3D
  = BasicMaterial3D BasicMaterialParams
  | StandardMaterial3D StandardMaterialParams
  | PhysicalMaterial3D PhysicalMaterialParams

derive instance eqMaterial3D :: Eq Material3D

-- | Basic unlit material.
type BasicMaterialParams =
  { color :: RGBA
  , opacity :: Number         -- 0.0 to 1.0
  , transparent :: Boolean
  , wireframe :: Boolean
  }

basicMaterial3D :: BasicMaterialParams -> Material3D
basicMaterial3D = BasicMaterial3D

-- | Standard PBR material (metallic-roughness workflow).
type StandardMaterialParams =
  { color :: RGBA
  , roughness :: Number       -- 0.0 (mirror) to 1.0 (diffuse)
  , metalness :: Number       -- 0.0 (dielectric) to 1.0 (metal)
  , emissive :: RGBA
  , emissiveIntensity :: Number
  , opacity :: Number
  , transparent :: Boolean
  , wireframe :: Boolean
  }

standardMaterial3D :: StandardMaterialParams -> Material3D
standardMaterial3D = StandardMaterial3D

-- | Physical material (advanced PBR with clearcoat, transmission, etc.).
type PhysicalMaterialParams =
  { color :: RGBA
  , roughness :: Number
  , metalness :: Number
  , clearcoat :: Number       -- 0.0 to 1.0
  , clearcoatRoughness :: Number
  , ior :: Number             -- Index of refraction (typically 1.0-2.5)
  , transmission :: Number    -- 0.0 to 1.0 (glass-like)
  , thickness :: Meter        -- For transmission volume
  , emissive :: RGBA
  , emissiveIntensity :: Number
  , opacity :: Number
  , transparent :: Boolean
  }

physicalMaterial3D :: PhysicalMaterialParams -> Material3D
physicalMaterial3D = PhysicalMaterial3D
