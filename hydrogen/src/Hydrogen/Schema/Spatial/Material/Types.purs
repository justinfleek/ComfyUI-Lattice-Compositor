-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // spatial // material // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Material Types — 3D material definitions for PBR and stylized rendering.
-- |
-- | Materials define how surfaces interact with light:
-- |
-- | ## StandardPBR
-- | Full physically-based rendering material with metallic/roughness workflow.
-- | Industry standard for games, film, and visualization.
-- |
-- | ## UnlitMaterial
-- | No lighting calculations. Shows albedo/texture as-is.
-- | Used for UI, emissive surfaces, or post-processing.
-- |
-- | ## TransparentMaterial
-- | Glass, water, and translucent materials.
-- | Supports transmission, IOR, and thin-surface approximations.
-- |
-- | ## SubsurfaceMaterial
-- | Skin, wax, marble, and other translucent solids.
-- | Light scatters within the material.
-- |
-- | ## ClothMaterial
-- | Fabric rendering with sheen and subsurface.
-- | Specialized for soft goods (clothing, upholstery).
-- |
-- | ## HairMaterial
-- | Hair and fur rendering.
-- | Specialized anisotropic shading for fiber geometry.
-- |
-- | ## ToonMaterial
-- | Cel-shaded, non-photorealistic rendering.
-- | Hard shadow edges, flat color bands.

module Hydrogen.Schema.Spatial.Material.Types
  ( -- * Material Types
    StandardPBR(..)
  , UnlitMaterial(..)
  , TransparentMaterial(..)
  , SubsurfaceMaterial(..)
  , ClothMaterial(..)
  , HairMaterial(..)
  , ToonMaterial(..)
  
  -- * Unified Material
  , Material(..)
  
  -- * Constructors
  , standardPBR
  , unlit
  , transparent
  , glass
  , subsurface
  , skin
  , cloth
  , hair
  , toon
  
  -- * Presets
  , gold
  , chrome
  , plastic
  , emissive
  
  -- * Accessors
  , materialAlbedo
  , isTransparent
  , isDoubleSided
  
  -- * Blending
  , BlendMode(..)
  , AlphaMode(..)
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)
import Hydrogen.Schema.Spatial.Roughness (Roughness)
import Hydrogen.Schema.Spatial.Roughness as Roughness
import Hydrogen.Schema.Spatial.Metallic (Metallic)
import Hydrogen.Schema.Spatial.Metallic as Metallic
import Hydrogen.Schema.Spatial.Reflectance (Reflectance)
import Hydrogen.Schema.Spatial.ClearCoat (ClearCoat)
import Hydrogen.Schema.Spatial.ClearCoatRoughness (ClearCoatRoughness)
import Hydrogen.Schema.Spatial.Anisotropy (Anisotropy)
import Hydrogen.Schema.Spatial.Transmission (Transmission)
import Hydrogen.Schema.Spatial.Transmission as Transmission
import Hydrogen.Schema.Spatial.IOR (IOR)
import Hydrogen.Schema.Spatial.IOR as IOR
import Hydrogen.Schema.Spatial.Subsurface (Subsurface)
import Hydrogen.Schema.Spatial.Subsurface as SSS
import Hydrogen.Schema.Spatial.Sheen (Sheen)
import Hydrogen.Schema.Spatial.EmissiveStrength (EmissiveStrength)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // blend modes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend mode for transparent materials
data BlendMode
  = BlendOpaque      -- ^ No blending (default)
  | BlendAlpha       -- ^ Standard alpha blending
  | BlendPremultiplied -- ^ Pre-multiplied alpha
  | BlendAdditive    -- ^ Additive blending (glow effects)
  | BlendMultiply    -- ^ Multiply blending (shadows)

derive instance eqBlendMode :: Eq BlendMode
derive instance ordBlendMode :: Ord BlendMode

instance showBlendMode :: Show BlendMode where
  show BlendOpaque = "BlendOpaque"
  show BlendAlpha = "BlendAlpha"
  show BlendPremultiplied = "BlendPremultiplied"
  show BlendAdditive = "BlendAdditive"
  show BlendMultiply = "BlendMultiply"

-- | Alpha handling mode
data AlphaMode
  = AlphaOpaque      -- ^ Ignore alpha, fully opaque
  | AlphaMask        -- ^ Binary cutout at threshold
  | AlphaBlend       -- ^ Smooth alpha blending

derive instance eqAlphaMode :: Eq AlphaMode
derive instance ordAlphaMode :: Ord AlphaMode

instance showAlphaMode :: Show AlphaMode where
  show AlphaOpaque = "AlphaOpaque"
  show AlphaMask = "AlphaMask"
  show AlphaBlend = "AlphaBlend"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // standard pbr
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard PBR material (metallic/roughness workflow)
-- |
-- | The industry-standard physically-based material model.
-- | Compatible with glTF, USD, Three.js, Unity, Unreal, Blender.
newtype StandardPBR = StandardPBR
  { albedo :: Vec3 Number           -- ^ Base color (linear RGB, 0-1)
  , roughness :: Roughness          -- ^ Surface roughness (0=mirror, 1=matte)
  , metallic :: Metallic            -- ^ Metallic factor (0=dielectric, 1=metal)
  , reflectance :: Maybe Reflectance -- ^ Dielectric reflectance (F0)
  , clearCoat :: Maybe ClearCoat    -- ^ Clear coat layer intensity
  , clearCoatRoughness :: Maybe ClearCoatRoughness
  , anisotropy :: Maybe Anisotropy  -- ^ Anisotropic reflection
  , emissive :: Maybe (Vec3 Number) -- ^ Emissive color (linear RGB)
  , emissiveStrength :: Maybe EmissiveStrength
  , alphaMode :: AlphaMode
  , alphaCutoff :: Number           -- ^ Cutoff for AlphaMask mode
  , doubleSided :: Boolean
  }

derive instance eqStandardPBR :: Eq StandardPBR

instance showStandardPBR :: Show StandardPBR where
  show (StandardPBR m) =
    "StandardPBR { albedo: " <> show m.albedo <>
    ", roughness: " <> show m.roughness <>
    ", metallic: " <> show m.metallic <> " }"

-- | Create a standard PBR material with minimal parameters
standardPBR :: Vec3 Number -> Roughness -> Metallic -> StandardPBR
standardPBR albedo roughness metallic = StandardPBR
  { albedo
  , roughness
  , metallic
  , reflectance: Nothing
  , clearCoat: Nothing
  , clearCoatRoughness: Nothing
  , anisotropy: Nothing
  , emissive: Nothing
  , emissiveStrength: Nothing
  , alphaMode: AlphaOpaque
  , alphaCutoff: 0.5
  , doubleSided: false
  }

-- | Gold material preset
gold :: StandardPBR
gold = StandardPBR
  { albedo: vec3 1.0 0.765 0.336  -- Gold color
  , roughness: Roughness.glossy
  , metallic: Metallic.metal
  , reflectance: Nothing
  , clearCoat: Nothing
  , clearCoatRoughness: Nothing
  , anisotropy: Nothing
  , emissive: Nothing
  , emissiveStrength: Nothing
  , alphaMode: AlphaOpaque
  , alphaCutoff: 0.5
  , doubleSided: false
  }

-- | Chrome material preset (mirror-like metal)
chrome :: StandardPBR
chrome = StandardPBR
  { albedo: vec3 0.9 0.9 0.9  -- Neutral bright
  , roughness: Roughness.mirror
  , metallic: Metallic.metal
  , reflectance: Nothing
  , clearCoat: Nothing
  , clearCoatRoughness: Nothing
  , anisotropy: Nothing
  , emissive: Nothing
  , emissiveStrength: Nothing
  , alphaMode: AlphaOpaque
  , alphaCutoff: 0.5
  , doubleSided: false
  }

-- | Plastic material preset (dielectric with medium roughness)
plastic :: Vec3 Number -> StandardPBR
plastic color = StandardPBR
  { albedo: color
  , roughness: Roughness.semiRough
  , metallic: Metallic.dielectric
  , reflectance: Nothing
  , clearCoat: Nothing
  , clearCoatRoughness: Nothing
  , anisotropy: Nothing
  , emissive: Nothing
  , emissiveStrength: Nothing
  , alphaMode: AlphaOpaque
  , alphaCutoff: 0.5
  , doubleSided: false
  }

-- | Emissive material preset (glowing surface)
emissive :: Vec3 Number -> Vec3 Number -> EmissiveStrength -> StandardPBR
emissive albedo emissiveColor strength = StandardPBR
  { albedo
  , roughness: Roughness.matte
  , metallic: Metallic.dielectric
  , reflectance: Nothing
  , clearCoat: Nothing
  , clearCoatRoughness: Nothing
  , anisotropy: Nothing
  , emissive: Just emissiveColor
  , emissiveStrength: Just strength
  , alphaMode: AlphaOpaque
  , alphaCutoff: 0.5
  , doubleSided: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // unlit material
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unlit material (no lighting calculations)
-- |
-- | Displays color/texture without any lighting.
-- | Used for UI elements, emissive displays, and post-processing.
newtype UnlitMaterial = UnlitMaterial
  { color :: Vec3 Number            -- ^ Display color (linear RGB, 0-1)
  , opacity :: Number               -- ^ Opacity (0-1)
  , blendMode :: BlendMode
  , doubleSided :: Boolean
  }

derive instance eqUnlitMaterial :: Eq UnlitMaterial

instance showUnlitMaterial :: Show UnlitMaterial where
  show (UnlitMaterial m) =
    "UnlitMaterial { color: " <> show m.color <>
    ", opacity: " <> show m.opacity <> " }"

-- | Create an unlit material
unlit :: Vec3 Number -> UnlitMaterial
unlit color = UnlitMaterial
  { color
  , opacity: 1.0
  , blendMode: BlendOpaque
  , doubleSided: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // transparent material
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transparent material (glass, water, crystals)
-- |
-- | Supports refraction, transmission, and thin-surface approximations.
newtype TransparentMaterial = TransparentMaterial
  { albedo :: Vec3 Number           -- ^ Tint color
  , roughness :: Roughness          -- ^ Surface roughness (affects refraction blur)
  , transmission :: Transmission    -- ^ How much light passes through
  , ior :: IOR                      -- ^ Index of refraction
  , thickness :: Number             -- ^ Volume thickness (for attenuation)
  , attenuationColor :: Vec3 Number -- ^ Color absorbed over distance
  , attenuationDistance :: Number   -- ^ Distance for attenuation
  , doubleSided :: Boolean
  }

derive instance eqTransparentMaterial :: Eq TransparentMaterial

instance showTransparentMaterial :: Show TransparentMaterial where
  show (TransparentMaterial m) =
    "TransparentMaterial { transmission: " <> show m.transmission <>
    ", ior: " <> show m.ior <> " }"

-- | Create a transparent material
transparent :: Vec3 Number -> Transmission -> IOR -> TransparentMaterial
transparent albedo transmission ior = TransparentMaterial
  { albedo
  , roughness: Roughness.mirror
  , transmission
  , ior
  , thickness: 0.0
  , attenuationColor: vec3 1.0 1.0 1.0
  , attenuationDistance: 0.0
  , doubleSided: true
  }

-- | Create a glass material (preset)
glass :: TransparentMaterial
glass = TransparentMaterial
  { albedo: vec3 1.0 1.0 1.0
  , roughness: Roughness.mirror
  , transmission: Transmission.transparent
  , ior: IOR.glass
  , thickness: 0.01
  , attenuationColor: vec3 1.0 1.0 1.0
  , attenuationDistance: 1.0
  , doubleSided: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // subsurface material
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subsurface scattering material (skin, wax, marble)
-- |
-- | Light penetrates the surface and scatters within.
newtype SubsurfaceMaterial = SubsurfaceMaterial
  { albedo :: Vec3 Number           -- ^ Surface color
  , roughness :: Roughness
  , subsurface :: Subsurface        -- ^ Subsurface amount
  , subsurfaceColor :: Vec3 Number  -- ^ Scatter color (often reddish for skin)
  , subsurfaceRadius :: Vec3 Number -- ^ Scatter radius per channel (RGB)
  , doubleSided :: Boolean
  }

derive instance eqSubsurfaceMaterial :: Eq SubsurfaceMaterial

instance showSubsurfaceMaterial :: Show SubsurfaceMaterial where
  show (SubsurfaceMaterial m) =
    "SubsurfaceMaterial { subsurface: " <> show m.subsurface <>
    ", subsurfaceColor: " <> show m.subsurfaceColor <> " }"

-- | Create a subsurface material
subsurface :: Vec3 Number -> Subsurface -> Vec3 Number -> SubsurfaceMaterial
subsurface albedo sss subsurfaceColor = SubsurfaceMaterial
  { albedo
  , roughness: Roughness.semiRough
  , subsurface: sss
  , subsurfaceColor
  , subsurfaceRadius: vec3 1.0 0.2 0.1  -- Default RGB radii
  , doubleSided: false
  }

-- | Create a skin material (preset)
skin :: Vec3 Number -> SubsurfaceMaterial
skin albedo = SubsurfaceMaterial
  { albedo
  , roughness: Roughness.semiRough
  , subsurface: SSS.moderate
  , subsurfaceColor: vec3 0.8 0.2 0.1  -- Reddish undertone
  , subsurfaceRadius: vec3 1.0 0.4 0.1
  , doubleSided: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // cloth material
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cloth material (fabric rendering)
-- |
-- | Specialized for soft goods with sheen and subsurface.
newtype ClothMaterial = ClothMaterial
  { albedo :: Vec3 Number           -- ^ Fabric color
  , roughness :: Roughness          -- ^ Surface roughness
  , sheen :: Sheen                  -- ^ Sheen intensity
  , sheenColor :: Vec3 Number       -- ^ Sheen tint
  , subsurface :: Maybe Subsurface  -- ^ Optional subsurface for thin fabrics
  , doubleSided :: Boolean
  }

derive instance eqClothMaterial :: Eq ClothMaterial

instance showClothMaterial :: Show ClothMaterial where
  show (ClothMaterial m) =
    "ClothMaterial { albedo: " <> show m.albedo <>
    ", sheen: " <> show m.sheen <> " }"

-- | Create a cloth material
cloth :: Vec3 Number -> Sheen -> ClothMaterial
cloth albedo sheen = ClothMaterial
  { albedo
  , roughness: Roughness.semiRough
  , sheen
  , sheenColor: vec3 1.0 1.0 1.0
  , subsurface: Nothing
  , doubleSided: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // hair material
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hair material (hair and fur rendering)
-- |
-- | Specialized anisotropic shading for fiber geometry.
newtype HairMaterial = HairMaterial
  { baseColor :: Vec3 Number        -- ^ Base hair color
  , roughness :: Roughness          -- ^ Roughness along fiber
  , melanin :: Number               -- ^ Melanin amount (0-1, for realistic hair)
  , melaninRedness :: Number        -- ^ Pheomelanin ratio (0-1)
  , scatter :: Number               -- ^ Internal scatter (0-1)
  , doubleSided :: Boolean
  }

derive instance eqHairMaterial :: Eq HairMaterial

instance showHairMaterial :: Show HairMaterial where
  show (HairMaterial m) =
    "HairMaterial { baseColor: " <> show m.baseColor <>
    ", melanin: " <> show m.melanin <> " }"

-- | Create a hair material
hair :: Vec3 Number -> Roughness -> HairMaterial
hair baseColor roughness = HairMaterial
  { baseColor
  , roughness
  , melanin: 0.5
  , melaninRedness: 0.5
  , scatter: 0.0
  , doubleSided: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // toon material
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toon material (cel-shaded rendering)
-- |
-- | Non-photorealistic rendering with hard shadow edges.
newtype ToonMaterial = ToonMaterial
  { baseColor :: Vec3 Number        -- ^ Base color
  , shadowColor :: Vec3 Number      -- ^ Shadow color
  , highlightColor :: Vec3 Number   -- ^ Highlight color
  , shadowThreshold :: Number       -- ^ Shadow cutoff (0-1)
  , highlightThreshold :: Number    -- ^ Highlight cutoff (0-1)
  , outlineWidth :: Number          -- ^ Outline thickness
  , outlineColor :: Vec3 Number     -- ^ Outline color
  , gradientSteps :: Int            -- ^ Number of color bands (1 = flat)
  }

derive instance eqToonMaterial :: Eq ToonMaterial

instance showToonMaterial :: Show ToonMaterial where
  show (ToonMaterial m) =
    "ToonMaterial { baseColor: " <> show m.baseColor <>
    ", gradientSteps: " <> show m.gradientSteps <> " }"

-- | Create a toon material
toon :: Vec3 Number -> ToonMaterial
toon baseColor = ToonMaterial
  { baseColor
  , shadowColor: vec3 0.3 0.3 0.4
  , highlightColor: vec3 1.0 1.0 1.0
  , shadowThreshold: 0.5
  , highlightThreshold: 0.9
  , outlineWidth: 0.002
  , outlineColor: vec3 0.0 0.0 0.0
  , gradientSteps: 3
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // unified material
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unified material type (sum of all material kinds)
data Material
  = MatStandardPBR StandardPBR
  | MatUnlit UnlitMaterial
  | MatTransparent TransparentMaterial
  | MatSubsurface SubsurfaceMaterial
  | MatCloth ClothMaterial
  | MatHair HairMaterial
  | MatToon ToonMaterial

derive instance eqMaterial :: Eq Material

instance showMaterial :: Show Material where
  show (MatStandardPBR m) = show m
  show (MatUnlit m) = show m
  show (MatTransparent m) = show m
  show (MatSubsurface m) = show m
  show (MatCloth m) = show m
  show (MatHair m) = show m
  show (MatToon m) = show m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the albedo/base color of any material
materialAlbedo :: Material -> Vec3 Number
materialAlbedo (MatStandardPBR (StandardPBR m)) = m.albedo
materialAlbedo (MatUnlit (UnlitMaterial m)) = m.color
materialAlbedo (MatTransparent (TransparentMaterial m)) = m.albedo
materialAlbedo (MatSubsurface (SubsurfaceMaterial m)) = m.albedo
materialAlbedo (MatCloth (ClothMaterial m)) = m.albedo
materialAlbedo (MatHair (HairMaterial m)) = m.baseColor
materialAlbedo (MatToon (ToonMaterial m)) = m.baseColor

-- | Check if a material is transparent
isTransparent :: Material -> Boolean
isTransparent (MatTransparent _) = true
isTransparent (MatStandardPBR (StandardPBR m)) = m.alphaMode /= AlphaOpaque
isTransparent (MatUnlit (UnlitMaterial m)) = m.opacity < 1.0
isTransparent _ = false

-- | Check if a material is double-sided
isDoubleSided :: Material -> Boolean
isDoubleSided (MatStandardPBR (StandardPBR m)) = m.doubleSided
isDoubleSided (MatUnlit (UnlitMaterial m)) = m.doubleSided
isDoubleSided (MatTransparent (TransparentMaterial m)) = m.doubleSided
isDoubleSided (MatSubsurface (SubsurfaceMaterial m)) = m.doubleSided
isDoubleSided (MatCloth (ClothMaterial m)) = m.doubleSided
isDoubleSided (MatHair (HairMaterial m)) = m.doubleSided
isDoubleSided (MatToon _) = false
