-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // material // neumorphism
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Neumorphism - soft UI / "soft glass" effect compound.
-- |
-- | Neumorphism creates a soft, extruded plastic appearance using
-- | dual shadows (light and dark) to simulate depth on a uniform
-- | background. Popular in 2019-2020 UI trends.
-- |
-- | ## Visual Effect
-- |
-- | - Light shadow on one side (simulates light source reflection)
-- | - Dark shadow on opposite side (simulates cast shadow)
-- | - Background color matches parent (crucial for the effect)
-- | - Creates "soft" raised or inset appearance
-- |
-- | ## Variants
-- |
-- | - **Raised**: Element appears to protrude from surface
-- | - **Inset**: Element appears pressed into surface
-- | - **Flat**: Subtle, almost imperceptible depth
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Color.RGB
-- | - Hydrogen.Schema.Bounded

module Hydrogen.Schema.Material.Neumorphism
  ( -- * Neumorphism Variant
    NeumorphismVariant(..)
  
  -- * Types
  , Neumorphism(Neumorphism)
  , NeumorphismConfig
  
  -- * Constructors
  , neumorphism
  , neumorphismRaised
  , neumorphismInset
  , neumorphismFlat
  
  -- * Accessors
  , variant
  , backgroundColor
  , lightShadowColor
  , darkShadowColor
  , shadowDistance
  , shadowBlur
  , intensity
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

import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Color.RGB (rgb) as RGB
import Hydrogen.Schema.Bounded (clampNumber) as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // variant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Neumorphism appearance variant.
data NeumorphismVariant
  = Raised     -- ^ Element protrudes from surface
  | Inset      -- ^ Element pressed into surface
  | Flat       -- ^ Subtle, minimal depth
  | Concave    -- ^ Curved inward surface
  | Convex     -- ^ Curved outward surface

derive instance eqNeumorphismVariant :: Eq NeumorphismVariant
derive instance ordNeumorphismVariant :: Ord NeumorphismVariant

instance showNeumorphismVariant :: Show NeumorphismVariant where
  show Raised = "raised"
  show Inset = "inset"
  show Flat = "flat"
  show Concave = "concave"
  show Convex = "convex"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // neumorphism
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration record for creating Neumorphism
type NeumorphismConfig =
  { backgroundColor :: RGB        -- ^ Background color (must match parent)
  , lightShadowColor :: RGB       -- ^ Light shadow (usually white-ish)
  , darkShadowColor :: RGB        -- ^ Dark shadow (darker than background)
  , shadowDistance :: Number      -- ^ Shadow offset in pixels
  , shadowBlur :: Number          -- ^ Shadow blur radius
  , intensity :: Number           -- ^ Effect intensity (0.0-1.0)
  }

-- | Neumorphism - soft UI effect compound.
-- |
-- | Describes dual-shadow soft plastic appearance.
newtype Neumorphism = Neumorphism
  { variant :: NeumorphismVariant
  , backgroundColor :: RGB
  , lightShadowColor :: RGB
  , darkShadowColor :: RGB
  , shadowDistance :: Number
  , shadowBlur :: Number
  , intensity :: Number           -- ^ 0.0 = invisible, 1.0 = full effect
  }

derive instance eqNeumorphism :: Eq Neumorphism

instance showNeumorphism :: Show Neumorphism where
  show (Neumorphism n) = 
    "(Neumorphism " <> show n.variant 
      <> " bg:" <> show n.backgroundColor
      <> " dist:" <> show n.shadowDistance
      <> " blur:" <> show n.shadowBlur
      <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create neumorphism from full configuration
neumorphism :: NeumorphismVariant -> NeumorphismConfig -> Neumorphism
neumorphism var cfg = Neumorphism
  { variant: var
  , backgroundColor: cfg.backgroundColor
  , lightShadowColor: cfg.lightShadowColor
  , darkShadowColor: cfg.darkShadowColor
  , shadowDistance: Bounded.clampNumber 0.0 100.0 cfg.shadowDistance
  , shadowBlur: Bounded.clampNumber 0.0 200.0 cfg.shadowBlur
  , intensity: Bounded.clampNumber 0.0 1.0 cfg.intensity
  }

-- | Create raised neumorphism with default colors
-- |
-- | Uses a light gray background with white/dark gray shadows.
neumorphismRaised :: RGB -> Neumorphism
neumorphismRaised bg = Neumorphism
  { variant: Raised
  , backgroundColor: bg
  , lightShadowColor: RGB.rgb 255 255 255
  , darkShadowColor: RGB.rgb 163 177 198
  , shadowDistance: 10.0
  , shadowBlur: 20.0
  , intensity: 0.5
  }

-- | Create inset neumorphism (pressed appearance)
neumorphismInset :: RGB -> Neumorphism
neumorphismInset bg = Neumorphism
  { variant: Inset
  , backgroundColor: bg
  , lightShadowColor: RGB.rgb 255 255 255
  , darkShadowColor: RGB.rgb 163 177 198
  , shadowDistance: 5.0
  , shadowBlur: 10.0
  , intensity: 0.4
  }

-- | Create flat neumorphism (minimal depth)
neumorphismFlat :: RGB -> Neumorphism
neumorphismFlat bg = Neumorphism
  { variant: Flat
  , backgroundColor: bg
  , lightShadowColor: RGB.rgb 255 255 255
  , darkShadowColor: RGB.rgb 163 177 198
  , shadowDistance: 3.0
  , shadowBlur: 6.0
  , intensity: 0.25
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get variant
variant :: Neumorphism -> NeumorphismVariant
variant (Neumorphism n) = n.variant

-- | Get background color
backgroundColor :: Neumorphism -> RGB
backgroundColor (Neumorphism n) = n.backgroundColor

-- | Get light shadow color
lightShadowColor :: Neumorphism -> RGB
lightShadowColor (Neumorphism n) = n.lightShadowColor

-- | Get dark shadow color
darkShadowColor :: Neumorphism -> RGB
darkShadowColor (Neumorphism n) = n.darkShadowColor

-- | Get shadow distance
shadowDistance :: Neumorphism -> Number
shadowDistance (Neumorphism n) = n.shadowDistance

-- | Get shadow blur
shadowBlur :: Neumorphism -> Number
shadowBlur (Neumorphism n) = n.shadowBlur

-- | Get intensity
intensity :: Neumorphism -> Number
intensity (Neumorphism n) = n.intensity
