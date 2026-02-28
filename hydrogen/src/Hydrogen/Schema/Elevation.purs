-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // schema // elevation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Elevation pillar — depth, shadow, and visual hierarchy.
-- |
-- | ## Physical Model
-- |
-- | Elevation simulates the z-axis in a 2D interface. Higher elevation means:
-- |
-- | - **Closer to light source** → More prominent shadow
-- | - **Above other elements** → Higher z-index
-- | - **More visual emphasis** → Draws user attention
-- |
-- | ## Atoms
-- |
-- | This pillar provides concrete, typed atoms:
-- |
-- | - **Shadow**: Box shadow parameters (offset, blur, spread, color)
-- | - **ZIndex**: Stacking order integers
-- |
-- | ## Concrete Values, Not Semantics
-- |
-- | These atoms are **concrete typed parameters**. Semantic elevation scales
-- | ("flat", "raised", "floating", "modal") belong in BrandSchema where the
-- | brand defines what each level means for their design system.
-- |
-- | ```purescript
-- | -- BrandSchema defines semantic elevation
-- | brand.elevationCard = Shadow.layered
-- |   [ Shadow.boxShadow { offsetX: 0.0, offsetY: 1.0, blur: 3.0, ... }
-- |   , Shadow.boxShadow { offsetX: 0.0, offsetY: 4.0, blur: 6.0, ... }
-- |   ]
-- |
-- | brand.elevationModal = Shadow.layered
-- |   [ Shadow.boxShadow { offsetX: 0.0, offsetY: 10.0, blur: 25.0, ... }
-- |   ]
-- |
-- | brand.zIndexDropdown = ZIndex.z 100
-- | brand.zIndexModal = ZIndex.z 1000
-- | ```
-- |
-- | ## Usage
-- |
-- | Always use qualified imports:
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Elevation.Shadow as Shadow
-- | import Hydrogen.Schema.Elevation.ZIndex as ZIndex
-- |
-- | myShadow :: Shadow.BoxShadow
-- | myShadow = Shadow.boxShadow
-- |   { offsetX: 0.0
-- |   , offsetY: 4.0
-- |   , blur: 8.0
-- |   , spread: 0.0
-- |   , color: Color.rgba 0 0 0 0.15
-- |   , inset: false
-- |   }
-- |
-- | myZIndex :: ZIndex.ZIndex
-- | myZIndex = ZIndex.z 50
-- | ```
-- |
-- | ## Related Pillars
-- |
-- | - **Color.Glow**: Emissive light effects (outward glow)
-- | - **Geometry.Transform**: 3D transforms for perspective effects
-- | - **Dimension.Camera**: 3D camera for true depth rendering

module Hydrogen.Schema.Elevation
  ( -- * Shadow (re-export types only)
    module Shadow
  
  -- * ZIndex (re-export types only)
  , module ZIndex
  ) where

-- Re-export only types to avoid function name conflicts.
-- Users should import submodules qualified for functions:
--   import Hydrogen.Schema.Elevation.Shadow as Shadow
--   import Hydrogen.Schema.Elevation.ZIndex as ZIndex

import Hydrogen.Schema.Elevation.Shadow
  ( BoxShadow
  , DropShadow
  , LayeredShadow
  , ShadowOffset
  ) as Shadow

import Hydrogen.Schema.Elevation.ZIndex
  ( ZIndex(..)
  ) as ZIndex
