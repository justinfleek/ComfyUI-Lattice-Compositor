-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // elevation // semantic-elevation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SemanticElevation — meaningful elevation scale for UI depth.
-- |
-- | ## The Problem
-- |
-- | CSS provides box-shadow with raw pixel values, but humans think in
-- | semantic terms: "this card should float above the page", "this modal
-- | should be the topmost layer", "this button should look pressed".
-- |
-- | ## The Solution
-- |
-- | This module provides a bounded, semantic elevation scale (0-5) that:
-- |
-- | - Maps to research-backed shadow configurations
-- | - Provides consistent depth perception across UI
-- | - Scales proportionally for different contexts
-- | - Works with both light and dark themes
-- |
-- | ## Elevation Levels
-- |
-- | | Level | Name     | Use Case                          | Z-Index Range |
-- | |-------|----------|-----------------------------------|---------------|
-- | | 0     | Flat     | Recessed, inset, pressed states   | 0-99          |
-- | | 1     | Raised   | Cards, list items, default state  | 100-199       |
-- | | 2     | Floating | Dropdowns, tooltips, popovers     | 200-299       |
-- | | 3     | Overlay  | Sidebars, drawers, panels         | 300-399       |
-- | | 4     | Modal    | Dialogs, modals                   | 400-499       |
-- | | 5     | Toast    | Notifications, toasts, top layer  | 500-599       |
-- |
-- | ## Research Basis
-- |
-- | Shadow configurations follow Material Design research on perceived
-- | elevation, with modifications for modern aesthetics (softer, more
-- | diffuse shadows characteristic of Linear, Vercel, and similar UIs).
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Elevation.SemanticElevation as SE
-- |
-- | -- Get shadow for a specific elevation
-- | cardShadow = SE.shadowForLevel SE.Raised
-- |
-- | -- Convert to CSS
-- | css = SE.toLegacyCss SE.Modal
-- | ```

module Hydrogen.Schema.Elevation.SemanticElevation
  ( -- * Elevation Level (Atom)
    ElevationLevel(..)
  , allLevels
  , levelToInt
  , levelFromInt
  
  -- * Elevation Names
  , Flat
  , Raised
  , Floating
  , Overlay
  , Modal
  , Toast
  
  -- * Shadow Configuration
  , shadowForLevel
  , shadowForLevelDark
  
  -- * Z-Index Ranges
  , zIndexBase
  , zIndexRange
  
  -- * Conversion (Legacy string generation)
  , toLegacyCss
  , toLegacyCssDark
  
  -- * Comparison
  , isAbove
  , isBelow
  , isAtLevel
  
  -- * Operations
  , raise
  , lower
  , clampLevel
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(LT, GT)
  , show
  , compare
  , negate
  , ($)
  , (==)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  )

import Hydrogen.Schema.Color.RGB (RGBA, rgba)
import Hydrogen.Schema.Elevation.Shadow 
  ( BoxShadow
  , LayeredShadow
  , boxShadow
  , layered
  , noShadow
  , layeredToLegacyCss
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // elevation level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic elevation level — bounded from 0 (flat) to 5 (toast).
-- |
-- | Each level represents a distinct plane in the UI's z-axis hierarchy.
-- | The scale is intentionally limited to prevent elevation inflation
-- | (where everything becomes "important" and nothing stands out).
data ElevationLevel
  = Flat      -- ^ Level 0: Recessed or flush with surface
  | Raised    -- ^ Level 1: Slightly elevated, default for cards
  | Floating  -- ^ Level 2: Dropdowns, tooltips
  | Overlay   -- ^ Level 3: Sidebars, drawers
  | Modal     -- ^ Level 4: Modal dialogs
  | Toast     -- ^ Level 5: Topmost notifications

derive instance eqElevationLevel :: Eq ElevationLevel
derive instance ordElevationLevel :: Ord ElevationLevel

instance showElevationLevel :: Show ElevationLevel where
  show Flat = "flat"
  show Raised = "raised"
  show Floating = "floating"
  show Overlay = "overlay"
  show Modal = "modal"
  show Toast = "toast"

-- | Type aliases for clarity in function signatures
type Flat = ElevationLevel
type Raised = ElevationLevel
type Floating = ElevationLevel
type Overlay = ElevationLevel
type Modal = ElevationLevel
type Toast = ElevationLevel

-- | All elevation levels in ascending order
allLevels :: Array ElevationLevel
allLevels = [Flat, Raised, Floating, Overlay, Modal, Toast]

-- | Convert level to integer (0-5)
levelToInt :: ElevationLevel -> Int
levelToInt Flat = 0
levelToInt Raised = 1
levelToInt Floating = 2
levelToInt Overlay = 3
levelToInt Modal = 4
levelToInt Toast = 5

-- | Convert integer to level (clamped to 0-5)
levelFromInt :: Int -> ElevationLevel
levelFromInt n
  | n < 1 = Flat
  | n == 1 = Raised
  | n == 2 = Floating
  | n == 3 = Overlay
  | n == 4 = Modal
  | n > 4 = Toast
  | true = Raised  -- Default case, should not be reached

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // shadow configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get LayeredShadow for an elevation level (light theme).
-- |
-- | Shadows use multiple layers for realistic depth:
-- | - Ambient shadow: Soft, diffuse background shadow
-- | - Key shadow: Sharper, directional shadow (light from above)
-- |
-- | ## Research Notes
-- |
-- | These configurations follow observations from Linear, Vercel, Stripe,
-- | and other modern UIs. Key characteristics:
-- |
-- | - Lower opacity than Material Design (more subtle)
-- | - Larger blur radii relative to offset (softer edges)
-- | - Negative spread to prevent shadow "halo" effect
shadowForLevel :: ElevationLevel -> LayeredShadow
shadowForLevel Flat = noShadow
shadowForLevel Raised = layered
  [ -- Ambient shadow (soft, large)
    mkShadow 0.0 1.0 3.0 0.0 (shadowColor 10)
    -- Key shadow (sharper, offset)
  , mkShadow 0.0 1.0 2.0 (-1.0) (shadowColor 6)
  ]
shadowForLevel Floating = layered
  [ mkShadow 0.0 4.0 6.0 (-1.0) (shadowColor 10)
  , mkShadow 0.0 2.0 4.0 (-2.0) (shadowColor 6)
  ]
shadowForLevel Overlay = layered
  [ mkShadow 0.0 10.0 15.0 (-3.0) (shadowColor 10)
  , mkShadow 0.0 4.0 6.0 (-4.0) (shadowColor 5)
  ]
shadowForLevel Modal = layered
  [ mkShadow 0.0 20.0 25.0 (-5.0) (shadowColor 10)
  , mkShadow 0.0 8.0 10.0 (-6.0) (shadowColor 4)
  ]
shadowForLevel Toast = layered
  [ mkShadow 0.0 25.0 50.0 (-12.0) (shadowColor 25)
  ]

-- | Get LayeredShadow for an elevation level (dark theme).
-- |
-- | Dark themes require different shadow treatment:
-- | - Higher opacity shadows (to be visible against dark backgrounds)
-- | - Often combined with subtle borders or glows
-- | - Same structure, different color values
shadowForLevelDark :: ElevationLevel -> LayeredShadow
shadowForLevelDark Flat = noShadow
shadowForLevelDark Raised = layered
  [ mkShadow 0.0 1.0 3.0 0.0 (shadowColorDark 20)
  , mkShadow 0.0 1.0 2.0 (-1.0) (shadowColorDark 15)
  ]
shadowForLevelDark Floating = layered
  [ mkShadow 0.0 4.0 6.0 (-1.0) (shadowColorDark 25)
  , mkShadow 0.0 2.0 4.0 (-2.0) (shadowColorDark 15)
  ]
shadowForLevelDark Overlay = layered
  [ mkShadow 0.0 10.0 15.0 (-3.0) (shadowColorDark 30)
  , mkShadow 0.0 4.0 6.0 (-4.0) (shadowColorDark 20)
  ]
shadowForLevelDark Modal = layered
  [ mkShadow 0.0 20.0 25.0 (-5.0) (shadowColorDark 40)
  , mkShadow 0.0 8.0 10.0 (-6.0) (shadowColorDark 25)
  ]
shadowForLevelDark Toast = layered
  [ mkShadow 0.0 25.0 50.0 (-12.0) (shadowColorDark 50)
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // z-index ranges
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the base z-index for an elevation level.
-- |
-- | Each level occupies a 100-unit range, allowing for sub-layering
-- | within a level (e.g., dropdown at 200, dropdown item at 201).
zIndexBase :: ElevationLevel -> Int
zIndexBase level = levelToInt level * 100

-- | Get the z-index range for an elevation level.
-- |
-- | Returns {min, max} for the level's z-index range.
zIndexRange :: ElevationLevel -> { min :: Int, max :: Int }
zIndexRange level =
  let base = zIndexBase level
  in { min: base, max: base + 99 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert elevation level to CSS box-shadow string (light theme).
-- |
-- | NOT an FFI boundary - pure string generation.
toLegacyCss :: ElevationLevel -> String
toLegacyCss = layeredToLegacyCss <<< shadowForLevel

-- | Convert elevation level to CSS box-shadow string (dark theme).
-- |
-- | NOT an FFI boundary - pure string generation.
toLegacyCssDark :: ElevationLevel -> String
toLegacyCssDark = layeredToLegacyCss <<< shadowForLevelDark

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if first level is above second
isAbove :: ElevationLevel -> ElevationLevel -> Boolean
isAbove a b = compare a b == GT

-- | Check if first level is below second
isBelow :: ElevationLevel -> ElevationLevel -> Boolean
isBelow a b = compare a b == LT

-- | Check if two levels are equal
isAtLevel :: ElevationLevel -> ElevationLevel -> Boolean
isAtLevel a b = a == b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Raise elevation by one level (clamped at Toast)
raise :: ElevationLevel -> ElevationLevel
raise level = levelFromInt (levelToInt level + 1)

-- | Lower elevation by one level (clamped at Flat)
lower :: ElevationLevel -> ElevationLevel
lower level = levelFromInt (levelToInt level - 1)

-- | Clamp elevation to valid range
clampLevel :: Int -> ElevationLevel
clampLevel = levelFromInt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Function composition helper
infixr 9 composeFlipped as <<<

composeFlipped :: forall a b c. (b -> c) -> (a -> b) -> a -> c
composeFlipped f g x = f (g x)

-- | Create shadow with standard parameters
mkShadow :: Number -> Number -> Number -> Number -> RGBA -> BoxShadow
mkShadow ox oy blur spread color = boxShadow
  { offsetX: ox
  , offsetY: oy
  , blur: blur
  , spread: spread
  , color: color
  , inset: false
  }

-- | Shadow color for light theme (black with given alpha percentage)
shadowColor :: Int -> RGBA
shadowColor alphaPercent = rgba 0 0 0 alphaPercent

-- | Shadow color for dark theme (pure black with given alpha percentage)
-- |
-- | Dark themes need higher opacity shadows to be visible.
shadowColorDark :: Int -> RGBA
shadowColorDark alphaPercent = rgba 0 0 0 alphaPercent
