-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // material // blur-radius
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BlurRadius - Gaussian blur amount.
-- |
-- | Measured in pixels, representing the radius of the blur kernel.
-- | Used for backdrop blur, shadow blur, and filter effects.
-- |
-- | Range: 0 to finite (clamps at 0, no upper bound but must remain finite)
-- | - **0**: No blur (sharp)
-- | - **10**: Subtle blur
-- | - **50**: Heavy blur
-- | - **100+**: Extreme blur
-- |
-- | Note: Very large values may impact performance significantly.

module Hydrogen.Schema.Material.BlurRadius
  ( BlurRadius
  , blurRadius
  , unwrap
  , toNumber
  , bounds
  -- Constants
  , none
  , subtle
  , moderate
  , heavy
  , extreme
  -- Operations
  , blend
  , lerp
  , scale
  , add
  , subtract
  , toLegacyCss
  -- Predicates
  , isSharp
  , isSubtle
  , isModerate
  , isHeavy
  , isExtreme
  , atLeast
  , lessThan
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (==)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // blur-radius
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blur radius in pixels (0 to finite)
-- |
-- | Represents the radius of a Gaussian blur kernel. Larger values create
-- | more pronounced blurring effects.
newtype BlurRadius = BlurRadius Number

derive instance eqBlurRadius :: Eq BlurRadius
derive instance ordBlurRadius :: Ord BlurRadius

instance showBlurRadius :: Show BlurRadius where
  show (BlurRadius r) = show r <> "px"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a blur radius, clamping to 0 minimum and ensuring finite
blurRadius :: Number -> BlurRadius
blurRadius n = BlurRadius (Bounded.clampNumberMin 0.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No blur (sharp)
none :: BlurRadius
none = BlurRadius 0.0

-- | Subtle blur (10px)
subtle :: BlurRadius
subtle = BlurRadius 10.0

-- | Moderate blur (25px)
moderate :: BlurRadius
moderate = BlurRadius 25.0

-- | Heavy blur (50px)
heavy :: BlurRadius
heavy = BlurRadius 50.0

-- | Extreme blur (100px)
extreme :: BlurRadius
extreme = BlurRadius 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend two blur radii with weight (0.0 = all first, 1.0 = all second)
-- |
-- | Linear interpolation for animated blur effects:
-- | ```purescript
-- | blend 0.5 none heavy  -- BlurRadius 25px (midpoint)
-- | ```
blend :: Number -> BlurRadius -> BlurRadius -> BlurRadius
blend weight (BlurRadius a) (BlurRadius b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
  in blurRadius (a * (1.0 - w) + b * w)

-- | Linear interpolation (standard lerp signature)
lerp :: BlurRadius -> BlurRadius -> Number -> BlurRadius
lerp from to t = blend t from to

-- | Scale blur radius by a factor
-- |
-- | Useful for resolution-aware adjustments:
-- | ```purescript
-- | scale 2.0 subtle  -- BlurRadius 20px
-- | scale 0.5 heavy   -- BlurRadius 25px
-- | ```
scale :: Number -> BlurRadius -> BlurRadius
scale factor (BlurRadius r) = blurRadius (r * factor)

-- | Add to blur radius (clamped at 0)
add :: Number -> BlurRadius -> BlurRadius
add amount (BlurRadius r) = blurRadius (r + amount)

-- | Subtract from blur radius (clamped at 0)
subtract :: Number -> BlurRadius -> BlurRadius
subtract amount (BlurRadius r) = blurRadius (r - amount)

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS blur() filter value
-- |
-- | For use in CSS filter property:
-- | ```purescript
-- | toLegacyCss subtle  -- "blur(10px)"
-- | ```
toLegacyCss :: BlurRadius -> String
toLegacyCss (BlurRadius r) = "blur(" <> show r <> "px)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if blur is sharp (no blur, radius = 0)
-- |
-- | Sharp elements have no Gaussian blur applied:
-- | ```purescript
-- | isSharp none    -- true
-- | isSharp subtle  -- false
-- | ```
isSharp :: BlurRadius -> Boolean
isSharp (BlurRadius r) = r == 0.0

-- | Check if blur is subtle (0 < radius <= 15px)
-- |
-- | Subtle blur for soft shadows and gentle effects:
-- | ```purescript
-- | isSubtle subtle             -- true (10px)
-- | isSubtle (blurRadius 5.0)   -- true
-- | isSubtle none               -- false
-- | ```
isSubtle :: BlurRadius -> Boolean
isSubtle (BlurRadius r) = r > 0.0 && r <= 15.0

-- | Check if blur is moderate (15px < radius <= 35px)
-- |
-- | Moderate blur for backdrop effects and depth:
-- | ```purescript
-- | isModerate moderate         -- true (25px)
-- | isModerate (blurRadius 30.0) -- true
-- | isModerate subtle           -- false
-- | ```
isModerate :: BlurRadius -> Boolean
isModerate (BlurRadius r) = r > 15.0 && r <= 35.0

-- | Check if blur is heavy (35px < radius <= 75px)
-- |
-- | Heavy blur for strong frosted glass and emphasis effects:
-- | ```purescript
-- | isHeavy heavy              -- true (50px)
-- | isHeavy (blurRadius 60.0)  -- true
-- | isHeavy moderate           -- false
-- | ```
isHeavy :: BlurRadius -> Boolean
isHeavy (BlurRadius r) = r > 35.0 && r <= 75.0

-- | Check if blur is extreme (> 75px)
-- |
-- | Extreme blur for dramatic visual effects:
-- | ```purescript
-- | isExtreme extreme            -- true (100px)
-- | isExtreme (blurRadius 150.0) -- true
-- | isExtreme heavy              -- false
-- | ```
isExtreme :: BlurRadius -> Boolean
isExtreme (BlurRadius r) = r > 75.0

-- | Check if blur radius is at least a given value
-- |
-- | Useful for threshold checks in rendering pipelines:
-- | ```purescript
-- | atLeast 20.0 moderate  -- true (25px >= 20px)
-- | atLeast 30.0 subtle    -- false (10px < 30px)
-- | ```
atLeast :: Number -> BlurRadius -> Boolean
atLeast threshold (BlurRadius r) = r >= threshold

-- | Check if blur radius is less than a given value
-- |
-- | Useful for performance optimizations (skip blur if negligible):
-- | ```purescript
-- | lessThan 5.0 (blurRadius 3.0)  -- true
-- | lessThan 5.0 subtle            -- false (10px >= 5px)
-- | ```
lessThan :: Number -> BlurRadius -> Boolean
lessThan threshold (BlurRadius r) = r < threshold

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: BlurRadius -> Number
unwrap (BlurRadius r) = r

-- | Convert to Number (passthrough for this type)
toNumber :: BlurRadius -> Number
toNumber (BlurRadius r) = r

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1000.0 "blurRadius" "Gaussian blur radius in pixels"
