-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // temporal // cubic-bezier-easing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CubicBezierEasing — Molecule composing bezier control points for easing curves.
-- |
-- | ## CSS cubic-bezier()
-- |
-- | The standard timing function for CSS animations:
-- |   cubic-bezier(x1, y1, x2, y2)
-- |
-- | The curve goes from (0,0) to (1,1), with control points P1 and P2.
-- |
-- | ## Standard CSS Keywords
-- |
-- | - **ease**: (0.25, 0.1, 0.25, 1.0)
-- | - **ease-in**: (0.42, 0, 1, 1)
-- | - **ease-out**: (0, 0, 0.58, 1)
-- | - **ease-in-out**: (0.42, 0, 0.58, 1)
-- | - **linear**: (0, 0, 1, 1)

module Hydrogen.Schema.Temporal.CubicBezierEasing
  ( CubicBezierEasing(..)
  , cubicBezier
  , cubicBezierFromNumbers
  
  -- * Accessors
  , getX1
  , getY1
  , getX2
  , getY2
  
  -- * CSS Export
  , toLegacyCss
  
  -- * Standard Presets
  , linear
  , ease
  , easeIn
  , easeOut
  , easeInOut
  
  -- * Extended Presets
  , easeInQuad
  , easeOutQuad
  , easeInOutQuad
  , easeInCubic
  , easeOutCubic
  , easeInOutCubic
  , easeInQuart
  , easeOutQuart
  , easeInOutQuart
  , easeInQuint
  , easeOutQuint
  , easeInOutQuint
  , easeInExpo
  , easeOutExpo
  , easeInOutExpo
  , easeInCirc
  , easeOutCirc
  , easeInOutCirc
  , easeInBack
  , easeOutBack
  , easeInOutBack
  
  -- * Sinusoidal Presets
  , easeInSine
  , easeOutSine
  , easeInOutSine
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (<>)
  )

import Hydrogen.Schema.Temporal.BezierParam
  ( CubicX1
  , CubicY1
  , CubicX2
  , CubicY2
  , cubicX1
  , cubicY1
  , cubicX2
  , cubicY2
  , unwrapCubicX1
  , unwrapCubicY1
  , unwrapCubicX2
  , unwrapCubicY2
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // cubic bezier easing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete cubic bezier easing curve definition
-- |
-- | Composed of four control point coordinates:
-- | - P0 = (0, 0) — implicit start
-- | - P1 = (x1, y1) — first control point
-- | - P2 = (x2, y2) — second control point
-- | - P3 = (1, 1) — implicit end
newtype CubicBezierEasing = CubicBezierEasing
  { x1 :: CubicX1
  , y1 :: CubicY1
  , x2 :: CubicX2
  , y2 :: CubicY2
  }

derive instance eqCubicBezierEasing :: Eq CubicBezierEasing
derive instance ordCubicBezierEasing :: Ord CubicBezierEasing

instance showCubicBezierEasing :: Show CubicBezierEasing where
  show (CubicBezierEasing c) = 
    "(CubicBezier " 
    <> show (unwrapCubicX1 c.x1) <> " "
    <> show (unwrapCubicY1 c.y1) <> " "
    <> show (unwrapCubicX2 c.x2) <> " "
    <> show (unwrapCubicY2 c.y2) <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create CubicBezierEasing from typed control points
cubicBezier :: CubicX1 -> CubicY1 -> CubicX2 -> CubicY2 -> CubicBezierEasing
cubicBezier x1' y1' x2' y2' = CubicBezierEasing
  { x1: x1'
  , y1: y1'
  , x2: x2'
  , y2: y2'
  }

-- | Create CubicBezierEasing from raw numbers (clamped)
-- |
-- | ```purescript
-- | cubicBezierFromNumbers 0.25 0.1 0.25 1.0  -- ease preset
-- | ```
cubicBezierFromNumbers :: Number -> Number -> Number -> Number -> CubicBezierEasing
cubicBezierFromNumbers x1' y1' x2' y2' = CubicBezierEasing
  { x1: cubicX1 x1'
  , y1: cubicY1 y1'
  , x2: cubicX2 x2'
  , y2: cubicY2 y2'
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get x1 coordinate
getX1 :: CubicBezierEasing -> Number
getX1 (CubicBezierEasing c) = unwrapCubicX1 c.x1

-- | Get y1 coordinate
getY1 :: CubicBezierEasing -> Number
getY1 (CubicBezierEasing c) = unwrapCubicY1 c.y1

-- | Get x2 coordinate
getX2 :: CubicBezierEasing -> Number
getX2 (CubicBezierEasing c) = unwrapCubicX2 c.x2

-- | Get y2 coordinate
getY2 :: CubicBezierEasing -> Number
getY2 (CubicBezierEasing c) = unwrapCubicY2 c.y2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css export
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format for CSS for legacy system interop.
-- |
-- | **NOTE:** Hydrogen renders via WebGPU, NOT CSS. This function exists only
-- | for exporting to legacy systems that require CSS format.
-- |
-- | Returns: "cubic-bezier(0.25, 0.1, 0.25, 1)"
toLegacyCss :: CubicBezierEasing -> String
toLegacyCss (CubicBezierEasing c) =
  "cubic-bezier(" 
  <> show (unwrapCubicX1 c.x1) <> ", "
  <> show (unwrapCubicY1 c.y1) <> ", "
  <> show (unwrapCubicX2 c.x2) <> ", "
  <> show (unwrapCubicY2 c.y2) <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // standard presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear: no acceleration (constant speed)
linear :: CubicBezierEasing
linear = cubicBezierFromNumbers 0.0 0.0 1.0 1.0

-- | Ease: gentle acceleration and deceleration (CSS default)
ease :: CubicBezierEasing
ease = cubicBezierFromNumbers 0.25 0.1 0.25 1.0

-- | Ease-in: slow start, fast end
easeIn :: CubicBezierEasing
easeIn = cubicBezierFromNumbers 0.42 0.0 1.0 1.0

-- | Ease-out: fast start, slow end
easeOut :: CubicBezierEasing
easeOut = cubicBezierFromNumbers 0.0 0.0 0.58 1.0

-- | Ease-in-out: slow start and end
easeInOut :: CubicBezierEasing
easeInOut = cubicBezierFromNumbers 0.42 0.0 0.58 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // extended presets
-- ═════════════════════════════════════════════════════════════════════════════

-- Quadratic (power of 2)

-- | Quadratic ease-in
easeInQuad :: CubicBezierEasing
easeInQuad = cubicBezierFromNumbers 0.55 0.085 0.68 0.53

-- | Quadratic ease-out
easeOutQuad :: CubicBezierEasing
easeOutQuad = cubicBezierFromNumbers 0.25 0.46 0.45 0.94

-- | Quadratic ease-in-out
easeInOutQuad :: CubicBezierEasing
easeInOutQuad = cubicBezierFromNumbers 0.455 0.03 0.515 0.955

-- Cubic (power of 3)

-- | Cubic ease-in
easeInCubic :: CubicBezierEasing
easeInCubic = cubicBezierFromNumbers 0.55 0.055 0.675 0.19

-- | Cubic ease-out
easeOutCubic :: CubicBezierEasing
easeOutCubic = cubicBezierFromNumbers 0.215 0.61 0.355 1.0

-- | Cubic ease-in-out
easeInOutCubic :: CubicBezierEasing
easeInOutCubic = cubicBezierFromNumbers 0.645 0.045 0.355 1.0

-- Quartic (power of 4)

-- | Quartic ease-in
easeInQuart :: CubicBezierEasing
easeInQuart = cubicBezierFromNumbers 0.895 0.03 0.685 0.22

-- | Quartic ease-out
easeOutQuart :: CubicBezierEasing
easeOutQuart = cubicBezierFromNumbers 0.165 0.84 0.44 1.0

-- | Quartic ease-in-out
easeInOutQuart :: CubicBezierEasing
easeInOutQuart = cubicBezierFromNumbers 0.77 0.0 0.175 1.0

-- Quintic (power of 5)

-- | Quintic ease-in
easeInQuint :: CubicBezierEasing
easeInQuint = cubicBezierFromNumbers 0.755 0.05 0.855 0.06

-- | Quintic ease-out
easeOutQuint :: CubicBezierEasing
easeOutQuint = cubicBezierFromNumbers 0.23 1.0 0.32 1.0

-- | Quintic ease-in-out
easeInOutQuint :: CubicBezierEasing
easeInOutQuint = cubicBezierFromNumbers 0.86 0.0 0.07 1.0

-- Exponential

-- | Exponential ease-in
easeInExpo :: CubicBezierEasing
easeInExpo = cubicBezierFromNumbers 0.95 0.05 0.795 0.035

-- | Exponential ease-out
easeOutExpo :: CubicBezierEasing
easeOutExpo = cubicBezierFromNumbers 0.19 1.0 0.22 1.0

-- | Exponential ease-in-out
easeInOutExpo :: CubicBezierEasing
easeInOutExpo = cubicBezierFromNumbers 1.0 0.0 0.0 1.0

-- Circular

-- | Circular ease-in
easeInCirc :: CubicBezierEasing
easeInCirc = cubicBezierFromNumbers 0.6 0.04 0.98 0.335

-- | Circular ease-out
easeOutCirc :: CubicBezierEasing
easeOutCirc = cubicBezierFromNumbers 0.075 0.82 0.165 1.0

-- | Circular ease-in-out
easeInOutCirc :: CubicBezierEasing
easeInOutCirc = cubicBezierFromNumbers 0.785 0.135 0.15 0.86

-- Back (overshoot)

-- | Back ease-in (anticipation)
easeInBack :: CubicBezierEasing
easeInBack = cubicBezierFromNumbers 0.6 (-0.28) 0.735 0.045

-- | Back ease-out (overshoot)
easeOutBack :: CubicBezierEasing
easeOutBack = cubicBezierFromNumbers 0.175 0.885 0.32 1.275

-- | Back ease-in-out (anticipation + overshoot)
easeInOutBack :: CubicBezierEasing
easeInOutBack = cubicBezierFromNumbers 0.68 (-0.55) 0.265 1.55

-- Sinusoidal

-- | Sinusoidal ease-in (gentle start based on sine wave)
easeInSine :: CubicBezierEasing
easeInSine = cubicBezierFromNumbers 0.12 0.0 0.39 0.0

-- | Sinusoidal ease-out (gentle end based on sine wave)
easeOutSine :: CubicBezierEasing
easeOutSine = cubicBezierFromNumbers 0.61 1.0 0.88 1.0

-- | Sinusoidal ease-in-out (smooth sine wave transition)
easeInOutSine :: CubicBezierEasing
easeInOutSine = cubicBezierFromNumbers 0.37 0.0 0.63 1.0
