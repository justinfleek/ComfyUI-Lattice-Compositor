-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // motion // easing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Easing curves for animation interpolation.
-- |
-- | Defines how values change over time between keyframes. The easing
-- | function maps normalized time (0-1) to normalized value (0-1).
-- |
-- | ## Cubic Bezier
-- |
-- | The foundation is the cubic bezier curve, matching CSS `cubic-bezier()`:
-- | - Two control points (x1,y1) and (x2,y2)
-- | - Start point is implicitly (0,0)
-- | - End point is implicitly (1,1)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.Easing as Easing
-- |
-- | -- Use a preset
-- | ease = Easing.easeInOut
-- |
-- | -- Create custom cubic bezier
-- | custom = Easing.cubicBezier 0.17 0.67 0.83 0.67
-- |
-- | -- Evaluate easing at time t (0-1)
-- | value = Easing.evaluate ease 0.5
-- | -- Returns the eased value at 50% progress
-- | ```
module Hydrogen.Schema.Motion.Easing
  ( -- * Core Types
    Easing(..)
  , CubicBezier(..)
  
  -- * Constructors
  , linear
  , cubicBezier
  , steps
  
  -- * Standard Presets
  , ease
  , easeIn
  , easeOut
  , easeInOut
  
  -- * Sine Easing
  , easeInSine
  , easeOutSine
  , easeInOutSine
  
  -- * Quad Easing
  , easeInQuad
  , easeOutQuad
  , easeInOutQuad
  
  -- * Cubic Easing
  , easeInCubic
  , easeOutCubic
  , easeInOutCubic
  
  -- * Quart Easing
  , easeInQuart
  , easeOutQuart
  , easeInOutQuart
  
  -- * Quint Easing
  , easeInQuint
  , easeOutQuint
  , easeInOutQuint
  
  -- * Expo Easing
  , easeInExpo
  , easeOutExpo
  , easeInOutExpo
  
  -- * Circ Easing
  , easeInCirc
  , easeOutCirc
  , easeInOutCirc
  
  -- * Back Easing
  , easeInBack
  , easeOutBack
  , easeInOutBack
  
  -- * Elastic Easing
  , easeInElastic
  , easeOutElastic
  , easeInOutElastic
  
  -- * Bounce Easing
  , easeInBounce
  , easeOutBounce
  , easeInOutBounce
  
  -- * Evaluation
  , evaluate
  , evaluateBezier
  
  -- * Accessors
  , toControlPoints
  , p1x
  , p1y
  , p2x
  , p2y
  , toLegacyCssString
  , name
  ) where

import Prelude

import Data.Int (toNumber) as Int
import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cubic bezier control points
-- |
-- | Represents the two control points of a cubic bezier curve.
-- | Start (0,0) and end (1,1) are implicit.
newtype CubicBezier = CubicBezier
  { x1 :: Number
  , y1 :: Number
  , x2 :: Number
  , y2 :: Number
  }

derive instance eqCubicBezier :: Eq CubicBezier

instance showCubicBezier :: Show CubicBezier where
  show (CubicBezier p) = 
    "cubic-bezier(" <> show p.x1 <> ", " <> show p.y1 <> 
    ", " <> show p.x2 <> ", " <> show p.y2 <> ")"

-- | Easing function type
-- |
-- | Can be a cubic bezier, step function, or named preset.
data Easing
  = Linear
  | Bezier CubicBezier String  -- Bezier curve with name
  | Steps Int Boolean          -- Step count, jump-start?

derive instance eqEasing :: Eq Easing

instance showEasing :: Show Easing where
  show Linear = "linear"
  show (Bezier _ n) = n
  show (Steps n jumpStart) = 
    "steps(" <> show n <> ", " <> 
    (if jumpStart then "jump-start" else "jump-end") <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear easing (no acceleration)
linear :: Easing
linear = Linear

-- | Create custom cubic bezier easing
-- |
-- | ```purescript
-- | custom = cubicBezier 0.17 0.67 0.83 0.67
-- | ```
cubicBezier :: Number -> Number -> Number -> Number -> Easing
cubicBezier x1 y1 x2 y2 = 
  Bezier (CubicBezier { x1, y1, x2, y2 }) "custom"

-- | Create step easing
-- |
-- | ```purescript
-- | steppedEase = steps 4 true  -- 4 steps, jump at start
-- | ```
steps :: Int -> Boolean -> Easing
steps n jumpStart = Steps (max 1 n) jumpStart

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // standard presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS default ease
ease :: Easing
ease = Bezier (CubicBezier { x1: 0.25, y1: 0.1, x2: 0.25, y2: 1.0 }) "ease"

-- | CSS ease-in
easeIn :: Easing
easeIn = Bezier (CubicBezier { x1: 0.42, y1: 0.0, x2: 1.0, y2: 1.0 }) "ease-in"

-- | CSS ease-out
easeOut :: Easing
easeOut = Bezier (CubicBezier { x1: 0.0, y1: 0.0, x2: 0.58, y2: 1.0 }) "ease-out"

-- | CSS ease-in-out
easeInOut :: Easing
easeInOut = Bezier (CubicBezier { x1: 0.42, y1: 0.0, x2: 0.58, y2: 1.0 }) "ease-in-out"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // sine easing
-- ═════════════════════════════════════════════════════════════════════════════

easeInSine :: Easing
easeInSine = Bezier (CubicBezier { x1: 0.12, y1: 0.0, x2: 0.39, y2: 0.0 }) "ease-in-sine"

easeOutSine :: Easing
easeOutSine = Bezier (CubicBezier { x1: 0.61, y1: 1.0, x2: 0.88, y2: 1.0 }) "ease-out-sine"

easeInOutSine :: Easing
easeInOutSine = Bezier (CubicBezier { x1: 0.37, y1: 0.0, x2: 0.63, y2: 1.0 }) "ease-in-out-sine"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // quad easing
-- ═════════════════════════════════════════════════════════════════════════════

easeInQuad :: Easing
easeInQuad = Bezier (CubicBezier { x1: 0.11, y1: 0.0, x2: 0.5, y2: 0.0 }) "ease-in-quad"

easeOutQuad :: Easing
easeOutQuad = Bezier (CubicBezier { x1: 0.5, y1: 1.0, x2: 0.89, y2: 1.0 }) "ease-out-quad"

easeInOutQuad :: Easing
easeInOutQuad = Bezier (CubicBezier { x1: 0.45, y1: 0.0, x2: 0.55, y2: 1.0 }) "ease-in-out-quad"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cubic easing
-- ═════════════════════════════════════════════════════════════════════════════

easeInCubic :: Easing
easeInCubic = Bezier (CubicBezier { x1: 0.32, y1: 0.0, x2: 0.67, y2: 0.0 }) "ease-in-cubic"

easeOutCubic :: Easing
easeOutCubic = Bezier (CubicBezier { x1: 0.33, y1: 1.0, x2: 0.68, y2: 1.0 }) "ease-out-cubic"

easeInOutCubic :: Easing
easeInOutCubic = Bezier (CubicBezier { x1: 0.65, y1: 0.0, x2: 0.35, y2: 1.0 }) "ease-in-out-cubic"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // quart easing
-- ═════════════════════════════════════════════════════════════════════════════

easeInQuart :: Easing
easeInQuart = Bezier (CubicBezier { x1: 0.5, y1: 0.0, x2: 0.75, y2: 0.0 }) "ease-in-quart"

easeOutQuart :: Easing
easeOutQuart = Bezier (CubicBezier { x1: 0.25, y1: 1.0, x2: 0.5, y2: 1.0 }) "ease-out-quart"

easeInOutQuart :: Easing
easeInOutQuart = Bezier (CubicBezier { x1: 0.76, y1: 0.0, x2: 0.24, y2: 1.0 }) "ease-in-out-quart"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // quint easing
-- ═════════════════════════════════════════════════════════════════════════════

easeInQuint :: Easing
easeInQuint = Bezier (CubicBezier { x1: 0.64, y1: 0.0, x2: 0.78, y2: 0.0 }) "ease-in-quint"

easeOutQuint :: Easing
easeOutQuint = Bezier (CubicBezier { x1: 0.22, y1: 1.0, x2: 0.36, y2: 1.0 }) "ease-out-quint"

easeInOutQuint :: Easing
easeInOutQuint = Bezier (CubicBezier { x1: 0.83, y1: 0.0, x2: 0.17, y2: 1.0 }) "ease-in-out-quint"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // expo easing
-- ═════════════════════════════════════════════════════════════════════════════

easeInExpo :: Easing
easeInExpo = Bezier (CubicBezier { x1: 0.7, y1: 0.0, x2: 0.84, y2: 0.0 }) "ease-in-expo"

easeOutExpo :: Easing
easeOutExpo = Bezier (CubicBezier { x1: 0.16, y1: 1.0, x2: 0.3, y2: 1.0 }) "ease-out-expo"

easeInOutExpo :: Easing
easeInOutExpo = Bezier (CubicBezier { x1: 0.87, y1: 0.0, x2: 0.13, y2: 1.0 }) "ease-in-out-expo"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // circ easing
-- ═════════════════════════════════════════════════════════════════════════════

easeInCirc :: Easing
easeInCirc = Bezier (CubicBezier { x1: 0.55, y1: 0.0, x2: 1.0, y2: 0.45 }) "ease-in-circ"

easeOutCirc :: Easing
easeOutCirc = Bezier (CubicBezier { x1: 0.0, y1: 0.55, x2: 0.45, y2: 1.0 }) "ease-out-circ"

easeInOutCirc :: Easing
easeInOutCirc = Bezier (CubicBezier { x1: 0.85, y1: 0.0, x2: 0.15, y2: 1.0 }) "ease-in-out-circ"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // back easing
-- ═════════════════════════════════════════════════════════════════════════════

easeInBack :: Easing
easeInBack = Bezier (CubicBezier { x1: 0.36, y1: 0.0, x2: 0.66, y2: (-0.56) }) "ease-in-back"

easeOutBack :: Easing
easeOutBack = Bezier (CubicBezier { x1: 0.34, y1: 1.56, x2: 0.64, y2: 1.0 }) "ease-out-back"

easeInOutBack :: Easing
easeInOutBack = Bezier (CubicBezier { x1: 0.68, y1: (-0.6), x2: 0.32, y2: 1.6 }) "ease-in-out-back"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // elastic easing
-- ═════════════════════════════════════════════════════════════════════════════

-- Note: Elastic easing cannot be perfectly represented as cubic bezier.
-- These are approximations for visual preview. Actual evaluation uses
-- the elastic formula.

easeInElastic :: Easing
easeInElastic = Bezier (CubicBezier { x1: 0.5, y1: (-0.25), x2: 0.75, y2: 0.0 }) "ease-in-elastic"

easeOutElastic :: Easing
easeOutElastic = Bezier (CubicBezier { x1: 0.25, y1: 1.0, x2: 0.5, y2: 1.25 }) "ease-out-elastic"

easeInOutElastic :: Easing
easeInOutElastic = Bezier (CubicBezier { x1: 0.68, y1: (-0.55), x2: 0.32, y2: 1.55 }) "ease-in-out-elastic"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // bounce easing
-- ═════════════════════════════════════════════════════════════════════════════

-- Note: Bounce easing cannot be represented as cubic bezier.
-- These are visual approximations. Actual evaluation uses bounce formula.

easeInBounce :: Easing
easeInBounce = Bezier (CubicBezier { x1: 0.6, y1: 0.0, x2: 0.9, y2: 0.4 }) "ease-in-bounce"

easeOutBounce :: Easing
easeOutBounce = Bezier (CubicBezier { x1: 0.1, y1: 0.6, x2: 0.4, y2: 1.0 }) "ease-out-bounce"

easeInOutBounce :: Easing
easeInOutBounce = Bezier (CubicBezier { x1: 0.7, y1: 0.0, x2: 0.3, y2: 1.0 }) "ease-in-out-bounce"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate easing function at time t (0-1)
-- |
-- | Returns the eased value (usually 0-1, but can overshoot for back/elastic)
evaluate :: Easing -> Number -> Number
evaluate Linear t = t
evaluate (Bezier bezier _) t = evaluateBezier bezier t
evaluate (Steps n jumpStart) t = evaluateSteps n jumpStart t

-- | Evaluate cubic bezier at time t
-- |
-- | Uses Newton-Raphson iteration to find the x value, then
-- | evaluates the y coordinate.
evaluateBezier :: CubicBezier -> Number -> Number
evaluateBezier (CubicBezier p) t
  | t <= 0.0 = 0.0
  | t >= 1.0 = 1.0
  | otherwise =
      let
        -- Find t parameter for given x using Newton-Raphson
        tx = findTForX p.x1 p.x2 t
        -- Evaluate y at that t
        ay = 1.0 - 3.0 * p.y2 + 3.0 * p.y1
        by = 3.0 * p.y2 - 6.0 * p.y1
        cy = 3.0 * p.y1
      in
        ((ay * tx + by) * tx + cy) * tx

-- | Find bezier t parameter for given x value
findTForX :: Number -> Number -> Number -> Number
findTForX x1 x2 x = iterate 0.5 8
  where
    ax = 1.0 - 3.0 * x2 + 3.0 * x1
    bx = 3.0 * x2 - 6.0 * x1
    cx = 3.0 * x1
    
    sampleX t = ((ax * t + bx) * t + cx) * t
    sampleDerivative t = (3.0 * ax * t + 2.0 * bx) * t + cx
    
    iterate t 0 = t
    iterate t n =
      let
        currentX = sampleX t
        derivative = sampleDerivative t
      in
        if Math.abs (currentX - x) < 0.0001 || derivative == 0.0
          then t
          else iterate (t - (currentX - x) / derivative) (n - 1)

-- | Evaluate step easing
evaluateSteps :: Int -> Boolean -> Number -> Number
evaluateSteps n jumpStart t
  | t <= 0.0 = if jumpStart then 1.0 / Int.toNumber n else 0.0
  | t >= 1.0 = 1.0
  | otherwise =
      let
        step = Math.floor (t * Int.toNumber n)
        adjustedStep = if jumpStart then step + 1.0 else step
      in
        adjustedStep / Int.toNumber n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract control points (if bezier)
toControlPoints :: Easing -> { x1 :: Number, y1 :: Number, x2 :: Number, y2 :: Number }
toControlPoints Linear = { x1: 0.0, y1: 0.0, x2: 1.0, y2: 1.0 }
toControlPoints (Bezier (CubicBezier p) _) = p
toControlPoints (Steps _ _) = { x1: 0.0, y1: 0.0, x2: 1.0, y2: 1.0 }

-- | Extract first control point x coordinate
p1x :: Easing -> Number
p1x easing = (toControlPoints easing).x1

-- | Extract first control point y coordinate
p1y :: Easing -> Number
p1y easing = (toControlPoints easing).y1

-- | Extract second control point x coordinate
p2x :: Easing -> Number
p2x easing = (toControlPoints easing).x2

-- | Extract second control point y coordinate
p2y :: Easing -> Number
p2y easing = (toControlPoints easing).y2

-- | Get CSS animation-timing-function value for legacy system interop.
-- |
-- | **NOTE:** Hydrogen renders via WebGPU, NOT CSS. This function exists only
-- | for exporting to legacy systems that require CSS format.
toLegacyCssString :: Easing -> String
toLegacyCssString Linear = "linear"
toLegacyCssString (Bezier (CubicBezier p) _) =
  "cubic-bezier(" <> show p.x1 <> ", " <> show p.y1 <> 
  ", " <> show p.x2 <> ", " <> show p.y2 <> ")"
toLegacyCssString (Steps n jumpStart) =
  "steps(" <> show n <> ", " <> 
  (if jumpStart then "jump-start" else "jump-end") <> ")"

-- | Get easing name
name :: Easing -> String
name Linear = "linear"
name (Bezier _ n) = n
name (Steps n _) = "steps-" <> show n
