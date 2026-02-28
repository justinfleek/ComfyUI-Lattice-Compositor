-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // geometry // squircle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Squircle — Superellipse corner smoothing.
-- |
-- | ## Purpose
-- |
-- | A squircle (portmanteau of square + circle) is a superellipse that 
-- | provides smoother, more natural-looking rounded corners than standard
-- | circular arcs. Apple uses this extensively in iOS for app icons.
-- |
-- | ## Mathematics
-- |
-- | The superellipse is defined by: |x/a|^n + |y/b|^n = 1
-- |
-- | Where n is the "squareness" exponent:
-- | - n = 2: Perfect circle/ellipse (standard CSS border-radius)
-- | - n = 4: Apple's iOS icon squircle
-- | - n → ∞: Perfect rectangle
-- |
-- | ## Visual Difference
-- |
-- | Standard circular corners have an abrupt transition where the curve
-- | meets the straight edge. Squircle corners have a continuous curvature
-- | that gradually transitions, giving a more organic feel.
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.CornerRadii (base radius)

module Hydrogen.Schema.Geometry.Squircle
  ( -- * Squircle Type
    Squircle(Squircle)
  , squircle
  , squircleUniform
  
  -- * Accessors
  , cornerRadius
  , smoothness
  , exponent
  
  -- * Transformations
  , withRadius
  , withSmoothness
  , scaleSquircle
  
  -- * Presets
  , iosIcon
  , materialYou
  , subtle
  , standard
  , sharp
  
  -- * Queries
  , isCircular
  , isRectangular
  , effectiveExponent
  
  -- * Path Generation
  , cornerControlPoints
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (<)
  , (*)
  , (+)
  , (-)
  , max
  , min
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // squircle type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Squircle — superellipse-based corner smoothing.
-- |
-- | Combines a corner radius with a smoothness factor that controls
-- | how "squircle-like" the corner is.
-- |
-- | - **radius**: The corner radius in pixels
-- | - **smoothness**: 0.0 = circular, 1.0 = full squircle (n≈4)
newtype Squircle = Squircle
  { radius :: Number      -- ^ Corner radius in pixels (>= 0)
  , smoothness :: Number  -- ^ Squircle smoothness (0.0-1.0)
  }

derive instance eqSquircle :: Eq Squircle
derive instance ordSquircle :: Ord Squircle

instance showSquircle :: Show Squircle where
  show (Squircle s) = 
    "(Squircle r=" <> show s.radius <> " smooth=" <> show s.smoothness <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a value to [0, 1]
clampUnit :: Number -> Number
clampUnit n = max 0.0 (min 1.0 n)

-- | Clamp a value to non-negative
clampNonNegative :: Number -> Number
clampNonNegative n = max 0.0 n

-- | Create a squircle with specific radius and smoothness
squircle :: Number -> Number -> Squircle
squircle radius smoothness' = Squircle
  { radius: clampNonNegative radius
  , smoothness: clampUnit smoothness'
  }

-- | Create a uniform squircle (same smoothness for all corners)
-- |
-- | Convenience for the common case of uniform corners.
squircleUniform :: Number -> Number -> Squircle
squircleUniform = squircle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the corner radius
cornerRadius :: Squircle -> Number
cornerRadius (Squircle s) = s.radius

-- | Get the smoothness factor (0.0-1.0)
smoothness :: Squircle -> Number
smoothness (Squircle s) = s.smoothness

-- | Get the superellipse exponent
-- |
-- | Maps smoothness 0.0-1.0 to exponent 2.0-4.0
-- | - smoothness 0.0 → n = 2 (circular)
-- | - smoothness 1.0 → n = 4 (iOS squircle)
exponent :: Squircle -> Number
exponent (Squircle s) = 2.0 + s.smoothness * 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the corner radius
withRadius :: Number -> Squircle -> Squircle
withRadius r (Squircle s) = Squircle (s { radius = clampNonNegative r })

-- | Set the smoothness factor
withSmoothness :: Number -> Squircle -> Squircle
withSmoothness sm (Squircle s) = Squircle (s { smoothness = clampUnit sm })

-- | Scale the radius by a factor
scaleSquircle :: Number -> Squircle -> Squircle
scaleSquircle factor (Squircle s) = Squircle 
  (s { radius = clampNonNegative (s.radius * factor) })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | iOS app icon squircle
-- |
-- | 20% radius relative to size, full squircle smoothness
iosIcon :: Squircle
iosIcon = Squircle
  { radius: 0.2  -- 20% of width (interpret as ratio)
  , smoothness: 1.0
  }

-- | Material You squircle (Android 12+)
-- |
-- | Slightly less pronounced than iOS
materialYou :: Squircle
materialYou = Squircle
  { radius: 24.0
  , smoothness: 0.7
  }

-- | Subtle squircle effect
-- |
-- | Small radius, moderate smoothness
subtle :: Squircle
subtle = Squircle
  { radius: 8.0
  , smoothness: 0.4
  }

-- | Standard squircle
-- |
-- | Medium radius, full smoothness
standard :: Squircle
standard = Squircle
  { radius: 16.0
  , smoothness: 1.0
  }

-- | Sharp corners with slight squircle
-- |
-- | Small radius, minimal smoothness
sharp :: Squircle
sharp = Squircle
  { radius: 4.0
  , smoothness: 0.2
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if the squircle is effectively circular (smoothness near 0)
isCircular :: Squircle -> Boolean
isCircular (Squircle s) = s.smoothness < 0.1

-- | Check if the squircle is effectively rectangular (no radius)
isRectangular :: Squircle -> Boolean
isRectangular (Squircle s) = s.radius < 0.5

-- | Get the effective exponent for curve calculation
-- |
-- | Same as `exponent` but for clarity in curve algorithms.
effectiveExponent :: Squircle -> Number
effectiveExponent = exponent

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // path generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Corner control point record for bezier curve generation
-- |
-- | The runtime uses these to generate smooth squircle corners.
type CornerControlPoints =
  { startOffset :: Number    -- ^ How far from corner the curve starts
  , controlOffset :: Number  -- ^ Bezier control point offset
  , handleLength :: Number   -- ^ Length of bezier handles
  }

-- | Calculate control points for a squircle corner
-- |
-- | These values are used by the runtime to generate bezier curves
-- | that approximate the superellipse shape.
cornerControlPoints :: Squircle -> CornerControlPoints
cornerControlPoints (Squircle s) =
  let
    -- Higher smoothness = curve starts further from corner
    startRatio = 0.55 + s.smoothness * 0.35
    -- Control point moves closer to corner with higher smoothness
    controlRatio = 0.45 - s.smoothness * 0.2
    -- Handle length increases with smoothness
    handleRatio = 0.55 + s.smoothness * 0.15
  in
    { startOffset: s.radius * startRatio
    , controlOffset: s.radius * controlRatio
    , handleLength: s.radius * handleRatio
    }
