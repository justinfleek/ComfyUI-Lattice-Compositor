-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // tour // motion // spotlight
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spotlight Morphing — Shape interpolation between tour targets.
-- |
-- | ## Overview
-- |
-- | When transitioning between tour steps, the spotlight doesn't just
-- | appear/disappear — it MORPHS from one shape/position to another.
-- | This creates spatial continuity and helps users track where they are.
-- |
-- | ## Design Philosophy
-- |
-- | Morphing uses spring physics for organic movement, with optional:
-- | - Scale pop at midpoint (draws attention)
-- | - Rotation at midpoint (adds life)
-- | - Curved paths for distant targets (avoids diagonal motion)
-- |
-- | The result feels like a living entity guiding the user.

module Hydrogen.Element.Compound.Tour.Motion.Spotlight
  ( -- * Configuration
    MorphConfig
  , defaultMorphConfig
  , snappyMorphConfig
  , elasticMorphConfig
  
    -- * Interpolation Types
  , MorphInterpolation(..)
  , MorphPath(..)
  , ShapeInterpolation
  
    -- * Interpolation Functions
  , interpolateRect
  , interpolateCircle
  , interpolatePill
  , computeMorphPath
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , min
  , show
  , (*)
  , (+)
  , (-)
  , (/)
  , (<>)
  , (>)
  , (||)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Element.Compound.Tour.Motion.Spring
  ( SpringParams
  , snappySpring
  , bouncySpring
  , smoothSpring
  , evaluateSpring
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for spotlight morph transitions between targets.
-- |
-- | When transitioning from step N to step N+1, the highlight morphs
-- | from one shape/position to another with configurable physics.
type MorphConfig =
  { duration :: Number
    -- ^ Morph duration in milliseconds (default: 400ms)
  , spring :: SpringParams
    -- ^ Spring physics for organic movement
  , interpolation :: MorphInterpolation
    -- ^ How shapes blend during transition
  , pathCurve :: Number
    -- ^ Bezier control point offset (0.0 = direct, 1.0 = extreme arc)
  , scaleAtMidpoint :: Number
    -- ^ Scale multiplier at transition midpoint (1.05 = subtle pop)
  , rotateAtMidpoint :: Number
    -- ^ Rotation at midpoint in degrees (subtle tilt adds life)
  , opacityDip :: Number
    -- ^ Opacity dip at midpoint (0.0 = none, 0.2 = subtle fade)
  }

-- | How shapes interpolate during morphing.
data MorphInterpolation
  = InterpolateDirect      -- ^ Linear interpolation of bounds
  | InterpolateSmooth      -- ^ Smooth bezier-curved bounds interpolation
  | InterpolateSuperellipse -- ^ Superellipse blend for organic shapes
  | InterpolateCorners     -- ^ Interpolate each corner independently

derive instance eqMorphInterpolation :: Eq MorphInterpolation
derive instance ordMorphInterpolation :: Ord MorphInterpolation

instance showMorphInterpolation :: Show MorphInterpolation where
  show InterpolateDirect = "direct"
  show InterpolateSmooth = "smooth"
  show InterpolateSuperellipse = "superellipse"
  show InterpolateCorners = "corners"

-- | Path animation strategy for non-adjacent elements.
data MorphPath
  = PathDirect
    -- ^ Straight line between targets (default)
  | PathArc Number
    -- ^ Curved arc path (parameter = curvature, 0.0-1.0)
  | PathBezier
      { cx1 :: Number, cy1 :: Number }
      { cx2 :: Number, cy2 :: Number }
    -- ^ Custom bezier control points (normalized 0-1)
  | PathAvoid (Array { x :: Number, y :: Number, radius :: Number })
    -- ^ Path that avoids obstacles
  | PathFollow String
    -- ^ Follow a named SVG path

derive instance eqMorphPath :: Eq MorphPath

instance showMorphPath :: Show MorphPath where
  show PathDirect = "direct"
  show (PathArc c) = "arc(" <> show c <> ")"
  show (PathBezier _ _) = "bezier(...)"
  show (PathAvoid _) = "avoid(...)"
  show (PathFollow pathId) = "follow(" <> pathId <> ")"

-- | Shape interpolation result at time t.
type ShapeInterpolation =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  , borderRadius :: Number
  , scale :: Number
  , rotation :: Number
  , opacity :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default morph configuration — balanced and professional.
defaultMorphConfig :: MorphConfig
defaultMorphConfig =
  { duration: 400.0
  , spring: smoothSpring
  , interpolation: InterpolateSmooth
  , pathCurve: 0.15
  , scaleAtMidpoint: 1.02
  , rotateAtMidpoint: 0.0
  , opacityDip: 0.0
  }

-- | Snappy morph — quick and precise for power users.
snappyMorphConfig :: MorphConfig
snappyMorphConfig =
  { duration: 250.0
  , spring: snappySpring
  , interpolation: InterpolateDirect
  , pathCurve: 0.0
  , scaleAtMidpoint: 1.0
  , rotateAtMidpoint: 0.0
  , opacityDip: 0.0
  }

-- | Elastic morph — playful with overshoot.
elasticMorphConfig :: MorphConfig
elasticMorphConfig =
  { duration: 500.0
  , spring: bouncySpring
  , interpolation: InterpolateSmooth
  , pathCurve: 0.25
  , scaleAtMidpoint: 1.08
  , rotateAtMidpoint: 2.0
  , opacityDip: 0.05
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interpolate between two rectangles at time t (0-1).
interpolateRect 
  :: { x :: Number, y :: Number, width :: Number, height :: Number, borderRadius :: Number }
  -> { x :: Number, y :: Number, width :: Number, height :: Number, borderRadius :: Number }
  -> MorphConfig
  -> Number
  -> ShapeInterpolation
interpolateRect from to config t =
  let
    -- Apply easing to time
    easedT = evaluateSpring config.spring t
    
    -- Interpolate position with optional arc path
    pathOffset = computePathOffset config.pathCurve t
    
    -- Midpoint scale/rotation effects
    midpointEffect = computeMidpointEffect t
    scaleMult = 1.0 + (config.scaleAtMidpoint - 1.0) * midpointEffect
    rotationAdd = config.rotateAtMidpoint * midpointEffect
    opacityMult = 1.0 - config.opacityDip * midpointEffect
  in
    { x: lerp from.x to.x easedT + pathOffset.x
    , y: lerp from.y to.y easedT + pathOffset.y
    , width: lerp from.width to.width easedT
    , height: lerp from.height to.height easedT
    , borderRadius: lerp from.borderRadius to.borderRadius easedT
    , scale: scaleMult
    , rotation: rotationAdd
    , opacity: opacityMult
    }

-- | Interpolate circles (uses max dimension as diameter).
interpolateCircle
  :: { cx :: Number, cy :: Number, r :: Number }
  -> { cx :: Number, cy :: Number, r :: Number }
  -> MorphConfig
  -> Number
  -> ShapeInterpolation
interpolateCircle from to config t =
  let
    easedT = evaluateSpring config.spring t
    midpointEffect = computeMidpointEffect t
    scaleMult = 1.0 + (config.scaleAtMidpoint - 1.0) * midpointEffect
    r = lerp from.r to.r easedT
  in
    { x: lerp from.cx to.cx easedT - r
    , y: lerp from.cy to.cy easedT - r
    , width: r * 2.0
    , height: r * 2.0
    , borderRadius: r
    , scale: scaleMult
    , rotation: config.rotateAtMidpoint * midpointEffect
    , opacity: 1.0 - config.opacityDip * midpointEffect
    }

-- | Interpolate pill shapes.
-- |
-- | Pills have fully rounded ends, so borderRadius = min(width, height) / 2.
interpolatePill
  :: { x :: Number, y :: Number, width :: Number, height :: Number }
  -> { x :: Number, y :: Number, width :: Number, height :: Number }
  -> MorphConfig
  -> Number
  -> ShapeInterpolation
interpolatePill from to config t =
  let
    -- Convert pill bounds to rect with appropriate radius
    fromWithRadius = 
      { x: from.x
      , y: from.y
      , width: from.width
      , height: from.height
      , borderRadius: min from.width from.height / 2.0
      }
    toWithRadius = 
      { x: to.x
      , y: to.y
      , width: to.width
      , height: to.height
      , borderRadius: min to.width to.height / 2.0
      }
    result = interpolateRect fromWithRadius toWithRadius config t
    -- Pill always has fully rounded ends based on interpolated dimensions
    finalRadius = min result.width result.height / 2.0
  in
    result { borderRadius = finalRadius }

-- | Compute optimal path between two targets.
-- |
-- | Returns `PathDirect` for short distances, `PathArc` for longer ones.
-- | The arc direction is chosen based on the predominant movement direction.
computeMorphPath
  :: { x :: Number, y :: Number }
  -> { x :: Number, y :: Number }
  -> Number                          -- ^ Distance threshold for arcing
  -> MorphPath
computeMorphPath from to threshold =
  let
    dx = to.x - from.x
    dy = to.y - from.y
    distance = Math.sqrt (dx * dx + dy * dy)
    
    -- Bias factors determine arc direction
    verticalBias = Math.abs dy / (Math.abs dx + 0.001)
    horizontalBias = Math.abs dx / (Math.abs dy + 0.001)
    
    -- Base curvature on distance
    baseCurvature = if distance > threshold
      then min 0.3 (distance / (threshold * 3.0))
      else 0.0
    
    -- Adjust curvature based on movement bias
    biasMultiplier = if verticalBias > 2.0 || horizontalBias > 2.0
      then 1.2
      else 1.0
    
    curvature = baseCurvature * biasMultiplier
  in
    if curvature > 0.05
      then PathArc curvature
      else PathDirect

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation.
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Compute path offset for curved morph paths.
computePathOffset :: Number -> Number -> { x :: Number, y :: Number }
computePathOffset curvature t =
  let
    perpendicular = Math.sin (t * Math.pi)
    offset = perpendicular * curvature * 50.0  -- 50px max offset
  in
    { x: offset, y: offset * 0.5 }

-- | Compute midpoint effect strength (bell curve centered at t=0.5).
computeMidpointEffect :: Number -> Number
computeMidpointEffect t =
  let
    d = Math.abs (t - 0.5)
  in
    Math.cos (d * Math.pi) * 0.5 + 0.5
