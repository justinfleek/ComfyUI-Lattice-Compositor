-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // tour // motion // progress
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Progress Animations — Alive, anticipating progress indicators.
-- |
-- | ## Overview
-- |
-- | Progress indicators are not just passive displays — they're designed
-- | to build anticipation and guide attention. Features include:
-- |
-- | - **Anticipation**: Next dot glows before becoming active
-- | - **Liquid fill**: Bar progress with wave effects
-- | - **Flip counters**: Airport departure board style
-- |
-- | ## Design Philosophy
-- |
-- | Good progress animation should:
-- | - Feel responsive to user actions
-- | - Build anticipation for next steps
-- | - Never feel mechanical or robotic

module Hydrogen.Element.Compound.Tour.Motion.Progress
  ( -- * Style Types
    ProgressAnimationStyle(..)
  , BarFillStyle(..)
  
    -- * Configuration Types
  , DotProgressConfig
  , BarProgressConfig
  , CircularProgressConfig
  , FlipCounterConfig
  
    -- * Presets
  , defaultDotProgress
  , liquidBarProgress
  , strokeCircularProgress
  , flipCounterConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , negate
  )

import Hydrogen.Element.Compound.Tour.Motion.Spring
  ( SpringParams
  , bouncySpring
  , smoothSpring
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Style of progress animation.
data ProgressAnimationStyle
  = ProgressDots DotProgressConfig
    -- ^ Dot-based progress with anticipation effects
  | ProgressBar BarProgressConfig
    -- ^ Linear bar with liquid/elastic fill
  | ProgressCircular CircularProgressConfig
    -- ^ Circular progress with stroke animation
  | ProgressFlipCounter FlipCounterConfig
    -- ^ Flip-clock style numeric counter
  | ProgressNone
    -- ^ No visible progress

derive instance eqProgressAnimationStyle :: Eq ProgressAnimationStyle

instance showProgressAnimationStyle :: Show ProgressAnimationStyle where
  show (ProgressDots _) = "dots"
  show (ProgressBar _) = "bar"
  show (ProgressCircular _) = "circular"
  show (ProgressFlipCounter _) = "flip-counter"
  show ProgressNone = "none"

-- | How bar fill animates.
data BarFillStyle
  = FillLinear          -- ^ Simple linear fill
  | FillLiquid          -- ^ Liquid wave effect at edge
  | FillElastic         -- ^ Elastic bounce at stops
  | FillGradient        -- ^ Animated gradient fill

derive instance eqBarFillStyle :: Eq BarFillStyle

instance showBarFillStyle :: Show BarFillStyle where
  show FillLinear = "linear"
  show FillLiquid = "liquid"
  show FillElastic = "elastic"
  show FillGradient = "gradient"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // configuration records
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dot progress configuration.
-- |
-- | Features anticipation: next dot glows slightly before becoming active.
type DotProgressConfig =
  { dotSize :: Number
    -- ^ Dot diameter (px)
  , dotSpacing :: Number
    -- ^ Space between dots (px)
  , activeScale :: Number
    -- ^ Scale of active dot (1.2 = 20% larger)
  , anticipationGlow :: Number
    -- ^ Glow intensity on "next" dot (0-1)
  , anticipationScale :: Number
    -- ^ Scale of "next" dot (1.05 = subtle growth)
  , transitionDuration :: Number
    -- ^ Dot transition duration (ms)
  , spring :: SpringParams
    -- ^ Spring for dot animations
  , completedOpacity :: Number
    -- ^ Opacity of completed dots (0.5 = dimmed)
  , pulseActive :: Boolean
    -- ^ Whether active dot pulses
  , pulseDuration :: Number
    -- ^ Pulse animation duration (ms)
  }

-- | Bar progress configuration with liquid fill effect.
type BarProgressConfig =
  { height :: Number
    -- ^ Bar height (px)
  , borderRadius :: Number
    -- ^ Bar corner radius (px)
  , fillStyle :: BarFillStyle
    -- ^ How the fill animates
  , overshoot :: Number
    -- ^ Elastic overshoot amount (0-1)
  , transitionDuration :: Number
    -- ^ Fill transition duration (ms)
  , spring :: SpringParams
    -- ^ Spring for fill animation
  , showPercentage :: Boolean
    -- ^ Show percentage text
  , glowOnProgress :: Boolean
    -- ^ Glow effect at fill edge
  }

-- | Circular progress configuration.
type CircularProgressConfig =
  { radius :: Number
    -- ^ Circle radius (px)
  , strokeWidth :: Number
    -- ^ Stroke width (px)
  , strokeLinecap :: String
    -- ^ "round" or "butt"
  , rotateStart :: Number
    -- ^ Starting rotation (degrees, -90 = top)
  , direction :: String
    -- ^ "clockwise" or "counterclockwise"
  , transitionDuration :: Number
    -- ^ Stroke transition duration (ms)
  , spring :: SpringParams
    -- ^ Spring for stroke animation
  , showCenter :: Boolean
    -- ^ Show content in center
  , glowOnProgress :: Boolean
    -- ^ Glow at stroke end
  }

-- | Flip counter configuration (like airport departure boards).
type FlipCounterConfig =
  { digitHeight :: Number
    -- ^ Height of each digit (px)
  , flipDuration :: Number
    -- ^ Single flip duration (ms)
  , staggerDelay :: Number
    -- ^ Delay between digit flips (ms)
  , perspective :: Number
    -- ^ 3D perspective (px)
  , showDivider :: Boolean
    -- ^ Show " / " divider (e.g., "3 / 5")
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default dot progress with anticipation.
defaultDotProgress :: DotProgressConfig
defaultDotProgress =
  { dotSize: 8.0
  , dotSpacing: 12.0
  , activeScale: 1.25
  , anticipationGlow: 0.3
  , anticipationScale: 1.08
  , transitionDuration: 300.0
  , spring: smoothSpring
  , completedOpacity: 0.6
  , pulseActive: true
  , pulseDuration: 2000.0
  }

-- | Liquid bar progress preset.
liquidBarProgress :: BarProgressConfig
liquidBarProgress =
  { height: 4.0
  , borderRadius: 2.0
  , fillStyle: FillLiquid
  , overshoot: 0.05
  , transitionDuration: 400.0
  , spring: bouncySpring
  , showPercentage: false
  , glowOnProgress: true
  }

-- | Stroke circular progress preset.
strokeCircularProgress :: CircularProgressConfig
strokeCircularProgress =
  { radius: 20.0
  , strokeWidth: 3.0
  , strokeLinecap: "round"
  , rotateStart: -90.0
  , direction: "clockwise"
  , transitionDuration: 400.0
  , spring: smoothSpring
  , showCenter: true
  , glowOnProgress: true
  }

-- | Default flip counter.
flipCounterConfig :: FlipCounterConfig
flipCounterConfig =
  { digitHeight: 32.0
  , flipDuration: 400.0
  , staggerDelay: 50.0
  , perspective: 500.0
  , showDivider: true
  }
