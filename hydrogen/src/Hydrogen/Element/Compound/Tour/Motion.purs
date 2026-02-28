-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // tour // motion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour Motion System — The most fluid animations ever designed for a tour.
-- |
-- | ## Overview
-- |
-- | This leader module re-exports the complete animation vocabulary:
-- |
-- | | Submodule     | Purpose                                           |
-- | |---------------|---------------------------------------------------|
-- | | Spring        | Physics-based animation parameters                |
-- | | Timing        | CSS timing curves for tour animations             |
-- | | Spotlight     | Shape interpolation between targets               |
-- | | Choreography  | Tooltip entrance/exit/follow behaviors            |
-- | | Progress      | Progress indicator animations                     |
-- | | Attention     | Non-intrusive attention patterns                  |
-- | | Responsive    | Accessibility and performance scaling             |
-- |
-- | ## Design Philosophy
-- |
-- | Every animation serves the user's understanding. Motion should:
-- | - Guide attention without distraction
-- | - Provide spatial continuity between steps
-- | - Feel organic and responsive to input
-- | - Respect user preferences and device capabilities
-- |
-- | The animations here are designed for Frame.io-level fluidity.

module Hydrogen.Element.Compound.Tour.Motion
  ( -- * Spring Physics
    module ReexportSpring
  
    -- * Timing Curves
  , module ReexportTiming
  
    -- * Spotlight Morphing
  , module ReexportSpotlight
  
    -- * Tooltip Choreography
  , module ReexportChoreography
  
    -- * Progress Animations
  , module ReexportProgress
  
    -- * Attention Grabbers
  , module ReexportAttention
  
    -- * Responsive Motion
  , module ReexportResponsive
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- Spring Physics
import Hydrogen.Element.Compound.Tour.Motion.Spring
  ( SpringPreset(..)
  , SpringParams
  , snappySpring
  , bouncySpring
  , smoothSpring
  , preciseSpring
  , criticallyDamped
  , evaluateSpring
  , springDuration
  , springToCss
  ) as ReexportSpring

-- Timing Curves
import Hydrogen.Element.Compound.Tour.Motion.Timing
  ( TimingCurve
  , organicEase
  , morphEase
  , tooltipEntryEase
  , tooltipExitEase
  , progressEase
  , attentionEase
  ) as ReexportTiming

-- Spotlight Morphing
import Hydrogen.Element.Compound.Tour.Motion.Spotlight
  ( MorphConfig
  , defaultMorphConfig
  , snappyMorphConfig
  , elasticMorphConfig
  , MorphInterpolation(..)
  , MorphPath(..)
  , ShapeInterpolation
  , interpolateRect
  , interpolateCircle
  , interpolatePill
  , computeMorphPath
  ) as ReexportSpotlight

-- Tooltip Choreography
import Hydrogen.Element.Compound.Tour.Motion.Choreography
  ( TooltipChoreography
  , MicroInteractionConfig
  , ChoreographyPhase(..)
  , defaultChoreography
  , minimalChoreography
  , dramaticChoreography
  , defaultMicroInteractions
  , computeEntryAnimation
  , computeExitAnimation
  , computeFollowBehavior
  ) as ReexportChoreography

-- Progress Animations
import Hydrogen.Element.Compound.Tour.Motion.Progress
  ( ProgressAnimationStyle(..)
  , BarFillStyle(..)
  , DotProgressConfig
  , BarProgressConfig
  , CircularProgressConfig
  , FlipCounterConfig
  , defaultDotProgress
  , liquidBarProgress
  , strokeCircularProgress
  , flipCounterConfig
  ) as ReexportProgress

-- Attention Grabbers
import Hydrogen.Element.Compound.Tour.Motion.Attention
  ( AttentionPattern(..)
  , PulseConfig
  , BeaconConfig
  , MagneticConfig
  , CelebrationConfig
  , gentlePulse
  , subtleBeacon
  , magneticPull
  , celebrationBurst
  ) as ReexportAttention

-- Responsive Motion
import Hydrogen.Element.Compound.Tour.Motion.Responsive
  ( MotionScale(..)
  , PerformanceTier(..)
  , ReducedMotionFallback
  , computeMotionScale
  , reducedMotionFallbacks
  , performanceAdaptations
  ) as ReexportResponsive
