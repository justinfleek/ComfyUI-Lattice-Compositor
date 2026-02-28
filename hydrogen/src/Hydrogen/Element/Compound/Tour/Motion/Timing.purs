-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // tour // motion // timing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Timing Curves — CSS-ready easing functions for tour animations.
-- |
-- | ## Overview
-- |
-- | Each timing curve is tuned for a specific purpose in tour animations.
-- | These are the CSS cubic-bezier values that create the "Frame.io feel".
-- |
-- | ## Design Philosophy
-- |
-- | Unlike spring physics (which handles interruption gracefully), timing
-- | curves are for animations that play to completion. Each curve here
-- | serves a specific perceptual purpose:
-- |
-- | - **Organic**: General UI, feels intentional
-- | - **Morph**: Shape transitions, maintains visual continuity
-- | - **Tooltip Entry/Exit**: Arrival and departure choreography
-- | - **Progress**: Building anticipation
-- | - **Attention**: Continuous, breathing animations

module Hydrogen.Element.Compound.Tour.Motion.Timing
  ( -- * Types
    TimingCurve
  
    -- * Presets
  , organicEase
  , morphEase
  , tooltipEntryEase
  , tooltipExitEase
  , progressEase
  , attentionEase
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS-ready timing curve definition.
-- |
-- | Contains both the CSS value and documentation for the curve's intended use.
type TimingCurve =
  { name :: String
    -- ^ Semantic name for the curve
  , css :: String
    -- ^ CSS cubic-bezier() or keyword value
  , description :: String
    -- ^ When to use this curve
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Organic ease — feels natural and intentional.
-- |
-- | `cubic-bezier(0.22, 1.0, 0.36, 1.0)`
-- |
-- | Fast start, slow settle. Like setting something down gently.
-- | Use for: most UI elements, general transitions.
organicEase :: TimingCurve
organicEase =
  { name: "organic"
  , css: "cubic-bezier(0.22, 1.0, 0.36, 1.0)"
  , description: "Natural deceleration, used for most UI elements"
  }

-- | Morph ease — maintains perceptual continuity.
-- |
-- | `cubic-bezier(0.65, 0.0, 0.35, 1.0)`
-- |
-- | Smooth acceleration and deceleration for shape transitions.
-- | Use for: spotlight morphing, shape interpolation.
morphEase :: TimingCurve
morphEase =
  { name: "morph"
  , css: "cubic-bezier(0.65, 0.0, 0.35, 1.0)"
  , description: "Symmetric ease for shape morphing"
  }

-- | Tooltip entry — arrives with confidence.
-- |
-- | `cubic-bezier(0.34, 1.56, 0.64, 1.0)`
-- |
-- | Slight overshoot creates "arrival" feeling.
-- | Use for: tooltip appearance, popover entry.
tooltipEntryEase :: TimingCurve
tooltipEntryEase =
  { name: "tooltip-entry"
  , css: "cubic-bezier(0.34, 1.56, 0.64, 1.0)"
  , description: "Bouncy entry with slight overshoot"
  }

-- | Tooltip exit — departs gracefully.
-- |
-- | `cubic-bezier(0.36, 0.0, 0.66, -0.56)`
-- |
-- | Quick departure with slight anticipation.
-- | Use for: tooltip dismissal, popover exit.
tooltipExitEase :: TimingCurve
tooltipExitEase =
  { name: "tooltip-exit"
  , css: "cubic-bezier(0.36, 0.0, 0.66, -0.56)"
  , description: "Quick exit with anticipation"
  }

-- | Progress ease — builds anticipation.
-- |
-- | `cubic-bezier(0.4, 0.0, 0.2, 1.0)`
-- |
-- | Steady acceleration, then smooth arrival at destination.
-- | Use for: progress indicators, step transitions.
progressEase :: TimingCurve
progressEase =
  { name: "progress"
  , css: "cubic-bezier(0.4, 0.0, 0.2, 1.0)"
  , description: "Material Design standard easing"
  }

-- | Attention ease — gentle breathing.
-- |
-- | `ease-in-out`
-- |
-- | Symmetric ease for continuous attention animations.
-- | Use for: pulsing, breathing effects, continuous loops.
attentionEase :: TimingCurve
attentionEase =
  { name: "attention"
  , css: "ease-in-out"
  , description: "Symmetric ease for continuous animations"
  }
