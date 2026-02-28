-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // tour // motion // attention
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Attention Grabbers — Non-intrusive attention patterns.
-- |
-- | ## Overview
-- |
-- | Attention animations that don't feel like errors. Key insight:
-- | - Error pulses are red and fast
-- | - Friendly pulses are branded colors, slow, and subtle
-- |
-- | ## Design Philosophy
-- |
-- | These patterns guide attention without alarming the user:
-- | - **Pulse**: Gentle breathing that invites interaction
-- | - **Beacon**: Subtle expanding waves
-- | - **Magnetic**: Elements feel attracted to target
-- | - **Celebration**: Particle effects for completion

module Hydrogen.Element.Compound.Tour.Motion.Attention
  ( -- * Pattern Types
    AttentionPattern(..)
  
    -- * Configuration Types
  , PulseConfig
  , BeaconConfig
  , MagneticConfig
  , CelebrationConfig
  
    -- * Presets
  , gentlePulse
  , subtleBeacon
  , magneticPull
  , celebrationBurst
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , (/)
  )

import Data.Maybe (Maybe(Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Non-intrusive attention patterns that don't feel like errors.
data AttentionPattern
  = AttentionPulse PulseConfig
    -- ^ Gentle pulsing that doesn't alarm
  | AttentionBeacon BeaconConfig
    -- ^ Subtle beacon animation
  | AttentionMagnetic MagneticConfig
    -- ^ "Magnetic" pull effect toward target
  | AttentionCelebration CelebrationConfig
    -- ^ Particle effects for completion
  | AttentionNone
    -- ^ No attention animation

derive instance eqAttentionPattern :: Eq AttentionPattern

instance showAttentionPattern :: Show AttentionPattern where
  show (AttentionPulse _) = "pulse"
  show (AttentionBeacon _) = "beacon"
  show (AttentionMagnetic _) = "magnetic"
  show (AttentionCelebration _) = "celebration"
  show AttentionNone = "none"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // configuration records
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pulse configuration that doesn't feel like an error.
-- |
-- | Key insight: error pulses are red and fast. Friendly pulses are
-- | branded colors, slow, and subtle.
type PulseConfig =
  { scaleMin :: Number
    -- ^ Minimum scale (1.0 = no shrink)
  , scaleMax :: Number
    -- ^ Maximum scale (1.03 = very subtle)
  , opacityMin :: Number
    -- ^ Minimum opacity (0.7 = subtle dim)
  , opacityMax :: Number
    -- ^ Maximum opacity (1.0)
  , duration :: Number
    -- ^ Full pulse cycle (ms) — slow = friendly
  , easing :: String
    -- ^ "ease-in-out" for breathing feel
  , iterations :: Number
    -- ^ Number of pulses (Infinity for continuous)
  , ringExpand :: Boolean
    -- ^ Expanding ring effect
  , ringMaxScale :: Number
    -- ^ Ring maximum scale
  , ringOpacityStart :: Number
    -- ^ Ring starting opacity
  }

-- | Beacon configuration.
type BeaconConfig =
  { color :: String
    -- ^ Beacon color (usually brand color)
  , size :: Number
    -- ^ Beacon size (px)
  , waves :: Int
    -- ^ Number of expanding waves
  , waveDuration :: Number
    -- ^ Single wave duration (ms)
  , waveDelay :: Number
    -- ^ Delay between waves (ms)
  , waveMaxScale :: Number
    -- ^ Maximum scale of waves
  , fadeDistance :: Number
    -- ^ Distance at which waves fully fade
  }

-- | Magnetic pull configuration.
-- |
-- | Creates a subtle "pull" toward the target, making elements
-- | feel magnetically attracted.
type MagneticConfig =
  { strength :: Number
    -- ^ Pull strength (0-1)
  , radius :: Number
    -- ^ Effect radius (px)
  , smoothing :: Number
    -- ^ Movement smoothing (0-1)
  , affectsBackground :: Boolean
    -- ^ Whether background slightly warps
  , cursorInfluence :: Boolean
    -- ^ Whether cursor position influences
  }

-- | Celebration configuration for completion moments.
type CelebrationConfig =
  { particleCount :: Int
    -- ^ Number of particles
  , particleColors :: Array String
    -- ^ Particle colors
  , spread :: Number
    -- ^ Spread angle (degrees)
  , velocity :: Number
    -- ^ Initial velocity
  , gravity :: Number
    -- ^ Gravity effect
  , duration :: Number
    -- ^ Animation duration (ms)
  , confetti :: Boolean
    -- ^ Confetti style vs sparkles
  , sound :: Maybe String
    -- ^ Optional sound effect path
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Infinity constant for continuous animations.
infinity :: Number
infinity = 1.0 / 0.0

-- | Gentle pulse that doesn't alarm.
gentlePulse :: PulseConfig
gentlePulse =
  { scaleMin: 1.0
  , scaleMax: 1.02
  , opacityMin: 0.85
  , opacityMax: 1.0
  , duration: 3000.0        -- Very slow = calming
  , easing: "ease-in-out"
  , iterations: infinity
  , ringExpand: true
  , ringMaxScale: 1.5
  , ringOpacityStart: 0.4
  }

-- | Subtle beacon effect.
subtleBeacon :: BeaconConfig
subtleBeacon =
  { color: "currentColor"
  , size: 12.0
  , waves: 2
  , waveDuration: 2000.0
  , waveDelay: 700.0
  , waveMaxScale: 2.5
  , fadeDistance: 40.0
  }

-- | Subtle magnetic pull.
magneticPull :: MagneticConfig
magneticPull =
  { strength: 0.15
  , radius: 100.0
  , smoothing: 0.8
  , affectsBackground: false
  , cursorInfluence: true
  }

-- | Celebration burst for tour completion.
celebrationBurst :: CelebrationConfig
celebrationBurst =
  { particleCount: 30
  , particleColors: ["#FFD700", "#FFA500", "#FF69B4", "#00CED1", "#7B68EE"]
  , spread: 60.0
  , velocity: 400.0
  , gravity: 800.0
  , duration: 2000.0
  , confetti: true
  , sound: Nothing
  }
