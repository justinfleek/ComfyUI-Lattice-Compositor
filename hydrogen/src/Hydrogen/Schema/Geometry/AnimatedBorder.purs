-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // geometry // animated-border
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AnimatedBorder — Dynamic border effects for interactive UI.
-- |
-- | ## Design Philosophy
-- |
-- | Static borders (Geometry.Border) handle CSS box borders.
-- | This module extends that with ANIMATED borders:
-- | - Gradient strokes (fill stroke with color gradient)
-- | - Animated dash patterns (marching ants, flowing energy)
-- | - Pulsing strokes (width oscillation over time)
-- | - Glowing strokes (animated outer glow)
-- | - Conic gradient borders (Linear's signature effect)
-- |
-- | ## Research Findings (Linear, Figma, Vercel)
-- |
-- | **Linear's Glowing Border Effect:**
-- | - Uses conic gradients rotating around the element
-- | - CSS mask-composite to create border from gradient
-- | - CSS Houdini @property for smooth angle animation
-- | - Mouse position tracking for spotlight effect
-- |
-- | **Implementation Strategy:**
-- | - Define declarative data, runtime interprets to WebGL/Canvas
-- | - No CSS strings - pure typed atoms
-- | - Animation timing via Temporal atoms
-- |
-- | ## Dependencies
-- |
-- | - Schema.Color.Gradient (gradient fills for strokes)
-- | - Schema.Geometry.Stroke (line caps, joins)
-- | - Schema.Dimension.Temporal (Milliseconds for animation timing)

module Hydrogen.Schema.Geometry.AnimatedBorder
  ( -- * Gradient Stroke
    GradientType(..)
  , GradientColorStop
  , GradientStroke(..)
  , gradientStroke
  , linearGradientStroke
  , conicGradientStroke
  
  -- * Conic Border (Linear-style)
  , ConicBorderConfig(..)
  , conicBorder
  , linearStyleBorder
  , spotlightBorder
  
  -- * Animated Dash
  , DashPattern(..)
  , dashPattern
  , DashAnimation(..)
  , DashDirection(..)
  , dashAnimation
  , AnimatedDash(..)
  , animatedDash
  , marchingAnts
  , flowingEnergy
  
  -- * Pulsing Stroke
  , PulseConfig(..)
  , pulseConfig
  , PulsingStroke(..)
  , pulsingStroke
  , subtlePulse
  , heartbeatPulse
  
  -- * Glowing Stroke
  , GlowConfig(..)
  , glowConfig
  , GlowingStroke(..)
  , glowingStroke
  , softGlow
  , neonGlow
  
  -- * Combined Animated Border
  , AnimatedBorder(..)
  , BorderEffect(..)
  , animatedBorder
  , defaultAnimatedBorder
  , noAnimatedBorder
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // gradient stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of gradient used for stroke
data GradientType
  = GradientLinear Number               -- ^ Linear gradient at angle (degrees)
  | GradientRadial                      -- ^ Radial gradient from center
  | GradientConic Number                -- ^ Conic gradient starting at angle
  | GradientConicAnimated Number Number -- ^ Animated conic (start angle, speed deg/sec)

derive instance eqGradientType :: Eq GradientType

instance showGradientType :: Show GradientType where
  show (GradientLinear angle) = "(GradientLinear " <> show angle <> ")"
  show GradientRadial = "GradientRadial"
  show (GradientConic angle) = "(GradientConic " <> show angle <> ")"
  show (GradientConicAnimated start speed) = 
    "(GradientConicAnimated " <> show start <> " " <> show speed <> ")"

-- | Color stop for gradient stroke (position 0.0-1.0, color as hex string)
-- | Note: Using string for color here to avoid circular dependency with Color module
-- | In practice, the runtime converts Schema.Color types to this format
type GradientColorStop = { position :: Number, color :: String }

-- | Gradient stroke configuration
-- |
-- | Fills the stroke path with a gradient instead of solid color.
-- | The gradient follows the stroke path.
newtype GradientStroke = GradientStroke
  { gradientType :: GradientType
  , stops :: Array GradientColorStop
  , strokeWidth :: Number             -- ^ Stroke width in pixels
  }

derive instance eqGradientStroke :: Eq GradientStroke

instance showGradientStroke :: Show GradientStroke where
  show (GradientStroke gs) = 
    "(GradientStroke type:" <> show gs.gradientType <> " width:" <> show gs.strokeWidth <> ")"

-- | Create gradient stroke with specified type and stops
gradientStroke :: GradientType -> Array GradientColorStop -> Number -> GradientStroke
gradientStroke gradientType stops strokeWidth = GradientStroke
  { gradientType
  , stops
  , strokeWidth
  }

-- | Create linear gradient stroke
linearGradientStroke :: Number -> Array GradientColorStop -> Number -> GradientStroke
linearGradientStroke angle = gradientStroke (GradientLinear angle)

-- | Create conic gradient stroke (Linear-style rotating border)
conicGradientStroke :: Number -> Array GradientColorStop -> Number -> GradientStroke
conicGradientStroke startAngle = gradientStroke (GradientConic startAngle)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // conic border (linear-style)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear-style conic gradient border configuration
-- |
-- | ## Research Finding: Linear's Signature Effect
-- |
-- | Linear uses conic gradients that rotate around elements on hover.
-- | Key techniques:
-- | - Conic gradient positioned at mouse cursor
-- | - CSS mask-composite creates border from full gradient
-- | - @property for smooth angle animation
-- | - Gaussian blur on outer edge for glow
-- |
-- | This type captures the declarative configuration.
-- | The runtime interprets it as WebGL/Canvas effects.
newtype ConicBorderConfig = ConicBorderConfig
  { borderWidth :: Number               -- ^ Border width in pixels
  , blurRadius :: Number                -- ^ Glow blur radius in pixels
  , rotationSpeed :: Number             -- ^ Rotation speed (degrees per second, 0 = static)
  , colors :: Array String              -- ^ Gradient colors (hex or rgba)
  , mouseTracking :: Boolean            -- ^ Track mouse for spotlight effect
  , spotlightAngle :: Number            -- ^ Spotlight cone angle in degrees
  , spotlightFalloff :: Number          -- ^ How quickly spotlight fades (0.0-1.0)
  }

derive instance eqConicBorderConfig :: Eq ConicBorderConfig

instance showConicBorderConfig :: Show ConicBorderConfig where
  show (ConicBorderConfig c) = 
    "(ConicBorderConfig width:" <> show c.borderWidth <> 
    " blur:" <> show c.blurRadius <> 
    " speed:" <> show c.rotationSpeed <> ")"

-- | Create conic border with custom configuration
conicBorder 
  :: { borderWidth :: Number
     , blurRadius :: Number
     , rotationSpeed :: Number
     , colors :: Array String
     }
  -> ConicBorderConfig
conicBorder cfg = ConicBorderConfig
  { borderWidth: cfg.borderWidth
  , blurRadius: cfg.blurRadius
  , rotationSpeed: cfg.rotationSpeed
  , colors: cfg.colors
  , mouseTracking: false
  , spotlightAngle: 90.0
  , spotlightFalloff: 0.5
  }

-- | Linear-style glowing border preset
-- |
-- | Blue-to-purple rotating gradient with glow
linearStyleBorder :: ConicBorderConfig
linearStyleBorder = ConicBorderConfig
  { borderWidth: 1.0
  , blurRadius: 8.0
  , rotationSpeed: 45.0  -- 45 degrees per second (8 second full rotation)
  , colors: ["#3b82f6", "#8b5cf6", "#ec4899", "#3b82f6"]  -- Blue -> Purple -> Pink -> Blue
  , mouseTracking: false
  , spotlightAngle: 90.0
  , spotlightFalloff: 0.5
  }

-- | Mouse-tracking spotlight border
-- |
-- | Gradient centers on mouse position with falloff
spotlightBorder :: ConicBorderConfig
spotlightBorder = ConicBorderConfig
  { borderWidth: 1.0
  , blurRadius: 12.0
  , rotationSpeed: 0.0  -- Static, follows mouse instead
  , colors: ["#ffffff", "transparent", "transparent"]
  , mouseTracking: true
  , spotlightAngle: 60.0
  , spotlightFalloff: 0.7
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // animated dash
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dash pattern definition
-- |
-- | Defines the pattern of dashes and gaps in a stroke.
-- | Values are in pixels.
newtype DashPattern = DashPattern
  { dashLength :: Number     -- ^ Length of each dash
  , gapLength :: Number      -- ^ Length of gap between dashes
  , offset :: Number         -- ^ Initial offset (for animation start position)
  }

derive instance eqDashPattern :: Eq DashPattern

instance showDashPattern :: Show DashPattern where
  show (DashPattern d) = 
    "(DashPattern dash:" <> show d.dashLength <> " gap:" <> show d.gapLength <> ")"

-- | Create dash pattern
dashPattern :: Number -> Number -> DashPattern
dashPattern dashLength gapLength = DashPattern
  { dashLength
  , gapLength
  , offset: 0.0
  }

-- | Direction of dash animation
data DashDirection
  = DashForward   -- ^ Dashes move forward along path
  | DashBackward  -- ^ Dashes move backward
  | DashAlternate -- ^ Alternate direction each cycle

derive instance eqDashDirection :: Eq DashDirection

instance showDashDirection :: Show DashDirection where
  show DashForward = "DashForward"
  show DashBackward = "DashBackward"
  show DashAlternate = "DashAlternate"

-- | Animation configuration for dashes
newtype DashAnimation = DashAnimation
  { speed :: Number            -- ^ Speed in pixels per second
  , direction :: DashDirection -- ^ Movement direction
  , easing :: String           -- ^ Easing function name (linear, ease-in-out, etc)
  }

derive instance eqDashAnimation :: Eq DashAnimation

instance showDashAnimation :: Show DashAnimation where
  show (DashAnimation a) = 
    "(DashAnimation speed:" <> show a.speed <> " direction:" <> show a.direction <> ")"

-- | Create dash animation
dashAnimation :: Number -> DashDirection -> DashAnimation
dashAnimation speed direction = DashAnimation
  { speed
  , direction
  , easing: "linear"
  }

-- | Complete animated dash configuration
newtype AnimatedDash = AnimatedDash
  { pattern :: DashPattern
  , animation :: DashAnimation
  , strokeWidth :: Number
  , color :: String            -- ^ Stroke color (hex or rgba)
  }

derive instance eqAnimatedDash :: Eq AnimatedDash

instance showAnimatedDash :: Show AnimatedDash where
  show (AnimatedDash ad) = 
    "(AnimatedDash pattern:" <> show ad.pattern <> " animation:" <> show ad.animation <> ")"

-- | Create animated dash
animatedDash :: DashPattern -> DashAnimation -> Number -> String -> AnimatedDash
animatedDash pattern animation strokeWidth color = AnimatedDash
  { pattern
  , animation
  , strokeWidth
  , color
  }

-- | "Marching ants" selection indicator preset
-- |
-- | Classic selection border with moving dashes
marchingAnts :: AnimatedDash
marchingAnts = AnimatedDash
  { pattern: DashPattern { dashLength: 4.0, gapLength: 4.0, offset: 0.0 }
  , animation: DashAnimation { speed: 20.0, direction: DashForward, easing: "linear" }
  , strokeWidth: 1.0
  , color: "#000000"
  }

-- | "Flowing energy" effect preset
-- |
-- | Longer dashes with faster movement, creates energy flow effect
flowingEnergy :: AnimatedDash
flowingEnergy = AnimatedDash
  { pattern: DashPattern { dashLength: 20.0, gapLength: 10.0, offset: 0.0 }
  , animation: DashAnimation { speed: 60.0, direction: DashForward, easing: "ease-in-out" }
  , strokeWidth: 2.0
  , color: "#3b82f6"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // pulsing stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pulse animation configuration
-- |
-- | Defines how stroke width oscillates over time.
newtype PulseConfig = PulseConfig
  { minWidth :: Number       -- ^ Minimum stroke width
  , maxWidth :: Number       -- ^ Maximum stroke width
  , period :: Number         -- ^ Pulse period in milliseconds
  , easing :: String         -- ^ Easing function for pulse
  }

derive instance eqPulseConfig :: Eq PulseConfig

instance showPulseConfig :: Show PulseConfig where
  show (PulseConfig p) = 
    "(PulseConfig min:" <> show p.minWidth <> " max:" <> show p.maxWidth <> " period:" <> show p.period <> ")"

-- | Create pulse config
pulseConfig :: Number -> Number -> Number -> PulseConfig
pulseConfig minWidth maxWidth period = PulseConfig
  { minWidth
  , maxWidth
  , period
  , easing: "ease-in-out"
  }

-- | Complete pulsing stroke configuration
newtype PulsingStroke = PulsingStroke
  { pulse :: PulseConfig
  , color :: String
  , initialWidth :: Number   -- ^ Starting width
  }

derive instance eqPulsingStroke :: Eq PulsingStroke

instance showPulsingStroke :: Show PulsingStroke where
  show (PulsingStroke ps) = "(PulsingStroke pulse:" <> show ps.pulse <> ")"

-- | Create pulsing stroke
pulsingStroke :: PulseConfig -> String -> PulsingStroke
pulsingStroke pulse color = PulsingStroke
  { pulse
  , color
  , initialWidth: let (PulseConfig p) = pulse in p.minWidth
  }

-- | Subtle pulse preset (minimal width change)
subtlePulse :: PulsingStroke
subtlePulse = PulsingStroke
  { pulse: PulseConfig { minWidth: 1.0, maxWidth: 1.5, period: 2000.0, easing: "ease-in-out" }
  , color: "#3b82f6"
  , initialWidth: 1.0
  }

-- | Heartbeat pulse preset (more dramatic)
heartbeatPulse :: PulsingStroke
heartbeatPulse = PulsingStroke
  { pulse: PulseConfig { minWidth: 1.0, maxWidth: 3.0, period: 1000.0, easing: "ease-out" }
  , color: "#ef4444"
  , initialWidth: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // glowing stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow effect configuration
-- |
-- | ## Research Finding: Apple Liquid Glass
-- |
-- | Effective glows use:
-- | - Multiple blur layers at different radii
-- | - Slight color tinting in glow
-- | - Noise texture (2-3% opacity) to prevent banding
-- | - Inner border gradient for depth
newtype GlowConfig = GlowConfig
  { blurRadius :: Number        -- ^ Primary blur radius in pixels
  , intensity :: Number         -- ^ Glow intensity (0.0-1.0)
  , color :: String             -- ^ Glow color (hex or rgba)
  , animated :: Boolean         -- ^ Whether glow pulses
  , animationPeriod :: Number   -- ^ Pulse period in ms (if animated)
  , noiseAmount :: Number       -- ^ Noise texture amount (0.0-0.05 recommended)
  }

derive instance eqGlowConfig :: Eq GlowConfig

instance showGlowConfig :: Show GlowConfig where
  show (GlowConfig g) = 
    "(GlowConfig blur:" <> show g.blurRadius <> " intensity:" <> show g.intensity <> ")"

-- | Create glow config
glowConfig :: Number -> Number -> String -> GlowConfig
glowConfig blurRadius intensity color = GlowConfig
  { blurRadius
  , intensity
  , color
  , animated: false
  , animationPeriod: 0.0
  , noiseAmount: 0.02  -- Default 2% noise per Apple research
  }

-- | Complete glowing stroke configuration
newtype GlowingStroke = GlowingStroke
  { glow :: GlowConfig
  , strokeWidth :: Number
  , strokeColor :: String       -- ^ Core stroke color
  }

derive instance eqGlowingStroke :: Eq GlowingStroke

instance showGlowingStroke :: Show GlowingStroke where
  show (GlowingStroke gs) = "(GlowingStroke glow:" <> show gs.glow <> ")"

-- | Create glowing stroke
glowingStroke :: GlowConfig -> Number -> String -> GlowingStroke
glowingStroke glow strokeWidth strokeColor = GlowingStroke
  { glow
  , strokeWidth
  , strokeColor
  }

-- | Soft glow preset (subtle, professional)
softGlow :: GlowingStroke
softGlow = GlowingStroke
  { glow: GlowConfig
      { blurRadius: 8.0
      , intensity: 0.4
      , color: "#3b82f6"
      , animated: false
      , animationPeriod: 0.0
      , noiseAmount: 0.02
      }
  , strokeWidth: 1.0
  , strokeColor: "#3b82f6"
  }

-- | Neon glow preset (vibrant, attention-grabbing)
neonGlow :: GlowingStroke
neonGlow = GlowingStroke
  { glow: GlowConfig
      { blurRadius: 16.0
      , intensity: 0.8
      , color: "#22d3ee"
      , animated: true
      , animationPeriod: 1500.0
      , noiseAmount: 0.03
      }
  , strokeWidth: 2.0
  , strokeColor: "#22d3ee"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // animated border
-- ═════════════════════════════════════════════════════════════════════════════

-- | Individual border effect type
data BorderEffect
  = EffectGradient GradientStroke
  | EffectConic ConicBorderConfig
  | EffectDash AnimatedDash
  | EffectPulse PulsingStroke
  | EffectGlow GlowingStroke
  | EffectNone

derive instance eqBorderEffect :: Eq BorderEffect

instance showBorderEffect :: Show BorderEffect where
  show (EffectGradient gs) = "(EffectGradient " <> show gs <> ")"
  show (EffectConic cb) = "(EffectConic " <> show cb <> ")"
  show (EffectDash ad) = "(EffectDash " <> show ad <> ")"
  show (EffectPulse ps) = "(EffectPulse " <> show ps <> ")"
  show (EffectGlow gs) = "(EffectGlow " <> show gs <> ")"
  show EffectNone = "EffectNone"

-- | Combined animated border configuration
-- |
-- | Supports layered effects:
-- | - Primary effect (e.g., gradient stroke)
-- | - Secondary effect (e.g., glow on top)
-- | - Hover behavior
newtype AnimatedBorder = AnimatedBorder
  { primary :: BorderEffect         -- ^ Main border effect
  , secondary :: Maybe BorderEffect -- ^ Optional overlay effect
  , hoverPrimary :: Maybe BorderEffect -- ^ Primary effect on hover
  , hoverSecondary :: Maybe BorderEffect -- ^ Secondary effect on hover
  , transitionDuration :: Number    -- ^ Transition duration in ms
  }

derive instance eqAnimatedBorder :: Eq AnimatedBorder

instance showAnimatedBorder :: Show AnimatedBorder where
  show (AnimatedBorder ab) = 
    "(AnimatedBorder primary:" <> show ab.primary <> ")"

-- | Create animated border with primary effect only
animatedBorder :: BorderEffect -> AnimatedBorder
animatedBorder primary = AnimatedBorder
  { primary
  , secondary: Nothing
  , hoverPrimary: Nothing
  , hoverSecondary: Nothing
  , transitionDuration: 200.0
  }

-- | Default animated border (subtle gradient)
defaultAnimatedBorder :: AnimatedBorder
defaultAnimatedBorder = AnimatedBorder
  { primary: EffectGlow softGlow
  , secondary: Nothing
  , hoverPrimary: Just (EffectConic linearStyleBorder)
  , hoverSecondary: Nothing
  , transitionDuration: 200.0
  }

-- | No animated border effects
noAnimatedBorder :: AnimatedBorder
noAnimatedBorder = AnimatedBorder
  { primary: EffectNone
  , secondary: Nothing
  , hoverPrimary: Nothing
  , hoverSecondary: Nothing
  , transitionDuration: 0.0
  }
