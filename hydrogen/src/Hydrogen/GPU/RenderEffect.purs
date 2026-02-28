-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // gpu // render-effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | RenderEffect — Unified Real-Time Effect Pipeline
-- |
-- | ## Design Philosophy
-- |
-- | Frame.io, Ghostty, Linear — hyper-responsive UIs that feel alive.
-- | This module provides the composable effect vocabulary for that experience:
-- |
-- | - **Blur effects**: Gaussian, directional, radial, zoom
-- | - **Glow effects**: Inner, outer, animated pulse, color cycling
-- | - **Shadow effects**: Drop, box, layered, animated
-- | - **Border effects**: Gradient stroke, conic rotation, marching ants
-- | - **Material effects**: Glass, frosted, noise, grain
-- | - **Temporal effects**: Motion blur, echo, time displacement
-- |
-- | ## Architecture
-- |
-- | Effects are **pure data** describing GPU render passes. At billion-agent
-- | scale, effects compose deterministically:
-- |
-- | ```
-- | Element + Effects → RenderPlan → GPU Passes → Tensor Output
-- | ```
-- |
-- | Same effect parameters = same pixels. Always.
-- |
-- | ## Render Pass Model
-- |
-- | Effects execute as GPU render passes. Each pass:
-- | 1. Reads from source texture(s)
-- | 2. Applies effect computation (shader or compute kernel)
-- | 3. Writes to target texture
-- |
-- | Passes compose via texture chaining. The interpreter optimizes:
-- | - Fuses compatible passes
-- | - Reorders for cache locality
-- | - Batches similar effects
-- |
-- | ## Frame.io/Ghostty-level Responsiveness
-- |
-- | The key insight: **animation state is external to effects**.
-- | Effects receive `FrameState` (time, mouse, animation phases) and
-- | produce deterministic output. The runtime advances state at 60/120fps.
-- |
-- | This means:
-- | - Effects are stateless functions
-- | - Animation is predictable (replay-safe)
-- | - No per-effect timers or callbacks
-- | - Billion agents can share animation clock

module Hydrogen.GPU.RenderEffect
  ( -- * Core Types
    RenderEffect(..)
  , EffectPass
  , PassInput(..)
  , PassOutput(..)
  , BlendMode(..)
  
  -- * Effect Categories
  , BlurEffect(..)
  , GlowEffect(..)
  , ShadowEffect(..)
  , BorderEffect(..)
  , MaterialEffect(..)
  , TemporalEffect(..)
  , ParticleEffect(..)
  
  -- * Blur Variants
  , GaussianBlur(..)
  , DirectionalBlur(..)
  , RadialBlur(..)
  , ZoomBlur(..)
  
  -- * Glow Variants  
  , InnerGlow(..)
  , OuterGlow(..)
  , PulsingGlow(..)
  , NeonGlow(..)
  , GlowColor
  , GlowEasing(..)
  
  -- * Shadow Variants
  , DropShadowEffect(..)
  , BoxShadowEffect(..)
  , ContactShadow(..)
  
  -- * Border Variants
  , GradientBorder(..)
  , ConicBorder(..)
  , AnimatedDashBorder(..)
  , GlowingBorder(..)
  , BorderGradientType(..)
  , DashDirection(..)
  
  -- * Material Variants
  , GlassEffect(..)
  , FrostedGlass(..)
  , NoiseOverlay(..)
  , GrainEffect(..)
  , NoiseType(..)
  
  -- * Temporal Variants
  , MotionBlur(..)
  , EchoEffect(..)
  , TimeWarp(..)
  , EchoOperator(..)
  
  -- * Particle Variants
  , ParticleField(..)
  , ParticleEmitter(..)
  
  -- * Effect Composition
  , effectSequence
  , effectParallel
  , effectConditional
  , effectWhen
  , effectIfThenElse
  , effectAnimated
  
  -- * Condition Types
  , EffectCondition(..)
  
  -- * Effect Constructors
  , gaussianBlur
  , directionalBlur
  , radialBlur
  , zoomBlur
  , innerGlow
  , outerGlow
  , pulsingGlow
  , neonGlow
  , dropShadowEffect
  , boxShadowEffect
  , contactShadow
  , gradientBorder
  , conicBorder
  , animatedDashBorder
  , glowingBorder
  , glassEffect
  , frostedGlass
  , noiseOverlay
  , grainEffect
  , motionBlur
  , echoEffect
  , timeWarp
  , particleField
  , particleEmitter
  
  -- * Presets
  , subtleBlur
  , heavyBlur
  , softGlow
  , intenseGlow
  , elevatedShadow
  , floatingShadow
  , linearBorder
  , spotlightBorder
  , liquidGlass
  , acrylicGlass
  , filmGrain
  , digitalNoise
  , backgroundBlur
  , heroBlur
  , centeredZoomBlur
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.GPU.ComputeKernel
  ( BlurQuality(BlurQualityLow, BlurQualityMedium, BlurQualityHigh)
  , RadialBlurType(RadialTypeSpin, RadialTypeZoom)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A render effect — composable GPU operation.
-- |
-- | Effects are pure data describing visual transformations.
-- | The interpreter converts them to GPU render passes.
data RenderEffect
  = EffectBlur BlurEffect
  | EffectGlow GlowEffect
  | EffectShadow ShadowEffect
  | EffectBorder BorderEffect
  | EffectMaterial MaterialEffect
  | EffectTemporal TemporalEffect
  | EffectParticle ParticleEffect
  | EffectSequence (Array RenderEffect)     -- Apply in order
  | EffectParallel (Array RenderEffect)     -- Apply simultaneously (blend)
  | EffectConditional                       -- Apply based on condition
      { condition :: EffectCondition
      , thenEffect :: RenderEffect
      , elseEffect :: Maybe RenderEffect
      }
  | EffectAnimated                          -- Interpolate between states
      { from :: RenderEffect
      , to :: RenderEffect
      , progress :: Number                  -- 0.0-1.0
      }
  | EffectNone                              -- Identity (no effect)

derive instance eqRenderEffect :: Eq RenderEffect

instance showRenderEffect :: Show RenderEffect where
  show (EffectBlur b) = "(EffectBlur " <> show b <> ")"
  show (EffectGlow g) = "(EffectGlow " <> show g <> ")"
  show (EffectShadow s) = "(EffectShadow " <> show s <> ")"
  show (EffectBorder b) = "(EffectBorder " <> show b <> ")"
  show (EffectMaterial m) = "(EffectMaterial " <> show m <> ")"
  show (EffectTemporal t) = "(EffectTemporal " <> show t <> ")"
  show (EffectParticle p) = "(EffectParticle " <> show p <> ")"
  show (EffectSequence _) = "(EffectSequence [...])"
  show (EffectParallel _) = "(EffectParallel [...])"
  show (EffectConditional _) = "(EffectConditional ...)"
  show (EffectAnimated _) = "(EffectAnimated ...)"
  show EffectNone = "EffectNone"

-- | Condition for conditional effects
data EffectCondition
  = ConditionHover           -- Mouse over element
  | ConditionActive          -- Element is active (pressed)
  | ConditionFocus           -- Element has focus
  | ConditionAnimationPhase  -- Based on animation progress
      { minProgress :: Number
      , maxProgress :: Number
      }
  | ConditionViewportSize    -- Based on viewport dimensions
      { minWidth :: Number
      , minHeight :: Number
      }
  | ConditionAlways          -- Always true (for else branch)

derive instance eqEffectCondition :: Eq EffectCondition

instance showEffectCondition :: Show EffectCondition where
  show ConditionHover = "ConditionHover"
  show ConditionActive = "ConditionActive"
  show ConditionFocus = "ConditionFocus"
  show (ConditionAnimationPhase _) = "(ConditionAnimationPhase ...)"
  show (ConditionViewportSize _) = "(ConditionViewportSize ...)"
  show ConditionAlways = "ConditionAlways"

-- | Effect render pass specification
type EffectPass =
  { input :: PassInput
  , output :: PassOutput
  , effect :: RenderEffect
  , blendMode :: BlendMode
  }

-- | Input source for effect pass
data PassInput
  = InputPrevious           -- Output of previous pass
  | InputOriginal           -- Original unprocessed input
  | InputTexture Int        -- Named texture by ID
  | InputMultiple (Array PassInput)  -- Multiple inputs for composite

derive instance eqPassInput :: Eq PassInput

-- | Output target for effect pass
data PassOutput
  = OutputNext              -- Input for next pass
  | OutputFinal             -- Final output
  | OutputTexture Int       -- Named texture for later use
  | OutputScreen            -- Direct to screen

derive instance eqPassOutput :: Eq PassOutput

-- | Blend mode for compositing
data BlendMode
  = BlendNormal
  | BlendAdd
  | BlendMultiply
  | BlendScreen
  | BlendOverlay
  | BlendSoftLight
  | BlendHardLight
  | BlendDifference
  | BlendExclusion

derive instance eqBlendMode :: Eq BlendMode

instance showBlendMode :: Show BlendMode where
  show BlendNormal = "BlendNormal"
  show BlendAdd = "BlendAdd"
  show BlendMultiply = "BlendMultiply"
  show BlendScreen = "BlendScreen"
  show BlendOverlay = "BlendOverlay"
  show BlendSoftLight = "BlendSoftLight"
  show BlendHardLight = "BlendHardLight"
  show BlendDifference = "BlendDifference"
  show BlendExclusion = "BlendExclusion"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // blur effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blur effect variants
data BlurEffect
  = BlurGaussian GaussianBlur
  | BlurDirectional DirectionalBlur
  | BlurRadial RadialBlur
  | BlurZoom ZoomBlur

derive instance eqBlurEffect :: Eq BlurEffect

instance showBlurEffect :: Show BlurEffect where
  show (BlurGaussian g) = "(BlurGaussian " <> show g <> ")"
  show (BlurDirectional d) = "(BlurDirectional " <> show d <> ")"
  show (BlurRadial r) = "(BlurRadial " <> show r <> ")"
  show (BlurZoom z) = "(BlurZoom " <> show z <> ")"

-- | Gaussian blur — classic soft blur
newtype GaussianBlur = GaussianBlur
  { radius :: Number         -- Blur radius in pixels (0-100)
  , quality :: BlurQuality   -- Quality/performance tradeoff
  }

derive instance eqGaussianBlur :: Eq GaussianBlur

instance showGaussianBlur :: Show GaussianBlur where
  show (GaussianBlur b) = "(GaussianBlur radius:" <> show b.radius <> ")"

-- | Directional blur — motion in a direction
newtype DirectionalBlur = DirectionalBlur
  { angle :: Number          -- Direction in degrees (0-360)
  , distance :: Number       -- Blur distance in pixels
  , quality :: BlurQuality
  }

derive instance eqDirectionalBlur :: Eq DirectionalBlur

instance showDirectionalBlur :: Show DirectionalBlur where
  show (DirectionalBlur b) = "(DirectionalBlur angle:" <> show b.angle <> ")"

-- | Radial blur — spin/zoom from center
newtype RadialBlur = RadialBlur
  { centerX :: Number        -- Center X (0.0-1.0 normalized)
  , centerY :: Number        -- Center Y (0.0-1.0 normalized)
  , amount :: Number         -- Blur amount (0-100)
  , blurType :: RadialBlurType
  }

derive instance eqRadialBlur :: Eq RadialBlur

instance showRadialBlur :: Show RadialBlur where
  show (RadialBlur b) = "(RadialBlur amount:" <> show b.amount <> ")"

-- | Zoom blur — radial motion blur
newtype ZoomBlur = ZoomBlur
  { centerX :: Number
  , centerY :: Number
  , strength :: Number       -- Zoom strength (0-100)
  }

derive instance eqZoomBlur :: Eq ZoomBlur

instance showZoomBlur :: Show ZoomBlur where
  show (ZoomBlur b) = "(ZoomBlur strength:" <> show b.strength <> ")"

-- Note: BlurQuality and RadialBlurType are imported from Hydrogen.GPU.ComputeKernel
-- and re-exported for API completeness. The canonical definitions live at the
-- GPU compute level where quality/performance tradeoffs are actually implemented.

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // glow effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow effect variants
data GlowEffect
  = GlowInner InnerGlow
  | GlowOuter OuterGlow
  | GlowPulsing PulsingGlow
  | GlowNeon NeonGlow

derive instance eqGlowEffect :: Eq GlowEffect

instance showGlowEffect :: Show GlowEffect where
  show (GlowInner g) = "(GlowInner " <> show g <> ")"
  show (GlowOuter g) = "(GlowOuter " <> show g <> ")"
  show (GlowPulsing g) = "(GlowPulsing " <> show g <> ")"
  show (GlowNeon g) = "(GlowNeon " <> show g <> ")"

-- | Inner glow — glow inside element edges
newtype InnerGlow = InnerGlow
  { color :: GlowColor
  , radius :: Number         -- Glow radius in pixels
  , intensity :: Number      -- Glow intensity (0.0-1.0)
  , choke :: Number          -- Edge definition (0.0-1.0)
  }

derive instance eqInnerGlow :: Eq InnerGlow

instance showInnerGlow :: Show InnerGlow where
  show (InnerGlow g) = "(InnerGlow radius:" <> show g.radius <> ")"

-- | Outer glow — glow outside element edges
newtype OuterGlow = OuterGlow
  { color :: GlowColor
  , radius :: Number
  , intensity :: Number
  , spread :: Number         -- How far glow spreads (0.0-1.0)
  }

derive instance eqOuterGlow :: Eq OuterGlow

instance showOuterGlow :: Show OuterGlow where
  show (OuterGlow g) = "(OuterGlow radius:" <> show g.radius <> ")"

-- | Pulsing glow — animated intensity
newtype PulsingGlow = PulsingGlow
  { color :: GlowColor
  , minRadius :: Number
  , maxRadius :: Number
  , minIntensity :: Number
  , maxIntensity :: Number
  , periodMs :: Number       -- Pulse period in milliseconds
  , easing :: GlowEasing
  }

derive instance eqPulsingGlow :: Eq PulsingGlow

instance showPulsingGlow :: Show PulsingGlow where
  show (PulsingGlow g) = "(PulsingGlow period:" <> show g.periodMs <> ")"

-- | Neon glow — multi-layer vibrant glow
newtype NeonGlow = NeonGlow
  { coreColor :: GlowColor   -- Inner core color
  , outerColor :: GlowColor  -- Outer glow color
  , coreRadius :: Number
  , outerRadius :: Number
  , intensity :: Number
  , flicker :: Boolean       -- Random intensity variation
  , flickerSpeed :: Number   -- Flicker rate if enabled
  }

derive instance eqNeonGlow :: Eq NeonGlow

instance showNeonGlow :: Show NeonGlow where
  show (NeonGlow g) = "(NeonGlow intensity:" <> show g.intensity <> ")"

-- | Glow color specification
type GlowColor =
  { r :: Int                 -- Red (0-255)
  , g :: Int                 -- Green (0-255)
  , b :: Int                 -- Blue (0-255)
  , a :: Number              -- Alpha (0.0-1.0)
  }

-- | Glow easing type
data GlowEasing
  = GlowEaseLinear
  | GlowEaseSine
  | GlowEaseQuad
  | GlowEaseCubic

derive instance eqGlowEasing :: Eq GlowEasing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // shadow effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shadow effect variants
data ShadowEffect
  = ShadowDrop DropShadowEffect
  | ShadowBox BoxShadowEffect
  | ShadowContact ContactShadow

derive instance eqShadowEffect :: Eq ShadowEffect

instance showShadowEffect :: Show ShadowEffect where
  show (ShadowDrop s) = "(ShadowDrop " <> show s <> ")"
  show (ShadowBox s) = "(ShadowBox " <> show s <> ")"
  show (ShadowContact s) = "(ShadowContact " <> show s <> ")"

-- | Drop shadow — follows element shape
newtype DropShadowEffect = DropShadowEffect
  { offsetX :: Number        -- Horizontal offset in pixels
  , offsetY :: Number        -- Vertical offset in pixels
  , blur :: Number           -- Blur radius
  , color :: GlowColor
  }

derive instance eqDropShadowEffect :: Eq DropShadowEffect

instance showDropShadowEffect :: Show DropShadowEffect where
  show (DropShadowEffect s) = "(DropShadowEffect blur:" <> show s.blur <> ")"

-- | Box shadow — CSS-style with spread
newtype BoxShadowEffect = BoxShadowEffect
  { offsetX :: Number
  , offsetY :: Number
  , blur :: Number
  , spread :: Number         -- Shadow expansion/contraction
  , color :: GlowColor
  , inset :: Boolean         -- Inner shadow
  }

derive instance eqBoxShadowEffect :: Eq BoxShadowEffect

instance showBoxShadowEffect :: Show BoxShadowEffect where
  show (BoxShadowEffect s) = "(BoxShadowEffect blur:" <> show s.blur <> ")"

-- | Contact shadow — grounded shadow beneath element
newtype ContactShadow = ContactShadow
  { blur :: Number
  , opacity :: Number        -- Shadow opacity (0.0-1.0)
  , offsetY :: Number        -- Vertical offset (typically negative)
  , scale :: Number          -- Shadow scale relative to element
  }

derive instance eqContactShadow :: Eq ContactShadow

instance showContactShadow :: Show ContactShadow where
  show (ContactShadow s) = "(ContactShadow blur:" <> show s.blur <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // border effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border effect variants
data BorderEffect
  = BorderGradient GradientBorder
  | BorderConic ConicBorder
  | BorderAnimatedDash AnimatedDashBorder
  | BorderGlowing GlowingBorder

derive instance eqBorderEffect :: Eq BorderEffect

instance showBorderEffect :: Show BorderEffect where
  show (BorderGradient b) = "(BorderGradient " <> show b <> ")"
  show (BorderConic b) = "(BorderConic " <> show b <> ")"
  show (BorderAnimatedDash b) = "(BorderAnimatedDash " <> show b <> ")"
  show (BorderGlowing b) = "(BorderGlowing " <> show b <> ")"

-- | Gradient border — fill stroke with gradient
newtype GradientBorder = GradientBorder
  { width :: Number          -- Border width in pixels
  , gradientType :: BorderGradientType
  , colors :: Array GlowColor
  , angle :: Number          -- Gradient angle for linear (degrees)
  }

derive instance eqGradientBorder :: Eq GradientBorder

instance showGradientBorder :: Show GradientBorder where
  show (GradientBorder b) = "(GradientBorder width:" <> show b.width <> ")"

-- | Border gradient type
data BorderGradientType
  = BorderGradientLinear
  | BorderGradientRadial
  | BorderGradientConic

derive instance eqBorderGradientType :: Eq BorderGradientType

-- | Conic border — Linear-style rotating gradient
newtype ConicBorder = ConicBorder
  { width :: Number
  , colors :: Array GlowColor
  , rotationSpeed :: Number  -- Degrees per second (0 = static)
  , blurRadius :: Number     -- Glow around border
  , mouseTracking :: Boolean -- Follow mouse position
  , spotlightAngle :: Number -- Spotlight cone width (degrees)
  }

derive instance eqConicBorder :: Eq ConicBorder

instance showConicBorder :: Show ConicBorder where
  show (ConicBorder b) = "(ConicBorder speed:" <> show b.rotationSpeed <> ")"

-- | Animated dash border — marching ants, flowing energy
newtype AnimatedDashBorder = AnimatedDashBorder
  { width :: Number
  , dashLength :: Number
  , gapLength :: Number
  , speed :: Number          -- Pixels per second
  , direction :: DashDirection
  , color :: GlowColor
  }

derive instance eqAnimatedDashBorder :: Eq AnimatedDashBorder

instance showAnimatedDashBorder :: Show AnimatedDashBorder where
  show (AnimatedDashBorder b) = "(AnimatedDashBorder speed:" <> show b.speed <> ")"

-- | Dash animation direction
data DashDirection
  = DashDirectionForward
  | DashDirectionBackward
  | DashDirectionAlternate

derive instance eqDashDirection :: Eq DashDirection

-- | Glowing border — border with outer glow
newtype GlowingBorder = GlowingBorder
  { width :: Number
  , borderColor :: GlowColor
  , glowColor :: GlowColor
  , glowRadius :: Number
  , glowIntensity :: Number
  , animated :: Boolean      -- Pulse glow
  , pulseSpeed :: Number     -- Pulse period in ms
  }

derive instance eqGlowingBorder :: Eq GlowingBorder

instance showGlowingBorder :: Show GlowingBorder where
  show (GlowingBorder b) = "(GlowingBorder width:" <> show b.width <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // material effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Material effect variants
data MaterialEffect
  = MaterialGlass GlassEffect
  | MaterialFrosted FrostedGlass
  | MaterialNoise NoiseOverlay
  | MaterialGrain GrainEffect

derive instance eqMaterialEffect :: Eq MaterialEffect

instance showMaterialEffect :: Show MaterialEffect where
  show (MaterialGlass m) = "(MaterialGlass " <> show m <> ")"
  show (MaterialFrosted m) = "(MaterialFrosted " <> show m <> ")"
  show (MaterialNoise m) = "(MaterialNoise " <> show m <> ")"
  show (MaterialGrain m) = "(MaterialGrain " <> show m <> ")"

-- | Glass effect — transparent with refraction
newtype GlassEffect = GlassEffect
  { tint :: GlowColor        -- Glass tint color
  , opacity :: Number        -- Background visibility (0.0-1.0)
  , refraction :: Number     -- Refraction strength (0.0-1.0)
  , reflection :: Number     -- Reflection amount (0.0-1.0)
  , fresnel :: Boolean       -- Edge reflection enhancement
  }

derive instance eqGlassEffect :: Eq GlassEffect

instance showGlassEffect :: Show GlassEffect where
  show (GlassEffect m) = "(GlassEffect opacity:" <> show m.opacity <> ")"

-- | Frosted glass — blurred background with texture
newtype FrostedGlass = FrostedGlass
  { blur :: Number           -- Background blur amount
  , saturation :: Number     -- Color saturation (0.0-2.0)
  , brightness :: Number     -- Brightness adjustment (0.0-2.0)
  , noiseAmount :: Number    -- Frosted texture noise (0.0-0.1)
  , tint :: GlowColor        -- Optional color tint
  }

derive instance eqFrostedGlass :: Eq FrostedGlass

instance showFrostedGlass :: Show FrostedGlass where
  show (FrostedGlass m) = "(FrostedGlass blur:" <> show m.blur <> ")"

-- | Noise overlay — procedural noise texture
newtype NoiseOverlay = NoiseOverlay
  { noiseType :: NoiseType
  , scale :: Number          -- Noise scale (1.0 = 1:1 pixels)
  , intensity :: Number      -- Noise visibility (0.0-1.0)
  , animated :: Boolean      -- Animate noise
  , speed :: Number          -- Animation speed
  }

derive instance eqNoiseOverlay :: Eq NoiseOverlay

instance showNoiseOverlay :: Show NoiseOverlay where
  show (NoiseOverlay m) = "(NoiseOverlay intensity:" <> show m.intensity <> ")"

-- | Noise types
data NoiseType
  = NoisePerlin
  | NoiseSimplex
  | NoiseWorley
  | NoiseWhite
  | NoiseFBM                 -- Fractal Brownian Motion

derive instance eqNoiseType :: Eq NoiseType

-- | Film grain effect
newtype GrainEffect = GrainEffect
  { amount :: Number         -- Grain intensity (0.0-1.0)
  , size :: Number           -- Grain size (0.5-2.0)
  , colorful :: Boolean      -- Color vs monochrome grain
  , animated :: Boolean      -- Per-frame variation
  }

derive instance eqGrainEffect :: Eq GrainEffect

instance showGrainEffect :: Show GrainEffect where
  show (GrainEffect m) = "(GrainEffect amount:" <> show m.amount <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // temporal effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temporal effect variants
data TemporalEffect
  = TemporalMotionBlur MotionBlur
  | TemporalEcho EchoEffect
  | TemporalTimeWarp TimeWarp

derive instance eqTemporalEffect :: Eq TemporalEffect

instance showTemporalEffect :: Show TemporalEffect where
  show (TemporalMotionBlur t) = "(TemporalMotionBlur " <> show t <> ")"
  show (TemporalEcho t) = "(TemporalEcho " <> show t <> ")"
  show (TemporalTimeWarp t) = "(TemporalTimeWarp " <> show t <> ")"

-- | Motion blur — blur in direction of motion
newtype MotionBlur = MotionBlur
  { samples :: Int           -- Number of temporal samples
  , shutterAngle :: Number   -- Shutter angle in degrees (0-360)
  }

derive instance eqMotionBlur :: Eq MotionBlur

instance showMotionBlur :: Show MotionBlur where
  show (MotionBlur t) = "(MotionBlur samples:" <> show t.samples <> ")"

-- | Echo effect — ghosting/trails
newtype EchoEffect = EchoEffect
  { count :: Int             -- Number of echoes
  , delay :: Number          -- Delay between echoes (frames)
  , decay :: Number          -- Opacity decay per echo (0.0-1.0)
  , operator :: EchoOperator
  }

derive instance eqEchoEffect :: Eq EchoEffect

instance showEchoEffect :: Show EchoEffect where
  show (EchoEffect t) = "(EchoEffect count:" <> show t.count <> ")"

-- | Echo blend operator
data EchoOperator
  = EchoAdd
  | EchoScreen
  | EchoMaximum
  | EchoMinimum
  | EchoBlend

derive instance eqEchoOperator :: Eq EchoOperator

-- | Time warp — time displacement effect
newtype TimeWarp = TimeWarp
  { displacement :: Number   -- Time offset amount
  , noiseScale :: Number     -- Spatial frequency of displacement
  , animated :: Boolean      -- Animate displacement pattern
  }

derive instance eqTimeWarp :: Eq TimeWarp

instance showTimeWarp :: Show TimeWarp where
  show (TimeWarp t) = "(TimeWarp displacement:" <> show t.displacement <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // particle effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle effect variants
data ParticleEffect
  = ParticleFieldEffect ParticleField
  | ParticleEmitterEffect ParticleEmitter

derive instance eqParticleEffect :: Eq ParticleEffect

instance showParticleEffect :: Show ParticleEffect where
  show (ParticleFieldEffect p) = "(ParticleFieldEffect " <> show p <> ")"
  show (ParticleEmitterEffect p) = "(ParticleEmitterEffect " <> show p <> ")"

-- | Particle field — ambient particles in area
newtype ParticleField = ParticleField
  { count :: Int             -- Number of particles
  , sizeMin :: Number        -- Minimum particle size
  , sizeMax :: Number        -- Maximum particle size
  , color :: GlowColor       -- Particle color
  , speedMin :: Number       -- Minimum speed
  , speedMax :: Number       -- Maximum speed
  , direction :: Number      -- Base direction (degrees)
  , spread :: Number         -- Direction spread (degrees)
  , lifetime :: Number       -- Particle lifetime (seconds)
  , fadeIn :: Number         -- Fade in duration (0.0-1.0 of lifetime)
  , fadeOut :: Number        -- Fade out duration (0.0-1.0 of lifetime)
  }

derive instance eqParticleField :: Eq ParticleField

instance showParticleField :: Show ParticleField where
  show (ParticleField p) = "(ParticleField count:" <> show p.count <> ")"

-- | Particle emitter — particles from point
newtype ParticleEmitter = ParticleEmitter
  { positionX :: Number      -- Emitter X position (0.0-1.0)
  , positionY :: Number      -- Emitter Y position (0.0-1.0)
  , rate :: Number           -- Particles per second
  , sizeMin :: Number
  , sizeMax :: Number
  , color :: GlowColor
  , velocity :: Number       -- Initial velocity
  , gravity :: Number        -- Gravity strength
  , spread :: Number         -- Emission cone spread (degrees)
  , lifetime :: Number       -- Particle lifetime (seconds)
  }

derive instance eqParticleEmitter :: Eq ParticleEmitter

instance showParticleEmitter :: Show ParticleEmitter where
  show (ParticleEmitter p) = "(ParticleEmitter rate:" <> show p.rate <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // effect composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sequence effects (apply in order)
effectSequence :: Array RenderEffect -> RenderEffect
effectSequence = EffectSequence

-- | Parallel effects (apply simultaneously)
effectParallel :: Array RenderEffect -> RenderEffect
effectParallel = EffectParallel

-- | Conditional effect
effectConditional :: EffectCondition -> RenderEffect -> Maybe RenderEffect -> RenderEffect
effectConditional condition thenEffect elseEffect = EffectConditional
  { condition, thenEffect, elseEffect }

-- | Conditional effect with no else branch
effectWhen :: EffectCondition -> RenderEffect -> RenderEffect
effectWhen condition thenEffect = EffectConditional
  { condition, thenEffect, elseEffect: Nothing }

-- | Conditional effect with both branches
effectIfThenElse :: EffectCondition -> RenderEffect -> RenderEffect -> RenderEffect
effectIfThenElse condition thenEffect elseEffect = EffectConditional
  { condition, thenEffect, elseEffect: Just elseEffect }

-- | Animated effect (interpolate between states)
effectAnimated :: RenderEffect -> RenderEffect -> Number -> RenderEffect
effectAnimated from to progress = EffectAnimated { from, to, progress }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // effect constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- Blur constructors
gaussianBlur :: Number -> RenderEffect
gaussianBlur radius = EffectBlur (BlurGaussian (GaussianBlur
  { radius, quality: BlurQualityMedium }))

directionalBlur :: Number -> Number -> RenderEffect
directionalBlur angle distance = EffectBlur (BlurDirectional (DirectionalBlur
  { angle, distance, quality: BlurQualityMedium }))

radialBlur :: Number -> Number -> Number -> RenderEffect
radialBlur centerX centerY amount = EffectBlur (BlurRadial (RadialBlur
  { centerX, centerY, amount, blurType: RadialTypeSpin }))

zoomBlur :: Number -> Number -> Number -> RenderEffect
zoomBlur centerX centerY strength = EffectBlur (BlurZoom (ZoomBlur
  { centerX, centerY, strength }))

-- Glow constructors
innerGlow :: GlowColor -> Number -> Number -> RenderEffect
innerGlow color radius intensity = EffectGlow (GlowInner (InnerGlow
  { color, radius, intensity, choke: 0.0 }))

outerGlow :: GlowColor -> Number -> Number -> RenderEffect
outerGlow color radius intensity = EffectGlow (GlowOuter (OuterGlow
  { color, radius, intensity, spread: 0.0 }))

pulsingGlow :: GlowColor -> Number -> Number -> Number -> RenderEffect
pulsingGlow color minRadius maxRadius periodMs = EffectGlow (GlowPulsing (PulsingGlow
  { color, minRadius, maxRadius, minIntensity: 0.3, maxIntensity: 1.0
  , periodMs, easing: GlowEaseSine }))

neonGlow :: GlowColor -> GlowColor -> Number -> RenderEffect
neonGlow coreColor outerColor intensity = EffectGlow (GlowNeon (NeonGlow
  { coreColor, outerColor, coreRadius: 2.0, outerRadius: 16.0
  , intensity, flicker: false, flickerSpeed: 0.0 }))

-- Shadow constructors
dropShadowEffect :: Number -> Number -> Number -> GlowColor -> RenderEffect
dropShadowEffect offsetX offsetY blur color = EffectShadow (ShadowDrop (DropShadowEffect
  { offsetX, offsetY, blur, color }))

boxShadowEffect :: Number -> Number -> Number -> Number -> GlowColor -> RenderEffect
boxShadowEffect offsetX offsetY blur spread color = EffectShadow (ShadowBox (BoxShadowEffect
  { offsetX, offsetY, blur, spread, color, inset: false }))

contactShadow :: Number -> Number -> RenderEffect
contactShadow blur opacity = EffectShadow (ShadowContact (ContactShadow
  { blur, opacity, offsetY: 2.0, scale: 0.9 }))

-- Border constructors
gradientBorder :: Number -> Array GlowColor -> Number -> RenderEffect
gradientBorder width colors angle = EffectBorder (BorderGradient (GradientBorder
  { width, gradientType: BorderGradientLinear, colors, angle }))

conicBorder :: Number -> Array GlowColor -> Number -> RenderEffect
conicBorder width colors rotationSpeed = EffectBorder (BorderConic (ConicBorder
  { width, colors, rotationSpeed, blurRadius: 8.0, mouseTracking: false, spotlightAngle: 90.0 }))

animatedDashBorder :: Number -> Number -> Number -> Number -> GlowColor -> RenderEffect
animatedDashBorder width dashLength gapLength speed color = EffectBorder (BorderAnimatedDash (AnimatedDashBorder
  { width, dashLength, gapLength, speed, direction: DashDirectionForward, color }))

glowingBorder :: Number -> GlowColor -> GlowColor -> Number -> RenderEffect
glowingBorder width borderColor glowColor glowRadius = EffectBorder (BorderGlowing (GlowingBorder
  { width, borderColor, glowColor, glowRadius, glowIntensity: 0.5, animated: false, pulseSpeed: 0.0 }))

-- Material constructors
glassEffect :: GlowColor -> Number -> RenderEffect
glassEffect tint opacity = EffectMaterial (MaterialGlass (GlassEffect
  { tint, opacity, refraction: 0.1, reflection: 0.1, fresnel: true }))

frostedGlass :: Number -> Number -> RenderEffect
frostedGlass blur noiseAmount = EffectMaterial (MaterialFrosted (FrostedGlass
  { blur, saturation: 1.0, brightness: 1.0, noiseAmount
  , tint: { r: 255, g: 255, b: 255, a: 0.0 } }))

noiseOverlay :: NoiseType -> Number -> Number -> RenderEffect
noiseOverlay noiseType scale intensity = EffectMaterial (MaterialNoise (NoiseOverlay
  { noiseType, scale, intensity, animated: false, speed: 0.0 }))

grainEffect :: Number -> Number -> RenderEffect
grainEffect amount size = EffectMaterial (MaterialGrain (GrainEffect
  { amount, size, colorful: false, animated: true }))

-- Temporal constructors
motionBlur :: Int -> Number -> RenderEffect
motionBlur samples shutterAngle = EffectTemporal (TemporalMotionBlur (MotionBlur
  { samples, shutterAngle }))

echoEffect :: Int -> Number -> Number -> RenderEffect
echoEffect count delay decay = EffectTemporal (TemporalEcho (EchoEffect
  { count, delay, decay, operator: EchoBlend }))

timeWarp :: Number -> Number -> RenderEffect
timeWarp displacement noiseScale = EffectTemporal (TemporalTimeWarp (TimeWarp
  { displacement, noiseScale, animated: true }))

-- Particle constructors
particleField :: Int -> GlowColor -> RenderEffect
particleField count color = EffectParticle (ParticleFieldEffect (ParticleField
  { count, sizeMin: 1.0, sizeMax: 3.0, color, speedMin: 10.0, speedMax: 30.0
  , direction: 0.0, spread: 360.0, lifetime: 5.0, fadeIn: 0.1, fadeOut: 0.2 }))

particleEmitter :: Number -> Number -> Number -> GlowColor -> RenderEffect
particleEmitter positionX positionY rate color = EffectParticle (ParticleEmitterEffect (ParticleEmitter
  { positionX, positionY, rate, sizeMin: 2.0, sizeMax: 4.0, color
  , velocity: 100.0, gravity: 50.0, spread: 45.0, lifetime: 2.0 }))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Preset: subtle blur (8px)
subtleBlur :: RenderEffect
subtleBlur = gaussianBlur 8.0

-- | Preset: heavy blur (32px)
heavyBlur :: RenderEffect
heavyBlur = gaussianBlur 32.0

-- | Preset: soft glow (subtle outer glow)
softGlow :: RenderEffect
softGlow = outerGlow { r: 59, g: 130, b: 246, a: 0.5 } 12.0 0.4

-- | Preset: intense glow (vibrant pulsing)
intenseGlow :: RenderEffect
intenseGlow = pulsingGlow { r: 34, g: 211, b: 238, a: 0.8 } 8.0 24.0 1500.0

-- | Preset: elevated shadow (Material Design elevation 8)
elevatedShadow :: RenderEffect
elevatedShadow = effectSequence
  [ boxShadowEffect 0.0 1.0 3.0 0.0 { r: 0, g: 0, b: 0, a: 0.1 }
  , boxShadowEffect 0.0 4.0 6.0 (-1.0) { r: 0, g: 0, b: 0, a: 0.1 }
  ]

-- | Preset: floating shadow (high elevation)
floatingShadow :: RenderEffect
floatingShadow = effectSequence
  [ boxShadowEffect 0.0 4.0 6.0 (-1.0) { r: 0, g: 0, b: 0, a: 0.1 }
  , boxShadowEffect 0.0 10.0 15.0 (-3.0) { r: 0, g: 0, b: 0, a: 0.1 }
  , boxShadowEffect 0.0 20.0 25.0 (-5.0) { r: 0, g: 0, b: 0, a: 0.1 }
  ]

-- | Preset: Linear-style rotating border
linearBorder :: RenderEffect
linearBorder = conicBorder 1.0
  [ { r: 59, g: 130, b: 246, a: 1.0 }    -- Blue
  , { r: 139, g: 92, b: 246, a: 1.0 }    -- Purple
  , { r: 236, g: 72, b: 153, a: 1.0 }    -- Pink
  , { r: 59, g: 130, b: 246, a: 1.0 }    -- Blue (loop)
  ]
  45.0  -- 45 degrees per second

-- | Preset: mouse-tracking spotlight border
spotlightBorder :: RenderEffect
spotlightBorder = EffectBorder (BorderConic (ConicBorder
  { width: 1.0
  , colors: [ { r: 255, g: 255, b: 255, a: 1.0 }
            , { r: 255, g: 255, b: 255, a: 0.0 }
            , { r: 255, g: 255, b: 255, a: 0.0 }
            ]
  , rotationSpeed: 0.0
  , blurRadius: 12.0
  , mouseTracking: true
  , spotlightAngle: 60.0
  }))

-- | Preset: liquid glass (iOS style)
liquidGlass :: RenderEffect
liquidGlass = effectSequence
  [ frostedGlass 20.0 0.02
  , glassEffect { r: 255, g: 255, b: 255, a: 0.1 } 0.8
  ]

-- | Preset: acrylic glass (Windows style)
acrylicGlass :: RenderEffect
acrylicGlass = effectSequence
  [ frostedGlass 30.0 0.03
  , noiseOverlay NoiseWhite 1.0 0.02
  , glassEffect { r: 245, g: 245, b: 245, a: 0.05 } 0.85
  ]

-- | Preset: film grain (cinematic)
filmGrain :: RenderEffect
filmGrain = grainEffect 0.1 1.0

-- | Preset: digital noise (glitch aesthetic)
digitalNoise :: RenderEffect
digitalNoise = effectSequence
  [ noiseOverlay NoiseWhite 2.0 0.05
  , grainEffect 0.15 0.8
  ]

-- | Preset: fast background blur (uses low quality for performance)
backgroundBlur :: RenderEffect
backgroundBlur = EffectBlur (BlurGaussian (GaussianBlur
  { radius: 32.0
  , quality: BlurQualityLow  -- Fast, acceptable for large backgrounds
  }))

-- | Preset: high quality hero blur (uses high quality for detail)
heroBlur :: RenderEffect
heroBlur = EffectBlur (BlurGaussian (GaussianBlur
  { radius: 8.0
  , quality: BlurQualityHigh  -- Best quality for hero elements
  }))

-- | Preset: zoom blur from center (uses RadialTypeZoom)
centeredZoomBlur :: Number -> RenderEffect
centeredZoomBlur amount = EffectBlur (BlurRadial (RadialBlur
  { centerX: 0.5
  , centerY: 0.5
  , amount: amount
  , blurType: RadialTypeZoom
  }))
