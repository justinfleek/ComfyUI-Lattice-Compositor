-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // carousel // effects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Effects — Visual effects applied to slides based on position.
-- |
-- | ## Design Philosophy
-- |
-- | Effects are pure functions: SlidePosition -> CSS properties.
-- | Each effect can be independently enabled/disabled via toggles.
-- | Effects compose — multiple can be active simultaneously.
-- |
-- | ## Effect Categories
-- |
-- | **Opacity Effects**: Fade inactive slides
-- | **Transform Effects**: Scale, rotate, translate, skew
-- | **Filter Effects**: Blur, grayscale, saturate, brightness
-- | **Material Effects**: Reflections, shadows, glow
-- | **3D Effects**: Perspective, depth, parallax layers
-- |
-- | ## Dependencies
-- |
-- | - Carousel.Types (SlidePosition)
-- | - Schema atoms (Color, Dimension, etc.)

module Hydrogen.Element.Compound.Carousel.Effects
  ( -- * Effect Kind
    EffectKind
      ( EffectOpacity
      , EffectScale
      , EffectBlur
      , EffectRotation
      , EffectReflection
      , EffectParallax
      , EffectGrayscale
      , EffectGlow
      , EffectShadow
      , EffectBrightness
      , EffectContrast
      , EffectHueShift
      )
  
  -- * Effect Toggle
  , EffectToggle
  , effectToggle
  , isEffectEnabled
  , enableEffect
  , disableEffect
  
  -- * Opacity Effect
  , OpacityEffect
  , opacityEffect
  , defaultOpacityEffect
  , activeOpacity
  , inactiveOpacity
  
  -- * Scale Effect
  , ScaleEffect
  , scaleEffect
  , defaultScaleEffect
  , activeScale
  , inactiveScale
  
  -- * Blur Effect
  , BlurEffect
  , blurEffect
  , defaultBlurEffect
  , activeBlur
  , inactiveBlur
  
  -- * Rotation Effect
  , RotationEffect
  , rotationEffect
  , defaultRotationEffect
  
  -- * Reflection Effect
  , ReflectionEffect
  , reflectionEffect
  , defaultReflectionEffect
  
  -- * Parallax Effect
  , ParallaxEffect
  , ParallaxDirection
      ( ParallaxHorizontal
      , ParallaxVertical
      , ParallaxBoth
      )
  , parallaxEffect
  , defaultParallaxEffect
  
  -- * Grayscale Effect
  , GrayscaleEffect
  , grayscaleEffect
  , defaultGrayscaleEffect
  
  -- * Glow Effect
  , GlowEffect
  , glowEffect
  , defaultGlowEffect
  
  -- * Combined Effects
  , SlideEffects
  , defaultEffects
  , noEffects
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Bounded
  , negate
  , max
  , min
  )

import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device as Device

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // effect kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enumeration of all available effect types
-- |
-- | Used for toggling individual effects on/off.
data EffectKind
  = EffectOpacity       -- ^ Fade inactive slides
  | EffectScale         -- ^ Scale transform
  | EffectBlur          -- ^ Gaussian blur filter
  | EffectRotation      -- ^ 3D rotation
  | EffectReflection    -- ^ Mirror reflection below
  | EffectParallax      -- ^ Multi-layer parallax
  | EffectGrayscale     -- ^ Desaturate inactive
  | EffectGlow          -- ^ Outer glow on active
  | EffectShadow        -- ^ Drop shadow
  | EffectBrightness    -- ^ Brightness adjustment
  | EffectContrast      -- ^ Contrast adjustment
  | EffectHueShift      -- ^ Hue rotation

derive instance eqEffectKind :: Eq EffectKind
derive instance ordEffectKind :: Ord EffectKind

instance showEffectKind :: Show EffectKind where
  show EffectOpacity = "opacity"
  show EffectScale = "scale"
  show EffectBlur = "blur"
  show EffectRotation = "rotation"
  show EffectReflection = "reflection"
  show EffectParallax = "parallax"
  show EffectGrayscale = "grayscale"
  show EffectGlow = "glow"
  show EffectShadow = "shadow"
  show EffectBrightness = "brightness"
  show EffectContrast = "contrast"
  show EffectHueShift = "hue-shift"

instance boundedEffectKind :: Bounded EffectKind where
  top = EffectHueShift
  bottom = EffectOpacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // effect toggle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toggle state for an effect
-- |
-- | Wraps Boolean but provides semantic API.
newtype EffectToggle = EffectToggle Boolean

derive instance eqEffectToggle :: Eq EffectToggle

instance showEffectToggle :: Show EffectToggle where
  show (EffectToggle true) = "enabled"
  show (EffectToggle false) = "disabled"

-- | Create effect toggle
effectToggle :: Boolean -> EffectToggle
effectToggle = EffectToggle

-- | Check if effect is enabled
isEffectEnabled :: EffectToggle -> Boolean
isEffectEnabled (EffectToggle b) = b

-- | Enable an effect
enableEffect :: EffectToggle
enableEffect = EffectToggle true

-- | Disable an effect
disableEffect :: EffectToggle
disableEffect = EffectToggle false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // opacity effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opacity effect configuration
-- |
-- | Fades inactive slides to draw attention to active.
type OpacityEffect =
  { enabled :: EffectToggle
  , active :: Number      -- ^ Opacity for active slide (0.0-1.0)
  , inactive :: Number    -- ^ Opacity for inactive slides (0.0-1.0)
  , nearbyFalloff :: Number -- ^ Multiplier per position from active
  }

-- | Create opacity effect
opacityEffect :: Number -> Number -> Number -> OpacityEffect
opacityEffect active inactive falloff =
  { enabled: enableEffect
  , active: clampOpacity active
  , inactive: clampOpacity inactive
  , nearbyFalloff: max 0.0 (min 1.0 falloff)
  }

-- | Default opacity effect (active=1.0, inactive=0.5)
defaultOpacityEffect :: OpacityEffect
defaultOpacityEffect = opacityEffect 1.0 0.5 0.8

-- | Get opacity for active slide
activeOpacity :: OpacityEffect -> Number
activeOpacity e = e.active

-- | Get opacity for inactive slides
inactiveOpacity :: OpacityEffect -> Number
inactiveOpacity e = e.inactive

-- | Clamp opacity to valid range
clampOpacity :: Number -> Number
clampOpacity n = max 0.0 (min 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // scale effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale transform effect configuration
-- |
-- | Scales active slide larger, inactive smaller.
type ScaleEffect =
  { enabled :: EffectToggle
  , active :: Number      -- ^ Scale for active slide (1.0 = normal)
  , inactive :: Number    -- ^ Scale for inactive slides
  , nearbyFalloff :: Number -- ^ Scale reduction per position
  }

-- | Create scale effect
scaleEffect :: Number -> Number -> Number -> ScaleEffect
scaleEffect active inactive falloff =
  { enabled: enableEffect
  , active: clampScale active
  , inactive: clampScale inactive
  , nearbyFalloff: max 0.0 (min 1.0 falloff)
  }

-- | Default scale effect (active=1.0, inactive=0.85)
defaultScaleEffect :: ScaleEffect
defaultScaleEffect = scaleEffect 1.0 0.85 0.9

-- | Get scale for active slide
activeScale :: ScaleEffect -> Number
activeScale e = e.active

-- | Get scale for inactive slides
inactiveScale :: ScaleEffect -> Number
inactiveScale e = e.inactive

-- | Clamp scale to reasonable range (0.1 to 3.0)
clampScale :: Number -> Number
clampScale n = max 0.1 (min 3.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // blur effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blur filter effect configuration
-- |
-- | Blurs inactive slides to focus attention.
type BlurEffect =
  { enabled :: EffectToggle
  , active :: Device.Pixel    -- ^ Blur radius for active (usually 0)
  , inactive :: Device.Pixel  -- ^ Blur radius for inactive
  , nearbyFalloff :: Number   -- ^ Blur increase per position
  }

-- | Create blur effect
blurEffect :: Device.Pixel -> Device.Pixel -> Number -> BlurEffect
blurEffect active inactive falloff =
  { enabled: enableEffect
  , active: active
  , inactive: inactive
  , nearbyFalloff: max 0.0 (min 2.0 falloff)
  }

-- | Default blur effect (active=0px, inactive=4px)
defaultBlurEffect :: BlurEffect
defaultBlurEffect = blurEffect (Device.px 0.0) (Device.px 4.0) 1.5

-- | Get blur for active slide
activeBlur :: BlurEffect -> Device.Pixel
activeBlur e = e.active

-- | Get blur for inactive slides
inactiveBlur :: BlurEffect -> Device.Pixel
inactiveBlur e = e.inactive

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // rotation effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D rotation effect configuration
-- |
-- | Rotates slides in 3D space based on position.
type RotationEffect =
  { enabled :: EffectToggle
  , rotateY :: Number       -- ^ Y-axis rotation per position (degrees)
  , rotateX :: Number       -- ^ X-axis rotation per position (degrees)
  , rotateZ :: Number       -- ^ Z-axis rotation per position (degrees)
  , perspective :: Device.Pixel -- ^ Perspective depth
  }

-- | Create rotation effect
rotationEffect :: Number -> Number -> Number -> Device.Pixel -> RotationEffect
rotationEffect ry rx rz perspective =
  { enabled: enableEffect
  , rotateY: clampRotation ry
  , rotateX: clampRotation rx
  , rotateZ: clampRotation rz
  , perspective: perspective
  }

-- | Default rotation effect (subtle Y rotation for coverflow)
defaultRotationEffect :: RotationEffect
defaultRotationEffect = rotationEffect 45.0 0.0 0.0 (Device.px 1000.0)

-- | Clamp rotation to -180 to 180 degrees
clampRotation :: Number -> Number
clampRotation n = max (-180.0) (min 180.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // reflection effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reflection effect configuration
-- |
-- | Renders a fading mirror reflection below the slide.
type ReflectionEffect =
  { enabled :: EffectToggle
  , height :: Number          -- ^ Reflection height as fraction of slide (0.0-1.0)
  , opacity :: Number         -- ^ Starting opacity of reflection (0.0-1.0)
  , gap :: Device.Pixel       -- ^ Gap between slide and reflection
  }

-- | Create reflection effect
reflectionEffect :: Number -> Number -> Device.Pixel -> ReflectionEffect
reflectionEffect height opacity gap =
  { enabled: enableEffect
  , height: max 0.0 (min 1.0 height)
  , opacity: clampOpacity opacity
  , gap: gap
  }

-- | Default reflection effect
defaultReflectionEffect :: ReflectionEffect
defaultReflectionEffect = reflectionEffect 0.3 0.3 (Device.px 4.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // parallax effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parallax effect configuration
-- |
-- | Multiple layers move at different speeds during transitions.
type ParallaxEffect =
  { enabled :: EffectToggle
  , layers :: Int             -- ^ Number of parallax layers (1-5)
  , speedRatio :: Number      -- ^ Speed difference between layers (0.1-0.9)
  , direction :: ParallaxDirection
  }

-- | Parallax movement direction
data ParallaxDirection
  = ParallaxHorizontal
  | ParallaxVertical
  | ParallaxBoth

derive instance eqParallaxDirection :: Eq ParallaxDirection

instance showParallaxDirection :: Show ParallaxDirection where
  show ParallaxHorizontal = "horizontal"
  show ParallaxVertical = "vertical"
  show ParallaxBoth = "both"

-- | Create parallax effect
parallaxEffect :: Int -> Number -> ParallaxDirection -> ParallaxEffect
parallaxEffect layers speedRatio direction =
  { enabled: enableEffect
  , layers: max 1 (min 5 layers)
  , speedRatio: max 0.1 (min 0.9 speedRatio)
  , direction: direction
  }

-- | Default parallax effect (3 layers, horizontal)
defaultParallaxEffect :: ParallaxEffect
defaultParallaxEffect = parallaxEffect 3 0.5 ParallaxHorizontal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // grayscale effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grayscale/desaturation effect configuration
-- |
-- | Desaturates inactive slides to highlight active.
type GrayscaleEffect =
  { enabled :: EffectToggle
  , active :: Number      -- ^ Grayscale amount for active (0.0 = full color)
  , inactive :: Number    -- ^ Grayscale amount for inactive (1.0 = full gray)
  }

-- | Create grayscale effect
grayscaleEffect :: Number -> Number -> GrayscaleEffect
grayscaleEffect active inactive =
  { enabled: enableEffect
  , active: clampOpacity active
  , inactive: clampOpacity inactive
  }

-- | Default grayscale effect (active=0%, inactive=80%)
defaultGrayscaleEffect :: GrayscaleEffect
defaultGrayscaleEffect = grayscaleEffect 0.0 0.8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // glow effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow effect configuration
-- |
-- | Adds outer glow to active slide.
type GlowEffect =
  { enabled :: EffectToggle
  , color :: Color.RGB        -- ^ Glow color
  , radius :: Device.Pixel    -- ^ Glow blur radius
  , spread :: Device.Pixel    -- ^ Glow spread
  , opacity :: Number         -- ^ Glow opacity (0.0-1.0)
  }

-- | Create glow effect
glowEffect :: Color.RGB -> Device.Pixel -> Device.Pixel -> Number -> GlowEffect
glowEffect color radius spread opacity =
  { enabled: enableEffect
  , color: color
  , radius: radius
  , spread: spread
  , opacity: clampOpacity opacity
  }

-- | Default glow effect (blue glow)
defaultGlowEffect :: GlowEffect
defaultGlowEffect = glowEffect 
  (Color.rgb 59 130 246) 
  (Device.px 20.0) 
  (Device.px 0.0) 
  0.6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // combined effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined slide effects configuration
-- |
-- | All effects that can be applied to slides. Each independently toggleable.
type SlideEffects =
  { opacity :: OpacityEffect
  , scale :: ScaleEffect
  , blur :: BlurEffect
  , rotation :: RotationEffect
  , reflection :: ReflectionEffect
  , parallax :: ParallaxEffect
  , grayscale :: GrayscaleEffect
  , glow :: GlowEffect
  }

-- | Default effects (opacity and scale enabled)
defaultEffects :: SlideEffects
defaultEffects =
  { opacity: defaultOpacityEffect
  , scale: defaultScaleEffect
  , blur: defaultBlurEffect { enabled = disableEffect }
  , rotation: defaultRotationEffect { enabled = disableEffect }
  , reflection: defaultReflectionEffect { enabled = disableEffect }
  , parallax: defaultParallaxEffect { enabled = disableEffect }
  , grayscale: defaultGrayscaleEffect { enabled = disableEffect }
  , glow: defaultGlowEffect { enabled = disableEffect }
  }

-- | No effects (all disabled)
noEffects :: SlideEffects
noEffects =
  { opacity: defaultOpacityEffect { enabled = disableEffect }
  , scale: defaultScaleEffect { enabled = disableEffect }
  , blur: defaultBlurEffect { enabled = disableEffect }
  , rotation: defaultRotationEffect { enabled = disableEffect }
  , reflection: defaultReflectionEffect { enabled = disableEffect }
  , parallax: defaultParallaxEffect { enabled = disableEffect }
  , grayscale: defaultGrayscaleEffect { enabled = disableEffect }
  , glow: defaultGlowEffect { enabled = disableEffect }
  }
