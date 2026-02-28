-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // material // glass-effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GlassEffect — Glassmorphism and translucent material effects.
-- |
-- | ## Research Findings
-- |
-- | **Apple's Liquid Glass (iOS/visionOS)**:
-- | - Fresnel effect for depth (edges more opaque than center)
-- | - Variable blur based on content behind
-- | - Mandatory noise (2-3% opacity) to prevent color banding
-- | - 1px internal border with gradient for depth perception
-- | - Multiple blur layers at different radii
-- |
-- | **Web Glassmorphism Best Practices**:
-- | - backdrop-filter: blur() for background blur
-- | - Semi-transparent background (rgba with 0.1-0.3 alpha)
-- | - Subtle border (1px white at 10-20% opacity)
-- | - Box shadow for elevation
-- |
-- | ## Performance Considerations
-- |
-- | Backdrop blur is expensive. The runtime may:
-- | - Skip blur on low-powered devices
-- | - Use cached/static blur for complex backgrounds
-- | - Reduce blur radius on mobile
-- |
-- | ## Dependencies
-- |
-- | - Schema.Material.BlurRadius (blur amount)
-- | - Schema.Color.Opacity (transparency)

module Hydrogen.Schema.Material.GlassEffect
  ( -- * Glass Type
    GlassType(..)
  
  -- * Fresnel Effect
  , FresnelConfig(..)
  , fresnelConfig
  , defaultFresnel
  , noFresnel
  
  -- * Noise Texture
  , NoiseConfig(..)
  , noiseConfig
  , defaultNoise
  , noNoise
  
  -- * Internal Border
  , InternalBorder(..)
  , internalBorder
  , defaultInternalBorder
  , noInternalBorder
  
  -- * Glass Effect
  , GlassEffect(..)
  , glassEffect
  , frostedGlass
  , liquidGlass
  , subtleGlass
  , darkGlass
  , acrylicGlass
  , noGlass
  
  -- * Presets by Platform
  , appleGlass
  , windowsAcrylic
  , materialYou
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // glass type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of glass material
data GlassType
  = FrostedGlass    -- ^ Classic iOS/macOS frosted glass
  | LiquidGlass     -- ^ Apple visionOS liquid glass with depth
  | AcrylicGlass    -- ^ Windows Fluent Design acrylic
  | MicaGlass       -- ^ Windows 11 Mica (tinted by wallpaper)
  | MaterialGlass   -- ^ Material You dynamic theming
  | CustomGlass     -- ^ Custom configuration

derive instance eqGlassType :: Eq GlassType

instance showGlassType :: Show GlassType where
  show FrostedGlass = "frosted"
  show LiquidGlass = "liquid"
  show AcrylicGlass = "acrylic"
  show MicaGlass = "mica"
  show MaterialGlass = "material"
  show CustomGlass = "custom"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // fresnel effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fresnel effect configuration
-- |
-- | Creates depth by varying opacity based on viewing angle.
-- | In 2D, this is approximated with a radial gradient from center to edges.
-- |
-- | - **centerOpacity**: Opacity at the center of the element
-- | - **edgeOpacity**: Opacity at the edges
-- | - **exponent**: Controls falloff curve (higher = sharper transition)
newtype FresnelConfig = FresnelConfig
  { enabled :: Boolean
  , centerOpacity :: Number    -- ^ 0.0-1.0
  , edgeOpacity :: Number      -- ^ 0.0-1.0
  , exponent :: Number         -- ^ Fresnel exponent (1.0-5.0 typical)
  }

derive instance eqFresnelConfig :: Eq FresnelConfig

instance showFresnelConfig :: Show FresnelConfig where
  show (FresnelConfig f) = 
    if f.enabled 
      then "Fresnel(center:" <> show f.centerOpacity <> ", edge:" <> show f.edgeOpacity <> ")"
      else "Fresnel(disabled)"

-- | Create fresnel config
fresnelConfig :: Number -> Number -> Number -> FresnelConfig
fresnelConfig centerOpacity edgeOpacity exponent = FresnelConfig
  { enabled: true
  , centerOpacity
  , edgeOpacity
  , exponent
  }

-- | Default fresnel effect (Apple Liquid Glass style)
-- |
-- | Research finding: edges should be 2-3x more opaque than center
defaultFresnel :: FresnelConfig
defaultFresnel = FresnelConfig
  { enabled: true
  , centerOpacity: 0.1
  , edgeOpacity: 0.3
  , exponent: 2.0
  }

-- | No fresnel effect (uniform opacity)
noFresnel :: FresnelConfig
noFresnel = FresnelConfig
  { enabled: false
  , centerOpacity: 0.0
  , edgeOpacity: 0.0
  , exponent: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // noise texture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Noise texture configuration
-- |
-- | Adds subtle noise to prevent color banding in gradients and
-- | semi-transparent areas.
-- |
-- | ## Research Finding
-- |
-- | Apple recommends 2-3% noise opacity for all glass effects.
-- | This is imperceptible but prevents the "posterization" effect
-- | that occurs with smooth gradients on 8-bit displays.
newtype NoiseConfig = NoiseConfig
  { enabled :: Boolean
  , opacity :: Number         -- ^ Noise opacity (0.02-0.05 recommended)
  , scale :: Number           -- ^ Noise scale (pixels per noise cell)
  , animated :: Boolean       -- ^ Subtle animation to prevent static patterns
  }

derive instance eqNoiseConfig :: Eq NoiseConfig

instance showNoiseConfig :: Show NoiseConfig where
  show (NoiseConfig n) = 
    if n.enabled 
      then "Noise(" <> show n.opacity <> ")"
      else "Noise(disabled)"

-- | Create noise config
noiseConfig :: Number -> Number -> NoiseConfig
noiseConfig opacity scale = NoiseConfig
  { enabled: true
  , opacity
  , scale
  , animated: false
  }

-- | Default noise (2% opacity, per Apple research)
defaultNoise :: NoiseConfig
defaultNoise = NoiseConfig
  { enabled: true
  , opacity: 0.02
  , scale: 1.0
  , animated: false
  }

-- | No noise texture
noNoise :: NoiseConfig
noNoise = NoiseConfig
  { enabled: false
  , opacity: 0.0
  , scale: 1.0
  , animated: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // internal border
-- ═════════════════════════════════════════════════════════════════════════════

-- | Internal border for glass depth
-- |
-- | A subtle inner border creates the perception of a glass edge.
-- | Apple uses a 1px border with a gradient from white (top-left) 
-- | to transparent (bottom-right).
newtype InternalBorder = InternalBorder
  { enabled :: Boolean
  , width :: Number           -- ^ Border width in pixels (typically 1)
  , topLeftColor :: String    -- ^ Color at top-left (usually white at ~20%)
  , bottomRightColor :: String -- ^ Color at bottom-right (usually transparent)
  , opacity :: Number         -- ^ Overall border opacity
  }

derive instance eqInternalBorder :: Eq InternalBorder

instance showInternalBorder :: Show InternalBorder where
  show (InternalBorder b) = 
    if b.enabled 
      then "InternalBorder(" <> show b.width <> "px)"
      else "InternalBorder(disabled)"

-- | Create internal border
internalBorder :: Number -> String -> String -> Number -> InternalBorder
internalBorder width topLeftColor bottomRightColor opacity = InternalBorder
  { enabled: true
  , width
  , topLeftColor
  , bottomRightColor
  , opacity
  }

-- | Default internal border (Apple Liquid Glass style)
defaultInternalBorder :: InternalBorder
defaultInternalBorder = InternalBorder
  { enabled: true
  , width: 1.0
  , topLeftColor: "rgba(255,255,255,0.3)"
  , bottomRightColor: "rgba(255,255,255,0.05)"
  , opacity: 1.0
  }

-- | No internal border
noInternalBorder :: InternalBorder
noInternalBorder = InternalBorder
  { enabled: false
  , width: 0.0
  , topLeftColor: "transparent"
  , bottomRightColor: "transparent"
  , opacity: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // glass effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete glass effect configuration
-- |
-- | Combines all glass properties into a single composable type.
newtype GlassEffect = GlassEffect
  { glassType :: GlassType
  , blurRadius :: Number           -- ^ Background blur in pixels
  , tintColor :: String            -- ^ Tint color overlay (hex or rgba)
  , tintOpacity :: Number          -- ^ Tint opacity (0.0-1.0)
  , saturation :: Number           -- ^ Background saturation (1.0 = normal)
  , brightness :: Number           -- ^ Background brightness (1.0 = normal)
  , fresnel :: FresnelConfig       -- ^ Edge opacity variation
  , noise :: NoiseConfig           -- ^ Anti-banding noise
  , border :: InternalBorder       -- ^ Inner border for depth
  , shadowColor :: String          -- ^ Outer shadow color
  , shadowBlur :: Number           -- ^ Outer shadow blur
  , shadowOffsetY :: Number        -- ^ Shadow vertical offset
  }

derive instance eqGlassEffect :: Eq GlassEffect

instance showGlassEffect :: Show GlassEffect where
  show (GlassEffect g) = 
    "GlassEffect(" <> show g.glassType <> ", blur:" <> show g.blurRadius <> "px)"

-- | Create custom glass effect
glassEffect 
  :: { blurRadius :: Number
     , tintColor :: String
     , tintOpacity :: Number
     }
  -> GlassEffect
glassEffect cfg = GlassEffect
  { glassType: CustomGlass
  , blurRadius: cfg.blurRadius
  , tintColor: cfg.tintColor
  , tintOpacity: cfg.tintOpacity
  , saturation: 1.0
  , brightness: 1.0
  , fresnel: noFresnel
  , noise: defaultNoise
  , border: noInternalBorder
  , shadowColor: "rgba(0,0,0,0.1)"
  , shadowBlur: 10.0
  , shadowOffsetY: 2.0
  }

-- | Classic frosted glass (iOS-style)
frostedGlass :: GlassEffect
frostedGlass = GlassEffect
  { glassType: FrostedGlass
  , blurRadius: 20.0
  , tintColor: "rgba(255,255,255,0.7)"
  , tintOpacity: 0.7
  , saturation: 1.8
  , brightness: 1.0
  , fresnel: noFresnel
  , noise: defaultNoise
  , border: defaultInternalBorder
  , shadowColor: "rgba(0,0,0,0.1)"
  , shadowBlur: 10.0
  , shadowOffsetY: 2.0
  }

-- | Apple Liquid Glass (visionOS-style)
-- |
-- | Full implementation with fresnel, noise, and internal borders
liquidGlass :: GlassEffect
liquidGlass = GlassEffect
  { glassType: LiquidGlass
  , blurRadius: 30.0
  , tintColor: "rgba(255,255,255,0.1)"
  , tintOpacity: 0.1
  , saturation: 1.2
  , brightness: 1.05
  , fresnel: defaultFresnel
  , noise: defaultNoise
  , border: defaultInternalBorder
  , shadowColor: "rgba(0,0,0,0.15)"
  , shadowBlur: 20.0
  , shadowOffsetY: 4.0
  }

-- | Subtle glass (minimal effect, performant)
subtleGlass :: GlassEffect
subtleGlass = GlassEffect
  { glassType: CustomGlass
  , blurRadius: 8.0
  , tintColor: "rgba(255,255,255,0.5)"
  , tintOpacity: 0.5
  , saturation: 1.0
  , brightness: 1.0
  , fresnel: noFresnel
  , noise: noNoise
  , border: noInternalBorder
  , shadowColor: "rgba(0,0,0,0.05)"
  , shadowBlur: 4.0
  , shadowOffsetY: 1.0
  }

-- | Dark glass (for dark mode)
darkGlass :: GlassEffect
darkGlass = GlassEffect
  { glassType: CustomGlass
  , blurRadius: 20.0
  , tintColor: "rgba(0,0,0,0.6)"
  , tintOpacity: 0.6
  , saturation: 1.0
  , brightness: 0.8
  , fresnel: noFresnel
  , noise: defaultNoise
  , border: InternalBorder
      { enabled: true
      , width: 1.0
      , topLeftColor: "rgba(255,255,255,0.1)"
      , bottomRightColor: "rgba(255,255,255,0.02)"
      , opacity: 1.0
      }
  , shadowColor: "rgba(0,0,0,0.3)"
  , shadowBlur: 15.0
  , shadowOffsetY: 4.0
  }

-- | Windows Acrylic (Fluent Design)
acrylicGlass :: GlassEffect
acrylicGlass = GlassEffect
  { glassType: AcrylicGlass
  , blurRadius: 30.0
  , tintColor: "rgba(255,255,255,0.65)"
  , tintOpacity: 0.65
  , saturation: 1.25
  , brightness: 1.0
  , fresnel: noFresnel
  , noise: NoiseConfig
      { enabled: true
      , opacity: 0.02
      , scale: 1.0
      , animated: true  -- Windows uses animated noise
      }
  , border: noInternalBorder
  , shadowColor: "rgba(0,0,0,0.1)"
  , shadowBlur: 8.0
  , shadowOffsetY: 2.0
  }

-- | No glass effect (solid background)
noGlass :: GlassEffect
noGlass = GlassEffect
  { glassType: CustomGlass
  , blurRadius: 0.0
  , tintColor: "transparent"
  , tintOpacity: 0.0
  , saturation: 1.0
  , brightness: 1.0
  , fresnel: noFresnel
  , noise: noNoise
  , border: noInternalBorder
  , shadowColor: "transparent"
  , shadowBlur: 0.0
  , shadowOffsetY: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // platform presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apple platform glass (adapts to iOS/macOS/visionOS)
appleGlass :: GlassEffect
appleGlass = liquidGlass

-- | Windows platform glass (Fluent Design)
windowsAcrylic :: GlassEffect
windowsAcrylic = acrylicGlass

-- | Material You glass (Android 12+)
materialYou :: GlassEffect
materialYou = GlassEffect
  { glassType: MaterialGlass
  , blurRadius: 25.0
  , tintColor: "rgba(255,255,255,0.3)"  -- Tinted by system color extraction
  , tintOpacity: 0.3
  , saturation: 1.1
  , brightness: 1.0
  , fresnel: noFresnel
  , noise: noNoise  -- Material You doesn't use noise
  , border: noInternalBorder
  , shadowColor: "rgba(0,0,0,0.08)"
  , shadowBlur: 12.0
  , shadowOffsetY: 3.0
  }
