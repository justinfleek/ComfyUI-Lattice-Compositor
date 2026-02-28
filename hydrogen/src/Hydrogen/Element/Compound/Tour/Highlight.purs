-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // tour // highlight
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour Highlight — Spotlight and overlay styles for tour steps.
-- |
-- | ## Architecture
-- |
-- | Highlights draw attention to target elements:
-- | - Overlay blocks interaction with non-target content
-- | - Spotlight creates cutout around target
-- | - Pulse animations attract attention
-- | - Glow effects for emphasis
-- |
-- | ## Schema Mapping
-- |
-- | | Type            | Pillar    | Purpose                              |
-- | |-----------------|-----------|--------------------------------------|
-- | | HighlightKind   | Material  | Overall highlight strategy           |
-- | | SpotlightShape  | Geometry  | Shape of cutout (rect, circle, etc.) |
-- | | OverlayStyle    | Material  | How overlay is rendered              |
-- | | PulseAnimation  | Temporal  | Attention-grabbing animation         |
-- | | GlowStyle       | Material  | Glow effect around target            |
-- | | BorderStyle     | Material  | Border around spotlight              |

module Hydrogen.Element.Compound.Tour.Highlight
  ( -- * Highlight Kind
    HighlightKind
      ( HighlightSpotlight
      , HighlightOutline
      , HighlightGlow
      , HighlightOverlay
      , HighlightNone
      )
  
  -- * Spotlight Shape
  , SpotlightShape
      ( ShapeRect
      , ShapeRoundedRect
      , ShapeCircle
      , ShapeEllipse
      , ShapePill
      , ShapeInset
      , ShapeCustomPath
      )
  
  -- * Overlay Style
  , OverlayStyle
      ( OverlaySolid
      , OverlayBlur
      , OverlayGradient
      , OverlayPattern
      , OverlayNone
      )
  
  -- * Pulse Animation
  , PulseAnimation
      ( PulseNone
      , PulseRing
      , PulseGlow
      , PulseScale
      , PulseBounce
      , PulseShake
      , PulseBreathing
      )
  
  -- * Glow Style
  , GlowStyle
      ( GlowNone
      , GlowSoft
      , GlowStrong
      , GlowNeon
      , GlowPulsing
      )
  
  -- * Border Style
  , BorderStyle
      ( BorderNone
      , BorderSolid
      , BorderDashed
      , BorderDotted
      , BorderAnimated
      , BorderGradient
      )
  
  -- * Opacity
  , Opacity
  , opacity
  , unwrapOpacity
  , opaque
  , transparent
  , semiTransparent
  
  -- * Corner Radius
  , CornerRadius
  , cornerRadius
  , unwrapCornerRadius
  , sharpCorners
  , roundedCorners
  , pillCorners
  
  -- * Highlight Config
  , HighlightConfig
  , defaultHighlightConfig
  , spotlightConfig
  , outlineConfig
  , glowConfig
  , noHighlightConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Bounded
  , class Eq
  , class Ord
  , class Show
  , max
  , min
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // highlight kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | Primary highlight strategy for drawing attention to target.
-- |
-- | Each strategy has different visual impact:
-- | - Spotlight: Dark overlay with cutout (most common)
-- | - Outline: Just a border around element (subtle)
-- | - Glow: Luminous effect around element (modern)
-- | - Overlay: Full overlay without cutout (blocking)
-- | - None: No visual highlight (tooltip only)
data HighlightKind
  = HighlightSpotlight  -- ^ Overlay with cutout around target
  | HighlightOutline    -- ^ Border around target only
  | HighlightGlow       -- ^ Glow effect around target
  | HighlightOverlay    -- ^ Full overlay without cutout
  | HighlightNone       -- ^ No highlight, tooltip only

derive instance eqHighlightKind :: Eq HighlightKind
derive instance ordHighlightKind :: Ord HighlightKind

instance showHighlightKind :: Show HighlightKind where
  show HighlightSpotlight = "spotlight"
  show HighlightOutline = "outline"
  show HighlightGlow = "glow"
  show HighlightOverlay = "overlay"
  show HighlightNone = "none"

instance boundedHighlightKind :: Bounded HighlightKind where
  bottom = HighlightSpotlight
  top = HighlightNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // spotlight shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape of the spotlight cutout.
-- |
-- | Determines how the "hole" in the overlay is rendered.
data SpotlightShape
  = ShapeRect           -- ^ Sharp rectangle
  | ShapeRoundedRect    -- ^ Rectangle with corner radius
  | ShapeCircle         -- ^ Perfect circle (inscribed in bounds)
  | ShapeEllipse        -- ^ Ellipse matching aspect ratio
  | ShapePill           -- ^ Pill/capsule shape (fully rounded ends)
  | ShapeInset          -- ^ Inset rectangle with padding
  | ShapeCustomPath     -- ^ Custom SVG path (advanced)

derive instance eqSpotlightShape :: Eq SpotlightShape
derive instance ordSpotlightShape :: Ord SpotlightShape

instance showSpotlightShape :: Show SpotlightShape where
  show ShapeRect = "rect"
  show ShapeRoundedRect = "rounded-rect"
  show ShapeCircle = "circle"
  show ShapeEllipse = "ellipse"
  show ShapePill = "pill"
  show ShapeInset = "inset"
  show ShapeCustomPath = "custom-path"

instance boundedSpotlightShape :: Bounded SpotlightShape where
  bottom = ShapeRect
  top = ShapeCustomPath

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // overlay style
-- ═════════════════════════════════════════════════════════════════════════════

-- | How the overlay background is rendered.
-- |
-- | Different styles create different moods:
-- | - Solid: Classic dark scrim
-- | - Blur: Modern glassmorphism (backdrop-filter)
-- | - Gradient: Radial gradient centered on target
-- | - Pattern: Repeating pattern (dots, lines)
data OverlayStyle
  = OverlaySolid       -- ^ Solid color (usually semi-transparent black)
  | OverlayBlur        -- ^ Blur background content (glassmorphism)
  | OverlayGradient    -- ^ Radial gradient from target outward
  | OverlayPattern     -- ^ Repeating pattern overlay
  | OverlayNone        -- ^ No overlay (target only visible)

derive instance eqOverlayStyle :: Eq OverlayStyle
derive instance ordOverlayStyle :: Ord OverlayStyle

instance showOverlayStyle :: Show OverlayStyle where
  show OverlaySolid = "solid"
  show OverlayBlur = "blur"
  show OverlayGradient = "gradient"
  show OverlayPattern = "pattern"
  show OverlayNone = "none"

instance boundedOverlayStyle :: Bounded OverlayStyle where
  bottom = OverlaySolid
  top = OverlayNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // pulse animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated effect to attract attention to target.
-- |
-- | Pulse animations loop continuously while step is active.
data PulseAnimation
  = PulseNone       -- ^ No animation
  | PulseRing       -- ^ Expanding ring from target
  | PulseGlow       -- ^ Pulsing glow intensity
  | PulseScale      -- ^ Subtle scale up/down
  | PulseBounce     -- ^ Bouncing indicator
  | PulseShake      -- ^ Gentle shake effect
  | PulseBreathing  -- ^ Slow opacity breathing

derive instance eqPulseAnimation :: Eq PulseAnimation
derive instance ordPulseAnimation :: Ord PulseAnimation

instance showPulseAnimation :: Show PulseAnimation where
  show PulseNone = "none"
  show PulseRing = "ring"
  show PulseGlow = "glow"
  show PulseScale = "scale"
  show PulseBounce = "bounce"
  show PulseShake = "shake"
  show PulseBreathing = "breathing"

instance boundedPulseAnimation :: Bounded PulseAnimation where
  bottom = PulseNone
  top = PulseBreathing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // glow style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow effect intensity around target.
data GlowStyle
  = GlowNone      -- ^ No glow
  | GlowSoft      -- ^ Subtle, diffuse glow
  | GlowStrong    -- ^ Pronounced glow
  | GlowNeon      -- ^ Sharp, vibrant neon effect
  | GlowPulsing   -- ^ Glow that pulses in intensity

derive instance eqGlowStyle :: Eq GlowStyle
derive instance ordGlowStyle :: Ord GlowStyle

instance showGlowStyle :: Show GlowStyle where
  show GlowNone = "none"
  show GlowSoft = "soft"
  show GlowStrong = "strong"
  show GlowNeon = "neon"
  show GlowPulsing = "pulsing"

instance boundedGlowStyle :: Bounded GlowStyle where
  bottom = GlowNone
  top = GlowPulsing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // border style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border style around spotlight cutout.
data BorderStyle
  = BorderNone      -- ^ No border
  | BorderSolid     -- ^ Solid border line
  | BorderDashed    -- ^ Dashed border
  | BorderDotted    -- ^ Dotted border
  | BorderAnimated  -- ^ Animated "marching ants" border
  | BorderGradient  -- ^ Gradient border (conic or linear)

derive instance eqBorderStyle :: Eq BorderStyle
derive instance ordBorderStyle :: Ord BorderStyle

instance showBorderStyle :: Show BorderStyle where
  show BorderNone = "none"
  show BorderSolid = "solid"
  show BorderDashed = "dashed"
  show BorderDotted = "dotted"
  show BorderAnimated = "animated"
  show BorderGradient = "gradient"

instance boundedBorderStyle :: Bounded BorderStyle where
  bottom = BorderNone
  top = BorderGradient

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // opacity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opacity value (0.0 to 1.0, clamped).
newtype Opacity = Opacity Number

derive instance eqOpacity :: Eq Opacity
derive instance ordOpacity :: Ord Opacity

instance showOpacity :: Show Opacity where
  show (Opacity o) = "Opacity(" <> show o <> ")"

-- | Create an opacity value (clamped to 0-1)
opacity :: Number -> Opacity
opacity n = Opacity (max 0.0 (min 1.0 n))

-- | Extract opacity value
unwrapOpacity :: Opacity -> Number
unwrapOpacity (Opacity o) = o

-- | Fully opaque (1.0)
opaque :: Opacity
opaque = Opacity 1.0

-- | Fully transparent (0.0)
transparent :: Opacity
transparent = Opacity 0.0

-- | Semi-transparent (0.5)
semiTransparent :: Opacity
semiTransparent = Opacity 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // corner radius
-- ═════════════════════════════════════════════════════════════════════════════

-- | Corner radius in pixels (non-negative).
newtype CornerRadius = CornerRadius Int

derive instance eqCornerRadius :: Eq CornerRadius
derive instance ordCornerRadius :: Ord CornerRadius

instance showCornerRadius :: Show CornerRadius where
  show (CornerRadius r) = "CornerRadius(" <> show r <> "px)"

-- | Create a corner radius (clamped to non-negative)
cornerRadius :: Int -> CornerRadius
cornerRadius n = CornerRadius (max 0 n)

-- | Extract corner radius value
unwrapCornerRadius :: CornerRadius -> Int
unwrapCornerRadius (CornerRadius r) = r

-- | Sharp corners (0px)
sharpCorners :: CornerRadius
sharpCorners = CornerRadius 0

-- | Rounded corners (8px)
roundedCorners :: CornerRadius
roundedCorners = CornerRadius 8

-- | Pill corners (9999px - effectively 50%)
pillCorners :: CornerRadius
pillCorners = CornerRadius 9999

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // highlight config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete highlight configuration for a step.
type HighlightConfig =
  { kind :: HighlightKind             -- ^ Primary highlight strategy
  , shape :: SpotlightShape           -- ^ Shape of spotlight cutout
  , overlayStyle :: OverlayStyle      -- ^ Overlay rendering style
  , overlayOpacity :: Opacity         -- ^ Overlay opacity
  , pulse :: PulseAnimation           -- ^ Attention animation
  , glow :: GlowStyle                 -- ^ Glow effect
  , border :: BorderStyle             -- ^ Border around spotlight
  , cornerRadius :: CornerRadius      -- ^ Corner radius for shapes
  , padding :: Int                    -- ^ Padding around target (px)
  , clickThrough :: Boolean           -- ^ Allow clicking through overlay
  , interactiveTarget :: Boolean      -- ^ Allow interaction with target
  }

-- | Default spotlight highlight
defaultHighlightConfig :: HighlightConfig
defaultHighlightConfig =
  { kind: HighlightSpotlight
  , shape: ShapeRoundedRect
  , overlayStyle: OverlaySolid
  , overlayOpacity: opacity 0.5
  , pulse: PulseNone
  , glow: GlowNone
  , border: BorderNone
  , cornerRadius: roundedCorners
  , padding: 4
  , clickThrough: false
  , interactiveTarget: false
  }

-- | Spotlight configuration preset
spotlightConfig :: HighlightConfig
spotlightConfig = defaultHighlightConfig

-- | Outline-only configuration preset
outlineConfig :: HighlightConfig
outlineConfig = defaultHighlightConfig
  { kind = HighlightOutline
  , overlayStyle = OverlayNone
  , overlayOpacity = transparent
  , border = BorderSolid
  }

-- | Glow configuration preset
glowConfig :: HighlightConfig
glowConfig = defaultHighlightConfig
  { kind = HighlightGlow
  , overlayStyle = OverlaySolid
  , overlayOpacity = opacity 0.3
  , glow = GlowSoft
  , pulse = PulseGlow
  }

-- | No highlight configuration preset
noHighlightConfig :: HighlightConfig
noHighlightConfig = defaultHighlightConfig
  { kind = HighlightNone
  , overlayStyle = OverlayNone
  , overlayOpacity = transparent
  }
