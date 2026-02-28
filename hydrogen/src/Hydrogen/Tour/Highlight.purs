-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // tour // highlight
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spotlight and Overlay System for Product Tours
-- |
-- | This module provides the visual vocabulary for highlighting target elements:
-- | - Overlay configuration (color, opacity, blur)
-- | - Spotlight shapes (rect, circle, rounded)
-- | - Highlight styles (glow, pulse, ring)
-- | - Cutout generation for SVG/canvas rendering
-- |
-- | ## Design Philosophy
-- |
-- | Highlights are pure data describing visual effects. The runtime interprets
-- | these to produce actual DOM/SVG/Canvas elements. This enables:
-- | - Deterministic rendering (same config = same pixels)
-- | - Multiple rendering targets (DOM, Canvas, WebGL)
-- | - Composable visual effects
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Highlight as H
-- |
-- | -- Basic spotlight
-- | spotlightConfig = H.spotlight
-- |   { shape: H.RoundedRect (Pixel 8)
-- |   , padding: Pixel 12
-- |   , style: H.Glow { color: "#3b82f6", spread: Pixel 4 }
-- |   }
-- |
-- | -- Animated overlay
-- | overlayConfig = H.overlay
-- |   { color: H.OverlayBlack
-- |   , opacity: H.Opacity75
-- |   , blur: Just (Pixel 2)
-- |   }
-- | ```
module Hydrogen.Tour.Highlight
  ( -- * Overlay Configuration
    OverlayConfig
  , defaultOverlay
  , OverlayColor(..)
  , OverlayOpacity(..)
  , overlayColorToCss
  , overlayOpacityToNumber
    -- * Overlay Builders
  , overlay
  , darkOverlay
  , lightOverlay
  , brandOverlay
  , withBlur
  , withInteraction
    -- * Spotlight Configuration
  , SpotlightConfig
  , defaultSpotlight
  , SpotlightShape(..)
  , spotlightShapeToCss
    -- * Spotlight Builders
  , spotlight
  , rectSpotlight
  , circleSpotlight
  , roundedSpotlight
  , pillSpotlight
    -- * Highlight Styles
  , HighlightStyle(..)
  , HighlightGlow
  , HighlightPulse
  , HighlightRing
  , HighlightGradient
  , defaultGlow
  , defaultPulse
  , defaultRing
    -- * Cutout Generation
  , CutoutPath
  , PathCommand(..)
  , generateRectCutout
  , generateCircleCutout
  , generateRoundedCutout
  , cutoutToSvgPath
  , cutoutToClipPath
    -- * Pulse Animation
  , PulseConfig
  , defaultPulseConfig
  , pulseAnimation
  , PulseStyle(..)
    -- * Interaction Modes
  , InteractionMode(..)
  , pointerEventsFromMode
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Show.Generic (genericShow)
import Data.String (joinWith)
import Hydrogen.Tour.Animation (EasingCurve, EasingPreset(EaseInOut), easingPreset)
import Hydrogen.Tour.Target (TargetRect)
import Hydrogen.Tour.Types (Milliseconds(Milliseconds), Pixel(Pixel))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // overlay configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for the overlay backdrop
-- |
-- | The overlay covers the entire viewport with a semi-transparent layer,
-- | except for the spotlight cutout.
type OverlayConfig =
  { color :: OverlayColor
    -- ^ Background color
  , opacity :: OverlayOpacity
    -- ^ Transparency level
  , blur :: Maybe Pixel
    -- ^ Optional backdrop blur
  , interaction :: InteractionMode
    -- ^ How user interaction is handled
  , transition :: Milliseconds
    -- ^ Transition duration for appearance
  }

-- | Preset overlay colors
-- |
-- | Bounded enumeration of overlay colors. No arbitrary strings.
data OverlayColor
  = OverlayBlack
    -- ^ Classic black overlay
  | OverlayGray
    -- ^ Softer gray overlay
  | OverlayBlue
    -- ^ Brand blue tint
  | OverlayPurple
    -- ^ Purple tint (creative tools)
  | OverlayGreen
    -- ^ Green tint (success/nature)
  | OverlayCustom { r :: Int, g :: Int, b :: Int }
    -- ^ Custom RGB (bounded 0-255)

derive instance eqOverlayColor :: Eq OverlayColor
derive instance genericOverlayColor :: Generic OverlayColor _

instance showOverlayColor :: Show OverlayColor where
  show = genericShow

-- | Preset opacity levels
-- |
-- | Bounded enumeration ensures consistent visual hierarchy.
data OverlayOpacity
  = Opacity25
    -- ^ Very light (subtle hint)
  | Opacity50
    -- ^ Medium (noticeable but see-through)
  | Opacity60
    -- ^ Slightly darker
  | Opacity75
    -- ^ Standard tour overlay
  | Opacity80
    -- ^ Darker, more focus
  | Opacity90
    -- ^ Very dark (maximum focus)

derive instance eqOverlayOpacity :: Eq OverlayOpacity
derive instance ordOverlayOpacity :: Ord OverlayOpacity
derive instance genericOverlayOpacity :: Generic OverlayOpacity _

instance showOverlayOpacity :: Show OverlayOpacity where
  show = genericShow

-- | Convert overlay color to CSS rgba
overlayColorToCss :: OverlayColor -> OverlayOpacity -> String
overlayColorToCss color opacity =
  let alpha = overlayOpacityToNumber opacity
  in case color of
    OverlayBlack -> "rgba(0, 0, 0, " <> show alpha <> ")"
    OverlayGray -> "rgba(55, 65, 81, " <> show alpha <> ")"
    OverlayBlue -> "rgba(30, 58, 138, " <> show alpha <> ")"
    OverlayPurple -> "rgba(76, 29, 149, " <> show alpha <> ")"
    OverlayGreen -> "rgba(20, 83, 45, " <> show alpha <> ")"
    OverlayCustom { r, g, b } -> 
      "rgba(" <> show r <> ", " <> show g <> ", " <> show b <> ", " <> show alpha <> ")"

-- | Convert opacity level to number
overlayOpacityToNumber :: OverlayOpacity -> Number
overlayOpacityToNumber = case _ of
  Opacity25 -> 0.25
  Opacity50 -> 0.50
  Opacity60 -> 0.60
  Opacity75 -> 0.75
  Opacity80 -> 0.80
  Opacity90 -> 0.90

-- | Default overlay configuration
defaultOverlay :: OverlayConfig
defaultOverlay =
  { color: OverlayBlack
  , opacity: Opacity75
  , blur: Nothing
  , interaction: BlockAll
  , transition: Milliseconds 200
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // overlay builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create overlay configuration
overlay :: OverlayColor -> OverlayOpacity -> OverlayConfig
overlay color opacity = defaultOverlay { color = color, opacity = opacity }

-- | Dark overlay (standard)
darkOverlay :: OverlayConfig
darkOverlay = overlay OverlayBlack Opacity75

-- | Light overlay (softer)
lightOverlay :: OverlayConfig
lightOverlay = overlay OverlayGray Opacity50

-- | Brand-colored overlay
brandOverlay :: { r :: Int, g :: Int, b :: Int } -> OverlayConfig
brandOverlay rgb = overlay (OverlayCustom rgb) Opacity60

-- | Add backdrop blur
withBlur :: Pixel -> OverlayConfig -> OverlayConfig
withBlur px cfg = cfg { blur = Just px }

-- | Set interaction mode
withInteraction :: InteractionMode -> OverlayConfig -> OverlayConfig
withInteraction mode cfg = cfg { interaction = mode }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // spotlight configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for the spotlight cutout
-- |
-- | The spotlight is the "window" in the overlay that reveals the target element.
type SpotlightConfig =
  { shape :: SpotlightShape
    -- ^ Shape of the cutout
  , padding :: Pixel
    -- ^ Space between element edge and spotlight edge
  , style :: Maybe HighlightStyle
    -- ^ Optional visual embellishment
  , animate :: Boolean
    -- ^ Whether to animate shape changes
  }

-- | Shape of the spotlight cutout
data SpotlightShape
  = ShapeRect
    -- ^ Sharp rectangle
  | ShapeCircle
    -- ^ Perfect circle (enclosing)
  | ShapeRounded Pixel
    -- ^ Rectangle with border radius
  | ShapePill
    -- ^ Pill shape (fully rounded ends)
  | ShapeInset Pixel
    -- ^ Rounded with inset (visual depth)

derive instance eqSpotlightShape :: Eq SpotlightShape
derive instance genericSpotlightShape :: Generic SpotlightShape _

instance showSpotlightShape :: Show SpotlightShape where
  show = genericShow

-- | Convert shape to CSS border-radius
spotlightShapeToCss :: SpotlightShape -> TargetRect -> String
spotlightShapeToCss shape rect = case shape of
  ShapeRect -> "0"
  ShapeCircle -> "50%"
  ShapeRounded (Pixel r) -> show r <> "px"
  ShapePill -> show (min rect.width rect.height / 2.0) <> "px"
  ShapeInset (Pixel r) -> show r <> "px"

-- | Default spotlight configuration
defaultSpotlight :: SpotlightConfig
defaultSpotlight =
  { shape: ShapeRounded (Pixel 8)
  , padding: Pixel 8
  , style: Just (Glow defaultGlow)
  , animate: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // spotlight builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create spotlight configuration
spotlight :: SpotlightShape -> Pixel -> SpotlightConfig
spotlight shape padding = defaultSpotlight { shape = shape, padding = padding }

-- | Rectangle spotlight
rectSpotlight :: Pixel -> SpotlightConfig
rectSpotlight = spotlight ShapeRect

-- | Circle spotlight
circleSpotlight :: Pixel -> SpotlightConfig
circleSpotlight = spotlight ShapeCircle

-- | Rounded rectangle spotlight
roundedSpotlight :: Pixel -> Pixel -> SpotlightConfig
roundedSpotlight radius = spotlight (ShapeRounded radius)

-- | Pill-shaped spotlight
pillSpotlight :: Pixel -> SpotlightConfig
pillSpotlight = spotlight ShapePill

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // highlight styles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual style for spotlight highlight
-- |
-- | These are decorative effects applied to the spotlight cutout.
data HighlightStyle
  = Glow HighlightGlow
    -- ^ Soft glow around spotlight
  | Pulse HighlightPulse
    -- ^ Pulsing animation
  | Ring HighlightRing
    -- ^ Border ring
  | GradientBorder HighlightGradient
    -- ^ Gradient border effect
  | Combined (Array HighlightStyle)
    -- ^ Multiple styles combined

derive instance eqHighlightStyle :: Eq HighlightStyle
derive instance genericHighlightStyle :: Generic HighlightStyle _

-- | Manual Show instance to handle recursive Combined
instance showHighlightStyle :: Show HighlightStyle where
  show = case _ of
    Glow cfg -> "(Glow { color: " <> show cfg.color <> 
                ", spread: " <> show cfg.spread <>
                ", opacity: " <> show cfg.opacity <> " })"
    Pulse cfg -> "(Pulse { color: " <> show cfg.color <>
                 ", scale: " <> show cfg.scale <>
                 ", duration: " <> show cfg.duration <> " })"
    Ring cfg -> "(Ring { color: " <> show cfg.color <>
                ", width: " <> show cfg.width <>
                ", style: " <> show cfg.style <> " })"
    GradientBorder cfg -> "(GradientBorder { colors: " <> show cfg.colors <>
                          ", angle: " <> show cfg.angle <>
                          ", width: " <> show cfg.width <> " })"
    Combined styles -> "(Combined [" <> joinWith ", " (map show styles) <> "])"

-- | Glow effect configuration
type HighlightGlow =
  { color :: String
    -- ^ Glow color (CSS color)
  , spread :: Pixel
    -- ^ Glow spread distance
  , opacity :: Number
    -- ^ Glow opacity (0-1)
  }

-- | Pulse animation configuration
type HighlightPulse =
  { color :: String
    -- ^ Pulse color
  , scale :: Number
    -- ^ Maximum scale (1.0 = no scale)
  , duration :: Milliseconds
    -- ^ Pulse cycle duration
  }

-- | Ring border configuration
type HighlightRing =
  { color :: String
    -- ^ Ring color
  , width :: Pixel
    -- ^ Ring thickness
  , style :: String
    -- ^ CSS border style (solid, dashed, etc.)
  }

-- | Gradient border configuration
type HighlightGradient =
  { colors :: Array String
    -- ^ Gradient color stops
  , width :: Pixel
    -- ^ Border width
  , angle :: Int
    -- ^ Gradient angle (degrees)
  }

-- | Default glow configuration
defaultGlow :: HighlightGlow
defaultGlow =
  { color: "#3b82f6"  -- Blue 500
  , spread: Pixel 4
  , opacity: 0.5
  }

-- | Default pulse configuration
defaultPulse :: HighlightPulse
defaultPulse =
  { color: "#3b82f6"
  , scale: 1.05
  , duration: Milliseconds 1500
  }

-- | Default ring configuration
defaultRing :: HighlightRing
defaultRing =
  { color: "#3b82f6"
  , width: Pixel 2
  , style: "solid"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // cutout generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Path data for spotlight cutout
-- |
-- | Used to generate SVG paths or Canvas clip regions.
type CutoutPath =
  { commands :: Array PathCommand
  , bounds :: TargetRect
  }

-- | SVG path command
data PathCommand
  = MoveTo Number Number
  | LineTo Number Number
  | ArcTo Number Number Number Number Number
  | QuadraticTo Number Number Number Number
  | Close

derive instance eqPathCommand :: Eq PathCommand
derive instance genericPathCommand :: Generic PathCommand _

instance showPathCommand :: Show PathCommand where
  show = genericShow

-- | Generate rectangular cutout path
generateRectCutout :: TargetRect -> Pixel -> CutoutPath
generateRectCutout rect (Pixel padding) =
  let 
    p = toNumber padding
    x = rect.x - p
    y = rect.y - p
    w = rect.width + p * 2.0
    h = rect.height + p * 2.0
  in
    { commands:
        [ MoveTo x y
        , LineTo (x + w) y
        , LineTo (x + w) (y + h)
        , LineTo x (y + h)
        , Close
        ]
    , bounds: { x, y, width: w, height: h, top: y, right: x + w, bottom: y + h, left: x }
    }

-- | Generate circular cutout path
generateCircleCutout :: TargetRect -> Pixel -> CutoutPath
generateCircleCutout rect (Pixel padding) =
  let 
    p = toNumber padding
    cx = rect.x + rect.width / 2.0
    cy = rect.y + rect.height / 2.0
    r = max rect.width rect.height / 2.0 + p
  in
    { commands:
        [ MoveTo cx (cy - r)
        , ArcTo r r 0.0 1.0 1.0  -- Full circle via two arcs
        , ArcTo r r 0.0 1.0 1.0
        ]
    , bounds: { x: cx - r, y: cy - r, width: r * 2.0, height: r * 2.0
              , top: cy - r, right: cx + r, bottom: cy + r, left: cx - r }
    }

-- | Generate rounded rectangle cutout path
generateRoundedCutout :: TargetRect -> Pixel -> Pixel -> CutoutPath
generateRoundedCutout rect (Pixel padding) (Pixel radius) =
  let 
    p = toNumber padding
    r = min (toNumber radius) (min rect.width rect.height / 2.0)
    x = rect.x - p
    y = rect.y - p
    w = rect.width + p * 2.0
    h = rect.height + p * 2.0
  in
    { commands:
        [ MoveTo (x + r) y
        , LineTo (x + w - r) y
        , QuadraticTo (x + w) y (x + w) (y + r)
        , LineTo (x + w) (y + h - r)
        , QuadraticTo (x + w) (y + h) (x + w - r) (y + h)
        , LineTo (x + r) (y + h)
        , QuadraticTo x (y + h) x (y + h - r)
        , LineTo x (y + r)
        , QuadraticTo x y (x + r) y
        , Close
        ]
    , bounds: { x, y, width: w, height: h, top: y, right: x + w, bottom: y + h, left: x }
    }

-- | Convert cutout to SVG path d attribute
cutoutToSvgPath :: CutoutPath -> String
cutoutToSvgPath cutout = intercalate " " (map commandToSvg cutout.commands)
  where
  commandToSvg :: PathCommand -> String
  commandToSvg = case _ of
    MoveTo x y -> "M " <> show x <> " " <> show y
    LineTo x y -> "L " <> show x <> " " <> show y
    ArcTo rx ry rot large sweep -> 
      "A " <> show rx <> " " <> show ry <> " " <> show rot <> " " <> 
      show large <> " " <> show sweep
    QuadraticTo cx cy x y -> 
      "Q " <> show cx <> " " <> show cy <> " " <> show x <> " " <> show y
    Close -> "Z"
  
  intercalate :: String -> Array String -> String
  intercalate sep arr = foldl (\acc s -> if acc == "" then s else acc <> sep <> s) "" arr
  
  foldl :: forall a b. (b -> a -> b) -> b -> Array a -> b
  foldl = foldlImpl
  
foreign import foldlImpl :: forall a b. (b -> a -> b) -> b -> Array a -> b

-- | Convert cutout to CSS clip-path
cutoutToClipPath :: CutoutPath -> String
cutoutToClipPath cutout = "path('" <> cutoutToSvgPath cutout <> "')"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // pulse animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for pulse animation
type PulseConfig =
  { style :: PulseStyle
  , duration :: Milliseconds
  , easing :: EasingCurve
  , iterations :: Maybe Int
    -- ^ Nothing = infinite
  }

-- | Pulse animation style
data PulseStyle
  = PulseScale
    -- ^ Scale up and down
  | PulseOpacity
    -- ^ Fade in and out
  | PulseGlow
    -- ^ Glow intensity changes
  | PulseRing
    -- ^ Expanding ring

derive instance eqPulseStyle :: Eq PulseStyle
derive instance genericPulseStyle :: Generic PulseStyle _

instance showPulseStyle :: Show PulseStyle where
  show = genericShow

-- | Default pulse configuration
defaultPulseConfig :: PulseConfig
defaultPulseConfig =
  { style: PulseGlow
  , duration: Milliseconds 1500
  , easing: easingPreset EaseInOut
  , iterations: Nothing  -- Infinite
  }

-- | Generate CSS animation for pulse
pulseAnimation :: PulseConfig -> String
pulseAnimation cfg =
  let 
    name = case cfg.style of
      PulseScale -> "tour-pulse-scale"
      PulseOpacity -> "tour-pulse-opacity"
      PulseGlow -> "tour-pulse-glow"
      PulseRing -> "tour-pulse-ring"
    dur = case cfg.duration of
      Milliseconds ms -> show ms <> "ms"
    iters = case cfg.iterations of
      Nothing -> "infinite"
      Just n -> show n
  in
    name <> " " <> dur <> " ease-in-out " <> iters

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // interaction modes
-- ═════════════════════════════════════════════════════════════════════════════

-- | How user interaction is handled
data InteractionMode
  = BlockAll
    -- ^ Block all clicks on overlay
  | AllowClick
    -- ^ Allow clicks to pass through
  | AllowOnTarget
    -- ^ Block overlay, allow target interaction
  | DismissOnClick
    -- ^ Clicking overlay dismisses tour

derive instance eqInteractionMode :: Eq InteractionMode
derive instance genericInteractionMode :: Generic InteractionMode _

instance showInteractionMode :: Show InteractionMode where
  show = genericShow

-- | Convert interaction mode to CSS pointer-events
pointerEventsFromMode :: InteractionMode -> { overlay :: String, target :: String }
pointerEventsFromMode = case _ of
  BlockAll -> { overlay: "auto", target: "none" }
  AllowClick -> { overlay: "none", target: "auto" }
  AllowOnTarget -> { overlay: "auto", target: "auto" }
  DismissOnClick -> { overlay: "auto", target: "auto" }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number
foreign import toNumber :: Int -> Number
