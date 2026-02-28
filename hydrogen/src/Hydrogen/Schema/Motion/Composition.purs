-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // motion // composition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Composition settings and related types for motion graphics.
-- |
-- | A Composition is the fundamental container for animated content — 
-- | analogous to a timeline in After Effects. It defines:
-- | - Dimensions (width × height)
-- | - Frame rate and duration
-- | - Background color
-- | - Rendering settings
-- |
-- | ## Architecture
-- |
-- | This module mirrors `Lattice.Project` from the Haskell backend,
-- | ensuring type-level compatibility for serialization.
-- |
-- | ## Blend Modes
-- |
-- | All 28 standard compositing blend modes are supported, following
-- | the Porter-Duff and SVG compositing specifications.
-- |
-- | ## Track Mattes
-- |
-- | Track matte modes for alpha and luminance masking between layers.

module Hydrogen.Schema.Motion.Composition
  ( -- * Composition Settings
    CompositionSettings(..)
  , defaultCompositionSettings
  , mkCompositionSettings
  
  -- * Composition Identifier
  , CompositionId(..)
  , mkCompositionId
  
  -- * Blend Mode
  , BlendMode(..)
  , blendModeToString
  , blendModeFromString
  , isBlendModeAdditive
  , isBlendModeSubtractive
  
  -- * Track Matte Mode
  , TrackMatteMode(..)
  , trackMatteModeToString
  , trackMatteModeFromString
  
  -- * Motion Blur Settings
  , MotionBlurSettings(..)
  , defaultMotionBlurSettings
  , motionBlurEnabled
  
  -- * Color Settings
  , ColorSpace(..)
  , BitDepth(..)
  
  -- * Accessors
  , compositionWidth
  , compositionHeight
  , compositionFrameCount
  , compositionFps
  , compositionDuration
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , ($)
  , (==)
  , (+)
  , (*)
  , (/)
  , (<>)
  , (&&)
  , (>)
  , (>=)
  , (<=)
  , max
  , min
  )

import Data.Int (floor, toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Dimension.Temporal (FrameRate(FrameRate), Seconds(Seconds))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // composition // id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a composition.
-- |
-- | Uses NonEmptyString semantics — must have at least one character.
newtype CompositionId = CompositionId String

derive instance eqCompositionId :: Eq CompositionId
derive instance ordCompositionId :: Ord CompositionId

instance showCompositionId :: Show CompositionId where
  show (CompositionId id) = "Comp:" <> id

-- | Smart constructor for CompositionId.
-- |
-- | Returns Nothing if the string is empty.
mkCompositionId :: String -> Maybe CompositionId
mkCompositionId "" = Nothing
mkCompositionId s = Just (CompositionId s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // blend // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend mode for compositing layers.
-- |
-- | Supports all 28 standard blend modes from Porter-Duff and SVG specifications.
-- | These are the same blend modes available in After Effects, Photoshop, and CSS.
data BlendMode
  -- Standard modes
  = BMNormal
  | BMMultiply
  | BMScreen
  | BMOverlay
  -- Darken modes
  | BMDarken
  | BMColorBurn
  | BMLinearBurn
  | BMDarkerColor
  -- Lighten modes
  | BMLighten
  | BMColorDodge
  | BMLinearDodge
  | BMLighterColor
  -- Contrast modes
  | BMHardLight
  | BMSoftLight
  | BMVividLight
  | BMLinearLight
  | BMPinLight
  | BMHardMix
  -- Inversion modes
  | BMDifference
  | BMExclusion
  | BMSubtract
  | BMDivide
  -- Component modes
  | BMHue
  | BMSaturation
  | BMColor
  | BMLuminosity
  -- Arithmetic modes
  | BMAdd
  | BMDissolve

derive instance eqBlendMode :: Eq BlendMode
derive instance ordBlendMode :: Ord BlendMode

instance showBlendMode :: Show BlendMode where
  show = blendModeToString

-- | Convert blend mode to string representation.
blendModeToString :: BlendMode -> String
blendModeToString BMNormal = "normal"
blendModeToString BMMultiply = "multiply"
blendModeToString BMScreen = "screen"
blendModeToString BMOverlay = "overlay"
blendModeToString BMDarken = "darken"
blendModeToString BMColorBurn = "color-burn"
blendModeToString BMLinearBurn = "linear-burn"
blendModeToString BMDarkerColor = "darker-color"
blendModeToString BMLighten = "lighten"
blendModeToString BMColorDodge = "color-dodge"
blendModeToString BMLinearDodge = "linear-dodge"
blendModeToString BMLighterColor = "lighter-color"
blendModeToString BMHardLight = "hard-light"
blendModeToString BMSoftLight = "soft-light"
blendModeToString BMVividLight = "vivid-light"
blendModeToString BMLinearLight = "linear-light"
blendModeToString BMPinLight = "pin-light"
blendModeToString BMHardMix = "hard-mix"
blendModeToString BMDifference = "difference"
blendModeToString BMExclusion = "exclusion"
blendModeToString BMSubtract = "subtract"
blendModeToString BMDivide = "divide"
blendModeToString BMHue = "hue"
blendModeToString BMSaturation = "saturation"
blendModeToString BMColor = "color"
blendModeToString BMLuminosity = "luminosity"
blendModeToString BMAdd = "add"
blendModeToString BMDissolve = "dissolve"

-- | Parse blend mode from string.
blendModeFromString :: String -> Maybe BlendMode
blendModeFromString "normal" = Just BMNormal
blendModeFromString "multiply" = Just BMMultiply
blendModeFromString "screen" = Just BMScreen
blendModeFromString "overlay" = Just BMOverlay
blendModeFromString "darken" = Just BMDarken
blendModeFromString "color-burn" = Just BMColorBurn
blendModeFromString "linear-burn" = Just BMLinearBurn
blendModeFromString "darker-color" = Just BMDarkerColor
blendModeFromString "lighten" = Just BMLighten
blendModeFromString "color-dodge" = Just BMColorDodge
blendModeFromString "linear-dodge" = Just BMLinearDodge
blendModeFromString "lighter-color" = Just BMLighterColor
blendModeFromString "hard-light" = Just BMHardLight
blendModeFromString "soft-light" = Just BMSoftLight
blendModeFromString "vivid-light" = Just BMVividLight
blendModeFromString "linear-light" = Just BMLinearLight
blendModeFromString "pin-light" = Just BMPinLight
blendModeFromString "hard-mix" = Just BMHardMix
blendModeFromString "difference" = Just BMDifference
blendModeFromString "exclusion" = Just BMExclusion
blendModeFromString "subtract" = Just BMSubtract
blendModeFromString "divide" = Just BMDivide
blendModeFromString "hue" = Just BMHue
blendModeFromString "saturation" = Just BMSaturation
blendModeFromString "color" = Just BMColor
blendModeFromString "luminosity" = Just BMLuminosity
blendModeFromString "add" = Just BMAdd
blendModeFromString "dissolve" = Just BMDissolve
blendModeFromString _ = Nothing

-- | Check if blend mode adds light (screen-like).
isBlendModeAdditive :: BlendMode -> Boolean
isBlendModeAdditive BMScreen = true
isBlendModeAdditive BMColorDodge = true
isBlendModeAdditive BMLinearDodge = true
isBlendModeAdditive BMAdd = true
isBlendModeAdditive BMLighten = true
isBlendModeAdditive BMLighterColor = true
isBlendModeAdditive _ = false

-- | Check if blend mode removes light (multiply-like).
isBlendModeSubtractive :: BlendMode -> Boolean
isBlendModeSubtractive BMMultiply = true
isBlendModeSubtractive BMColorBurn = true
isBlendModeSubtractive BMLinearBurn = true
isBlendModeSubtractive BMDarken = true
isBlendModeSubtractive BMDarkerColor = true
isBlendModeSubtractive BMSubtract = true
isBlendModeSubtractive _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // track // matte
-- ═════════════════════════════════════════════════════════════════════════════

-- | Track matte mode for masking between layers.
-- |
-- | A track matte uses one layer to define the transparency of another:
-- | - Alpha: Uses the alpha channel of the matte layer
-- | - Luma: Uses the luminance of the matte layer
-- | - Inverted variants: Inverts the matte values
data TrackMatteMode
  = TMNone           -- No track matte
  | TMAlpha          -- Use alpha channel
  | TMAlphaInverted  -- Use inverted alpha
  | TMLuma           -- Use luminance
  | TMLumaInverted   -- Use inverted luminance

derive instance eqTrackMatteMode :: Eq TrackMatteMode
derive instance ordTrackMatteMode :: Ord TrackMatteMode

instance showTrackMatteMode :: Show TrackMatteMode where
  show = trackMatteModeToString

-- | Convert track matte mode to string.
trackMatteModeToString :: TrackMatteMode -> String
trackMatteModeToString TMNone = "none"
trackMatteModeToString TMAlpha = "alpha"
trackMatteModeToString TMAlphaInverted = "alpha-inverted"
trackMatteModeToString TMLuma = "luma"
trackMatteModeToString TMLumaInverted = "luma-inverted"

-- | Parse track matte mode from string.
trackMatteModeFromString :: String -> Maybe TrackMatteMode
trackMatteModeFromString "none" = Just TMNone
trackMatteModeFromString "alpha" = Just TMAlpha
trackMatteModeFromString "alpha-inverted" = Just TMAlphaInverted
trackMatteModeFromString "luma" = Just TMLuma
trackMatteModeFromString "luma-inverted" = Just TMLumaInverted
trackMatteModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color // space
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color space for composition working space.
data ColorSpace
  = CSSrgb           -- Standard sRGB
  | CSLinearSrgb     -- Linear sRGB (for compositing)
  | CSRec709         -- HD video standard
  | CSRec2020        -- UHD/HDR video standard
  | CSDciP3          -- Digital cinema
  | CSAcesCg         -- ACES computer graphics
  | CSAces2065       -- ACES full gamut

derive instance eqColorSpace :: Eq ColorSpace
derive instance ordColorSpace :: Ord ColorSpace

instance showColorSpace :: Show ColorSpace where
  show CSSrgb = "srgb"
  show CSLinearSrgb = "linear-srgb"
  show CSRec709 = "rec709"
  show CSRec2020 = "rec2020"
  show CSDciP3 = "dci-p3"
  show CSAcesCg = "aces-cg"
  show CSAces2065 = "aces-2065"

-- | Bit depth for composition rendering.
data BitDepth
  = BD8Bit           -- 8 bits per channel (standard)
  | BD16Bit          -- 16 bits per channel (high quality)
  | BD32Bit          -- 32 bits per channel (HDR/float)

derive instance eqBitDepth :: Eq BitDepth
derive instance ordBitDepth :: Ord BitDepth

instance showBitDepth :: Show BitDepth where
  show BD8Bit = "8bpc"
  show BD16Bit = "16bpc"
  show BD32Bit = "32bpc"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // motion // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Motion blur settings for a composition.
-- |
-- | Motion blur simulates camera shutter by averaging multiple samples
-- | across the frame duration.
newtype MotionBlurSettings = MotionBlurSettings
  { enabled :: Boolean
  , samplesPerFrame :: Int       -- Number of samples (typically 8-64)
  , shutterAngle :: Number       -- 0-720 degrees (360 = full frame)
  , shutterPhase :: Number       -- -360 to 360 degrees (offset)
  , adaptiveSampling :: Boolean  -- Increase samples for fast motion
  }

derive instance eqMotionBlurSettings :: Eq MotionBlurSettings

instance showMotionBlurSettings :: Show MotionBlurSettings where
  show (MotionBlurSettings s) = 
    "MotionBlur(" <> show s.shutterAngle <> "deg, " <> 
    show s.samplesPerFrame <> " samples)"

-- | Default motion blur settings (disabled).
defaultMotionBlurSettings :: MotionBlurSettings
defaultMotionBlurSettings = MotionBlurSettings
  { enabled: false
  , samplesPerFrame: 16
  , shutterAngle: 180.0    -- Standard 180-degree shutter
  , shutterPhase: 0.0
  , adaptiveSampling: true
  }

-- | Create enabled motion blur settings.
motionBlurEnabled :: Int -> Number -> MotionBlurSettings
motionBlurEnabled samples angle = MotionBlurSettings
  { enabled: true
  , samplesPerFrame: max 1 samples
  , shutterAngle: max 0.0 (min 720.0 angle)
  , shutterPhase: 0.0
  , adaptiveSampling: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // composition // settings
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete composition settings.
-- |
-- | Defines the render target dimensions, timing, and visual properties.
-- |
-- | ## Invariants
-- |
-- | - width > 0, must be divisible by 8 for video encoding
-- | - height > 0, must be divisible by 8 for video encoding
-- | - frameCount >= 0
-- | - fps > 0
-- | - duration = frameCount / fps
newtype CompositionSettings = CompositionSettings
  { width :: Int                       -- Composition width in pixels
  , height :: Int                      -- Composition height in pixels
  , frameCount :: Int                  -- Total number of frames
  , fps :: FrameRate                   -- Frames per second
  , duration :: Seconds                -- Total duration (derived)
  , backgroundColor :: String          -- Background color (hex)
  , colorSpace :: ColorSpace           -- Working color space
  , bitDepth :: BitDepth               -- Render bit depth
  , motionBlur :: MotionBlurSettings   -- Motion blur settings
  , frameBlending :: Boolean           -- Enable frame blending
  , autoResize :: Boolean              -- Auto-resize to content
  }

derive instance eqCompositionSettings :: Eq CompositionSettings

instance showCompositionSettings :: Show CompositionSettings where
  show (CompositionSettings s) =
    show s.width <> "x" <> show s.height <> " @ " <> show s.fps <> 
    ", " <> show s.frameCount <> " frames"

-- | Default composition settings (1920x1080 @ 30fps, 300 frames = 10 seconds).
defaultCompositionSettings :: CompositionSettings
defaultCompositionSettings = CompositionSettings
  { width: 1920
  , height: 1080
  , frameCount: 300
  , fps: FrameRate 30.0
  , duration: Seconds 10.0
  , backgroundColor: "#000000"
  , colorSpace: CSSrgb
  , bitDepth: BD8Bit
  , motionBlur: defaultMotionBlurSettings
  , frameBlending: false
  , autoResize: false
  }

-- | Smart constructor for composition settings.
-- |
-- | Validates dimensions and calculates duration from frame count and fps.
mkCompositionSettings 
  :: Int           -- width
  -> Int           -- height
  -> Int           -- frameCount
  -> FrameRate     -- fps
  -> String        -- backgroundColor
  -> Maybe CompositionSettings
mkCompositionSettings w h fc (FrameRate fpsVal) bg
  | w > 0 && h > 0 && fc >= 0 && fpsVal > 0.0 = Just $ CompositionSettings
      { width: alignTo8 w
      , height: alignTo8 h
      , frameCount: fc
      , fps: FrameRate fpsVal
      , duration: Seconds (Int.toNumber fc / fpsVal)
      , backgroundColor: bg
      , colorSpace: CSSrgb
      , bitDepth: BD8Bit
      , motionBlur: defaultMotionBlurSettings
      , frameBlending: false
      , autoResize: false
      }
  | true = Nothing

-- | Align integer to 8-pixel boundary for video encoding.
alignTo8 :: Int -> Int
alignTo8 n = Int.floor ((Int.toNumber n + 7.0) / 8.0) * 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get composition width.
compositionWidth :: CompositionSettings -> Int
compositionWidth (CompositionSettings s) = s.width

-- | Get composition height.
compositionHeight :: CompositionSettings -> Int
compositionHeight (CompositionSettings s) = s.height

-- | Get total frame count.
compositionFrameCount :: CompositionSettings -> Int
compositionFrameCount (CompositionSettings s) = s.frameCount

-- | Get frames per second.
compositionFps :: CompositionSettings -> FrameRate
compositionFps (CompositionSettings s) = s.fps

-- | Get total duration in seconds.
compositionDuration :: CompositionSettings -> Seconds
compositionDuration (CompositionSettings s) = s.duration
