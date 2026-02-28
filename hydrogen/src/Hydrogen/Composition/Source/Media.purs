-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // composition // source // media
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Media Sources — Image, Video, Audio, SVG.
-- |
-- | Static and temporal media assets that generate pixels.

module Hydrogen.Composition.Source.Media
  ( -- * Image
    ImageSpec
  , ImageFit(..)
  , image
  
  -- * Video
  , VideoSpec
  , video
  
  -- * Audio
  , AudioSpec
  , AudioVisualization(..)
  , audio
  
  -- * SVG
  , SVGSpec
  , svg
  
  -- * Depth/Normal Maps
  , DepthSpec
  , DepthVisualization(..)
  , depth
  , NormalSpec
  , NormalVisualization(..)
  , normal
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  )

import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Color.Opacity (Opacity)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // image
-- ═══════════════════════════════════════════════════════════════════════════════

-- | How an image fits within bounds.
data ImageFit
  = FitCover    -- Scale to cover, crop excess
  | FitContain  -- Scale to fit, letterbox
  | FitFill     -- Stretch to fill
  | FitNone     -- Original size, centered

derive instance eqImageFit :: Eq ImageFit

instance showImageFit :: Show ImageFit where
  show FitCover = "cover"
  show FitContain = "contain"
  show FitFill = "fill"
  show FitNone = "none"

-- | Image source specification.
type ImageSpec =
  { assetId :: String     -- Asset reference
  , fit :: ImageFit       -- How to fit in bounds
  , opacity :: Opacity    -- Layer opacity
  , cropTop :: Number     -- Crop percentages (0-1)
  , cropBottom :: Number
  , cropLeft :: Number
  , cropRight :: Number
  }

-- | Create an image source.
image :: String -> ImageFit -> Opacity -> ImageSpec
image assetId fit opacity =
  { assetId, fit, opacity
  , cropTop: 0.0, cropBottom: 0.0, cropLeft: 0.0, cropRight: 0.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // video
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Video source specification.
type VideoSpec =
  { assetId :: String     -- Video asset reference
  , fit :: ImageFit       -- How to fit in bounds
  , opacity :: Opacity
  , loop :: Boolean       -- Loop playback
  , startTime :: Number   -- Start offset (seconds)
  , playbackSpeed :: Number -- 1.0 = normal, 0.5 = half, 2.0 = double
  , frameBlending :: Boolean -- Smooth slow-mo
  }

-- | Create a video source.
video :: String -> ImageFit -> Opacity -> Boolean -> VideoSpec
video assetId fit opacity loop =
  { assetId, fit, opacity, loop
  , startTime: 0.0, playbackSpeed: 1.0, frameBlending: false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // audio
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Audio visualization style.
data AudioVisualization
  = AudioWaveform       -- Classic waveform
  | AudioSpectrum       -- Frequency bars
  | AudioCircular       -- Circular spectrum
  | AudioMirror         -- Mirrored waveform
  | AudioBars           -- Vertical bars
  | AudioParticles      -- Particle reactive

derive instance eqAudioVisualization :: Eq AudioVisualization

instance showAudioVisualization :: Show AudioVisualization where
  show AudioWaveform = "waveform"
  show AudioSpectrum = "spectrum"
  show AudioCircular = "circular"
  show AudioMirror = "mirror"
  show AudioBars = "bars"
  show AudioParticles = "particles"

-- | Audio source specification (visual representation of audio).
type AudioSpec =
  { assetId :: String
  , visualization :: AudioVisualization
  , color :: RGB
  , opacity :: Opacity
  , smoothing :: Number   -- 0-1, temporal smoothing
  , sensitivity :: Number -- Audio reactivity
  }

-- | Create an audio visualization source.
audio :: String -> AudioVisualization -> RGB -> Opacity -> AudioSpec
audio assetId visualization color opacity =
  { assetId, visualization, color, opacity
  , smoothing: 0.5, sensitivity: 1.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                          // svg
-- ═══════════════════════════════════════════════════════════════════════════════

-- | SVG source specification.
type SVGSpec =
  { content :: String     -- SVG content or asset reference
  , opacity :: Opacity
  , preserveAspect :: Boolean
  }

-- | Create an SVG source.
svg :: String -> Opacity -> SVGSpec
svg content opacity = { content, opacity, preserveAspect: true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // depth / normal
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Depth map visualization mode.
data DepthVisualization
  = DepthGrayscale    -- Standard grayscale
  | DepthColormap     -- Colored by depth
  | DepthContour      -- Contour lines
  | DepthMesh         -- 3D mesh preview

derive instance eqDepthVisualization :: Eq DepthVisualization

instance showDepthVisualization :: Show DepthVisualization where
  show DepthGrayscale = "grayscale"
  show DepthColormap = "colormap"
  show DepthContour = "contour"
  show DepthMesh = "mesh"

-- | Depth map source.
type DepthSpec =
  { assetId :: String
  , visualization :: DepthVisualization
  , opacity :: Opacity
  , nearClip :: Number    -- Depth range
  , farClip :: Number
  }

-- | Create a depth map source.
depth :: String -> DepthVisualization -> Opacity -> DepthSpec
depth assetId visualization opacity =
  { assetId, visualization, opacity, nearClip: 0.0, farClip: 1.0 }

-- | Normal map visualization mode.
data NormalVisualization
  = NormalRGB         -- Direct RGB display
  | NormalHemisphere  -- Hemisphere coloring
  | NormalArrows      -- Arrow field
  | NormalLit         -- Lit preview

derive instance eqNormalVisualization :: Eq NormalVisualization

instance showNormalVisualization :: Show NormalVisualization where
  show NormalRGB = "rgb"
  show NormalHemisphere = "hemisphere"
  show NormalArrows = "arrows"
  show NormalLit = "lit"

-- | Normal map source.
type NormalSpec =
  { assetId :: String
  , visualization :: NormalVisualization
  , opacity :: Opacity
  }

-- | Create a normal map source.
normal :: String -> NormalVisualization -> Opacity -> NormalSpec
normal assetId visualization opacity = { assetId, visualization, opacity }
