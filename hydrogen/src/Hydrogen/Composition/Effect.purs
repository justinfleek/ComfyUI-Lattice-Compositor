-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // composition // effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Effect Stack — Visual effects applied to composition layers.
-- |
-- | Effects modify pixels after source generation, before blending.
-- | They stack in order: first effect processes source, second processes
-- | result of first, etc.
-- |
-- | ## Categories
-- |
-- | - Blur/Sharpen: Gaussian, Directional, Radial, Box, Sharpen
-- | - Color: Brightness, Contrast, Hue/Sat, Curves, Levels, Tint
-- | - Distort: Warp, Displacement, Bulge, Pinch, Ripple, Twirl
-- | - Stylize: Glow, Shadow, Emboss, Edge, Posterize
-- | - Generate: Fill, Gradient, Noise overlay
-- | - Time: Echo, Freeze, Posterize Time
-- |
-- | All effect parameters are bounded to prevent invalid states.

module Hydrogen.Composition.Effect
  ( -- * Core Effect Type
    Effect(..)
  , EffectCategory(..)
  , effectCategory
  , effectLabel
  , categoryLabel
  
  -- * Blur/Sharpen
  , GaussianBlurSpec, gaussianBlur
  , DirectionalBlurSpec, directionalBlur
  , RadialBlurSpec, RadialBlurType(..), radialBlur
  , BoxBlurSpec, boxBlur
  , SharpenSpec, sharpen
  
  -- * Color Correction
  , BrightnessContrastSpec, brightnessContrast
  , HueSaturationSpec, hueSaturation
  , LevelsSpec, levels
  , CurvesSpec, CurvePoint, curves
  , ColorBalanceSpec, colorBalance
  , TintSpec, tint
  , VignetteSpec, vignette
  , ExposureSpec, exposure
  
  -- * Distort
  , DisplacementSpec, displacement
  , WarpSpec, WarpType(..), warp
  , BulgeSpec, bulge
  , RippleSpec, ripple
  , TwirlSpec, twirl
  
  -- * Stylize
  , GlowSpec, glow
  , DropShadowSpec, dropShadow
  , InnerShadowSpec, innerShadow
  , EmbossSpec, emboss
  , EdgeDetectSpec, EdgeDetectType(..), edgeDetect
  , PosterizeSpec, posterize
  
  -- * Noise/Grain
  , NoiseOverlaySpec, NoiseBlendMode(..), noiseOverlay
  , GrainSpec, grain
  
  -- * Stylize Effects
  , RGBSplitSpec, rgbSplit
  , ScanlinesSpec, scanlines
  , VHSSpec, vhs
  , GlitchSpec, glitch
  , PixelateSpec, pixelate
  , HalftoneSpec, halftone
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  )

import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // effect category
-- ═══════════════════════════════════════════════════════════════════════════════

data EffectCategory
  = CategoryBlur
  | CategoryColor
  | CategoryDistort
  | CategoryStylize
  | CategoryNoise
  | CategoryTime

derive instance eqEffectCategory :: Eq EffectCategory

instance showEffectCategory :: Show EffectCategory where
  show CategoryBlur = "blur"
  show CategoryColor = "color"
  show CategoryDistort = "distort"
  show CategoryStylize = "stylize"
  show CategoryNoise = "noise"
  show CategoryTime = "time"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // effect type
-- ═══════════════════════════════════════════════════════════════════════════════

data Effect
  -- Blur/Sharpen
  = EffectGaussianBlur GaussianBlurSpec
  | EffectDirectionalBlur DirectionalBlurSpec
  | EffectRadialBlur RadialBlurSpec
  | EffectBoxBlur BoxBlurSpec
  | EffectSharpen SharpenSpec
  -- Color
  | EffectBrightnessContrast BrightnessContrastSpec
  | EffectHueSaturation HueSaturationSpec
  | EffectLevels LevelsSpec
  | EffectCurves CurvesSpec
  | EffectColorBalance ColorBalanceSpec
  | EffectTint TintSpec
  | EffectVignette VignetteSpec
  | EffectExposure ExposureSpec
  -- Distort
  | EffectDisplacement DisplacementSpec
  | EffectWarp WarpSpec
  | EffectBulge BulgeSpec
  | EffectRipple RippleSpec
  | EffectTwirl TwirlSpec
  -- Stylize
  | EffectGlow GlowSpec
  | EffectDropShadow DropShadowSpec
  | EffectInnerShadow InnerShadowSpec
  | EffectEmboss EmbossSpec
  | EffectEdgeDetect EdgeDetectSpec
  | EffectPosterize PosterizeSpec
  -- Noise
  | EffectNoiseOverlay NoiseOverlaySpec
  | EffectGrain GrainSpec
  -- Stylize Effects
  | EffectRGBSplit RGBSplitSpec
  | EffectScanlines ScanlinesSpec
  | EffectVHS VHSSpec
  | EffectGlitch GlitchSpec
  | EffectPixelate PixelateSpec
  | EffectHalftone HalftoneSpec

derive instance eqEffect :: Eq Effect

instance showEffect :: Show Effect where
  show (EffectGaussianBlur _) = "GaussianBlur"
  show (EffectDirectionalBlur _) = "DirectionalBlur"
  show (EffectRadialBlur _) = "RadialBlur"
  show (EffectBoxBlur _) = "BoxBlur"
  show (EffectSharpen _) = "Sharpen"
  show (EffectBrightnessContrast _) = "BrightnessContrast"
  show (EffectHueSaturation _) = "HueSaturation"
  show (EffectLevels _) = "Levels"
  show (EffectCurves _) = "Curves"
  show (EffectColorBalance _) = "ColorBalance"
  show (EffectTint _) = "Tint"
  show (EffectVignette _) = "Vignette"
  show (EffectExposure _) = "Exposure"
  show (EffectDisplacement _) = "Displacement"
  show (EffectWarp _) = "Warp"
  show (EffectBulge _) = "Bulge"
  show (EffectRipple _) = "Ripple"
  show (EffectTwirl _) = "Twirl"
  show (EffectGlow _) = "Glow"
  show (EffectDropShadow _) = "DropShadow"
  show (EffectInnerShadow _) = "InnerShadow"
  show (EffectEmboss _) = "Emboss"
  show (EffectEdgeDetect _) = "EdgeDetect"
  show (EffectPosterize _) = "Posterize"
  show (EffectNoiseOverlay _) = "NoiseOverlay"
  show (EffectGrain _) = "Grain"
  show (EffectRGBSplit _) = "RGBSplit"
  show (EffectScanlines _) = "Scanlines"
  show (EffectVHS _) = "VHS"
  show (EffectGlitch _) = "Glitch"
  show (EffectPixelate _) = "Pixelate"
  show (EffectHalftone _) = "Halftone"

effectCategory :: Effect -> EffectCategory
effectCategory (EffectGaussianBlur _) = CategoryBlur
effectCategory (EffectDirectionalBlur _) = CategoryBlur
effectCategory (EffectRadialBlur _) = CategoryBlur
effectCategory (EffectBoxBlur _) = CategoryBlur
effectCategory (EffectSharpen _) = CategoryBlur
effectCategory (EffectBrightnessContrast _) = CategoryColor
effectCategory (EffectHueSaturation _) = CategoryColor
effectCategory (EffectLevels _) = CategoryColor
effectCategory (EffectCurves _) = CategoryColor
effectCategory (EffectColorBalance _) = CategoryColor
effectCategory (EffectTint _) = CategoryColor
effectCategory (EffectVignette _) = CategoryColor
effectCategory (EffectExposure _) = CategoryColor
effectCategory (EffectDisplacement _) = CategoryDistort
effectCategory (EffectWarp _) = CategoryDistort
effectCategory (EffectBulge _) = CategoryDistort
effectCategory (EffectRipple _) = CategoryDistort
effectCategory (EffectTwirl _) = CategoryDistort
effectCategory (EffectGlow _) = CategoryStylize
effectCategory (EffectDropShadow _) = CategoryStylize
effectCategory (EffectInnerShadow _) = CategoryStylize
effectCategory (EffectEmboss _) = CategoryStylize
effectCategory (EffectEdgeDetect _) = CategoryStylize
effectCategory (EffectPosterize _) = CategoryStylize
effectCategory (EffectNoiseOverlay _) = CategoryNoise
effectCategory (EffectGrain _) = CategoryNoise
effectCategory (EffectRGBSplit _) = CategoryStylize
effectCategory (EffectScanlines _) = CategoryStylize
effectCategory (EffectVHS _) = CategoryStylize
effectCategory (EffectGlitch _) = CategoryStylize
effectCategory (EffectPixelate _) = CategoryStylize
effectCategory (EffectHalftone _) = CategoryStylize

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // blur / sharpen
-- ═══════════════════════════════════════════════════════════════════════════════

type GaussianBlurSpec =
  { radius :: Number      -- 0-500 pixels
  , quality :: Int        -- 1-5 (iterations)
  }

gaussianBlur :: Number -> Effect
gaussianBlur radius = EffectGaussianBlur
  { radius: Bounded.clampNumber 0.0 500.0 radius
  , quality: 3 }

type DirectionalBlurSpec =
  { angle :: Number       -- 0-360 degrees
  , distance :: Number    -- 0-500 pixels
  }

directionalBlur :: Number -> Number -> Effect
directionalBlur angle distance = EffectDirectionalBlur
  { angle: Bounded.clampNumber 0.0 360.0 angle
  , distance: Bounded.clampNumber 0.0 500.0 distance }

data RadialBlurType = RadialSpin | RadialZoom

derive instance eqRadialBlurType :: Eq RadialBlurType

instance showRadialBlurType :: Show RadialBlurType where
  show RadialSpin = "spin"
  show RadialZoom = "zoom"

type RadialBlurSpec =
  { blurType :: RadialBlurType
  , amount :: Number      -- 0-100
  , centerX :: Number     -- 0-1 (normalized)
  , centerY :: Number     -- 0-1
  }

radialBlur :: RadialBlurType -> Number -> Effect
radialBlur blurType amount = EffectRadialBlur
  { blurType
  , amount: Bounded.clampNumber 0.0 100.0 amount
  , centerX: 0.5, centerY: 0.5 }

type BoxBlurSpec =
  { radiusX :: Number     -- 0-500
  , radiusY :: Number     -- 0-500
  }

boxBlur :: Number -> Number -> Effect
boxBlur radiusX radiusY = EffectBoxBlur
  { radiusX: Bounded.clampNumber 0.0 500.0 radiusX
  , radiusY: Bounded.clampNumber 0.0 500.0 radiusY }

type SharpenSpec =
  { amount :: Number      -- 0-500%
  , radius :: Number      -- 0-100
  , threshold :: Number   -- 0-255
  }

sharpen :: Number -> Effect
sharpen amount = EffectSharpen
  { amount: Bounded.clampNumber 0.0 500.0 amount
  , radius: 1.0, threshold: 0.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // color correction
-- ═══════════════════════════════════════════════════════════════════════════════

type BrightnessContrastSpec =
  { brightness :: Number  -- -100 to 100
  , contrast :: Number    -- -100 to 100
  }

brightnessContrast :: Number -> Number -> Effect
brightnessContrast b c = EffectBrightnessContrast
  { brightness: Bounded.clampNumber (negate 100.0) 100.0 b
  , contrast: Bounded.clampNumber (negate 100.0) 100.0 c }

type HueSaturationSpec =
  { hue :: Number         -- -180 to 180
  , saturation :: Number  -- -100 to 100
  , lightness :: Number   -- -100 to 100
  }

hueSaturation :: Number -> Number -> Number -> Effect
hueSaturation h s l = EffectHueSaturation
  { hue: Bounded.clampNumber (negate 180.0) 180.0 h
  , saturation: Bounded.clampNumber (negate 100.0) 100.0 s
  , lightness: Bounded.clampNumber (negate 100.0) 100.0 l }

type LevelsSpec =
  { inputBlack :: Number  -- 0-255
  , inputWhite :: Number  -- 0-255
  , gamma :: Number       -- 0.1-10
  , outputBlack :: Number -- 0-255
  , outputWhite :: Number -- 0-255
  }

levels :: Number -> Number -> Number -> Effect
levels inputBlack inputWhite gamma = EffectLevels
  { inputBlack: Bounded.clampNumber 0.0 255.0 inputBlack
  , inputWhite: Bounded.clampNumber 0.0 255.0 inputWhite
  , gamma: Bounded.clampNumber 0.1 10.0 gamma
  , outputBlack: 0.0, outputWhite: 255.0 }

type CurvePoint = { x :: Number, y :: Number }

type CurvesSpec =
  { master :: Array CurvePoint
  , red :: Array CurvePoint
  , green :: Array CurvePoint
  , blue :: Array CurvePoint
  }

curves :: Array CurvePoint -> Effect
curves master = EffectCurves
  { master, red: [], green: [], blue: [] }

type ColorBalanceSpec =
  { shadowsCyanRed :: Number      -- -100 to 100
  , shadowsMagentaGreen :: Number
  , shadowsYellowBlue :: Number
  , midtonesCyanRed :: Number
  , midtonesMagentaGreen :: Number
  , midtonesYellowBlue :: Number
  , highlightsCyanRed :: Number
  , highlightsMagentaGreen :: Number
  , highlightsYellowBlue :: Number
  }

colorBalance :: Number -> Number -> Number -> Effect
colorBalance cr mg yb = EffectColorBalance
  { shadowsCyanRed: 0.0, shadowsMagentaGreen: 0.0, shadowsYellowBlue: 0.0
  , midtonesCyanRed: Bounded.clampNumber (negate 100.0) 100.0 cr
  , midtonesMagentaGreen: Bounded.clampNumber (negate 100.0) 100.0 mg
  , midtonesYellowBlue: Bounded.clampNumber (negate 100.0) 100.0 yb
  , highlightsCyanRed: 0.0, highlightsMagentaGreen: 0.0, highlightsYellowBlue: 0.0 }

type TintSpec =
  { color :: RGB
  , amount :: Number      -- 0-100%
  }

tint :: RGB -> Number -> Effect
tint color amount = EffectTint
  { color, amount: Bounded.clampNumber 0.0 100.0 amount }

type VignetteSpec =
  { amount :: Number      -- 0-100
  , midpoint :: Number    -- 0-100
  , roundness :: Number   -- -100 to 100
  , feather :: Number     -- 0-100
  }

vignette :: Number -> Effect
vignette amount = EffectVignette
  { amount: Bounded.clampNumber 0.0 100.0 amount
  , midpoint: 50.0, roundness: 0.0, feather: 50.0 }

type ExposureSpec =
  { exposure :: Number    -- -5 to 5 stops
  , offset :: Number      -- -1 to 1
  , gamma :: Number       -- 0.1 to 10
  }

exposure :: Number -> Effect
exposure e = EffectExposure
  { exposure: Bounded.clampNumber (negate 5.0) 5.0 e
  , offset: 0.0, gamma: 1.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // distort
-- ═══════════════════════════════════════════════════════════════════════════════

type DisplacementSpec =
  { mapSource :: String   -- Asset reference for displacement map
  , horizontalScale :: Number  -- -1000 to 1000
  , verticalScale :: Number
  }

displacement :: String -> Number -> Number -> Effect
displacement mapSource hScale vScale = EffectDisplacement
  { mapSource
  , horizontalScale: Bounded.clampNumber (negate 1000.0) 1000.0 hScale
  , verticalScale: Bounded.clampNumber (negate 1000.0) 1000.0 vScale }

data WarpType
  = WarpArc | WarpBulge | WarpFlag | WarpWave | WarpFish | WarpInflate

derive instance eqWarpType :: Eq WarpType

instance showWarpType :: Show WarpType where
  show WarpArc = "arc"
  show WarpBulge = "bulge"
  show WarpFlag = "flag"
  show WarpWave = "wave"
  show WarpFish = "fish"
  show WarpInflate = "inflate"

type WarpSpec =
  { warpType :: WarpType
  , bend :: Number        -- -100 to 100
  , horizontalDistortion :: Number
  , verticalDistortion :: Number
  }

warp :: WarpType -> Number -> Effect
warp warpType bend = EffectWarp
  { warpType
  , bend: Bounded.clampNumber (negate 100.0) 100.0 bend
  , horizontalDistortion: 0.0, verticalDistortion: 0.0 }

type BulgeSpec =
  { centerX :: Number     -- 0-1
  , centerY :: Number
  , radius :: Number      -- 0-1000
  , amount :: Number      -- -100 to 100
  }

bulge :: Number -> Number -> Effect
bulge radius amount = EffectBulge
  { centerX: 0.5, centerY: 0.5
  , radius: Bounded.clampNumber 0.0 1000.0 radius
  , amount: Bounded.clampNumber (negate 100.0) 100.0 amount }

type RippleSpec =
  { centerX :: Number
  , centerY :: Number
  , radius :: Number
  , wavelength :: Number  -- 1-500
  , amplitude :: Number   -- 0-500
  , phase :: Number       -- 0-360 (animatable)
  }

ripple :: Number -> Number -> Effect
ripple wavelength amplitude = EffectRipple
  { centerX: 0.5, centerY: 0.5, radius: 500.0
  , wavelength: Bounded.clampNumber 1.0 500.0 wavelength
  , amplitude: Bounded.clampNumber 0.0 500.0 amplitude
  , phase: 0.0 }

type TwirlSpec =
  { centerX :: Number
  , centerY :: Number
  , radius :: Number
  , angle :: Number       -- -3600 to 3600 degrees
  }

twirl :: Number -> Number -> Effect
twirl radius angle = EffectTwirl
  { centerX: 0.5, centerY: 0.5
  , radius: Bounded.clampNumber 0.0 2000.0 radius
  , angle: Bounded.clampNumber (negate 3600.0) 3600.0 angle }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // stylize
-- ═══════════════════════════════════════════════════════════════════════════════

type GlowSpec =
  { radius :: Number      -- 0-500
  , intensity :: Number   -- 0-500%
  , threshold :: Number   -- 0-100%
  , color :: RGB
  }

glow :: Number -> Number -> RGB -> Effect
glow radius intensity color = EffectGlow
  { radius: Bounded.clampNumber 0.0 500.0 radius
  , intensity: Bounded.clampNumber 0.0 500.0 intensity
  , threshold: 50.0, color }

type DropShadowSpec =
  { offsetX :: Number     -- -1000 to 1000
  , offsetY :: Number
  , blur :: Number        -- 0-500
  , spread :: Number      -- -100 to 100
  , color :: RGB
  , opacity :: Number     -- 0-100%
  }

dropShadow :: Number -> Number -> Number -> RGB -> Effect
dropShadow offsetX offsetY blur color = EffectDropShadow
  { offsetX: Bounded.clampNumber (negate 1000.0) 1000.0 offsetX
  , offsetY: Bounded.clampNumber (negate 1000.0) 1000.0 offsetY
  , blur: Bounded.clampNumber 0.0 500.0 blur
  , spread: 0.0, color, opacity: 75.0 }

type InnerShadowSpec =
  { offsetX :: Number
  , offsetY :: Number
  , blur :: Number
  , color :: RGB
  , opacity :: Number
  }

innerShadow :: Number -> Number -> Number -> RGB -> Effect
innerShadow offsetX offsetY blur color = EffectInnerShadow
  { offsetX: Bounded.clampNumber (negate 1000.0) 1000.0 offsetX
  , offsetY: Bounded.clampNumber (negate 1000.0) 1000.0 offsetY
  , blur: Bounded.clampNumber 0.0 500.0 blur
  , color, opacity: 75.0 }

type EmbossSpec =
  { angle :: Number       -- 0-360
  , height :: Number      -- 1-10
  , amount :: Number      -- 0-500%
  }

emboss :: Number -> Number -> Effect
emboss angle amount = EffectEmboss
  { angle: Bounded.clampNumber 0.0 360.0 angle
  , height: 3.0
  , amount: Bounded.clampNumber 0.0 500.0 amount }

data EdgeDetectType = EdgeCanny | EdgeSobel | EdgePrewitt | EdgeLaplacian

derive instance eqEdgeDetectType :: Eq EdgeDetectType

instance showEdgeDetectType :: Show EdgeDetectType where
  show EdgeCanny = "canny"
  show EdgeSobel = "sobel"
  show EdgePrewitt = "prewitt"
  show EdgeLaplacian = "laplacian"

type EdgeDetectSpec =
  { edgeType :: EdgeDetectType
  , threshold :: Number   -- 0-255
  , invert :: Boolean
  }

edgeDetect :: EdgeDetectType -> Number -> Effect
edgeDetect edgeType threshold = EffectEdgeDetect
  { edgeType, threshold: Bounded.clampNumber 0.0 255.0 threshold, invert: false }

type PosterizeSpec =
  { levels :: Int         -- 2-256
  }

posterize :: Int -> Effect
posterize lvls = EffectPosterize
  { levels: Bounded.clampInt 2 256 lvls }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // noise / grain
-- ═══════════════════════════════════════════════════════════════════════════════

data NoiseBlendMode = NoiseAdd | NoiseMultiply | NoiseScreen | NoiseOverlay

derive instance eqNoiseBlendMode :: Eq NoiseBlendMode

instance showNoiseBlendMode :: Show NoiseBlendMode where
  show NoiseAdd = "add"
  show NoiseMultiply = "multiply"
  show NoiseScreen = "screen"
  show NoiseOverlay = "overlay"

type NoiseOverlaySpec =
  { amount :: Number      -- 0-100%
  , blendMode :: NoiseBlendMode
  , monochrome :: Boolean
  , animated :: Boolean
  }

noiseOverlay :: Number -> NoiseBlendMode -> Effect
noiseOverlay amount blendMode = EffectNoiseOverlay
  { amount: Bounded.clampNumber 0.0 100.0 amount
  , blendMode, monochrome: true, animated: false }

type GrainSpec =
  { intensity :: Number   -- 0-100
  , size :: Number        -- 0.1-10
  , softness :: Number    -- 0-100
  , monochrome :: Boolean
  }

grain :: Number -> Number -> Effect
grain intensity size = EffectGrain
  { intensity: Bounded.clampNumber 0.0 100.0 intensity
  , size: Bounded.clampNumber 0.1 10.0 size
  , softness: 50.0, monochrome: true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // stylize effects
-- ═══════════════════════════════════════════════════════════════════════════════

type RGBSplitSpec =
  { redOffsetX :: Number
  , redOffsetY :: Number
  , blueOffsetX :: Number
  , blueOffsetY :: Number
  }

rgbSplit :: Number -> Number -> Effect
rgbSplit offsetX offsetY = EffectRGBSplit
  { redOffsetX: Bounded.clampNumber (negate 100.0) 100.0 offsetX
  , redOffsetY: Bounded.clampNumber (negate 100.0) 100.0 offsetY
  , blueOffsetX: Bounded.clampNumber (negate 100.0) 100.0 (negate offsetX)
  , blueOffsetY: Bounded.clampNumber (negate 100.0) 100.0 (negate offsetY) }

type ScanlinesSpec =
  { spacing :: Number     -- 1-100
  , thickness :: Number   -- 0.1-10
  , opacity :: Number     -- 0-100%
  , angle :: Number       -- 0-360
  }

scanlines :: Number -> Number -> Effect
scanlines spacing opacity = EffectScanlines
  { spacing: Bounded.clampNumber 1.0 100.0 spacing
  , thickness: 1.0
  , opacity: Bounded.clampNumber 0.0 100.0 opacity
  , angle: 0.0 }

type VHSSpec =
  { distortion :: Number  -- 0-100
  , noise :: Number       -- 0-100
  , colorBleed :: Number  -- 0-100
  , scanlines :: Boolean
  }

vhs :: Number -> Effect
vhs distortion = EffectVHS
  { distortion: Bounded.clampNumber 0.0 100.0 distortion
  , noise: 20.0, colorBleed: 30.0, scanlines: true }

type GlitchSpec =
  { intensity :: Number   -- 0-100
  , blockSize :: Number   -- 1-100
  , frequency :: Number   -- 0-100
  , rgbShift :: Boolean
  }

glitch :: Number -> Effect
glitch intensity = EffectGlitch
  { intensity: Bounded.clampNumber 0.0 100.0 intensity
  , blockSize: 20.0, frequency: 50.0, rgbShift: true }

type PixelateSpec =
  { blockWidth :: Number  -- 1-500
  , blockHeight :: Number -- 1-500
  }

pixelate :: Number -> Effect
pixelate size = EffectPixelate
  { blockWidth: Bounded.clampNumber 1.0 500.0 size
  , blockHeight: Bounded.clampNumber 1.0 500.0 size }

type HalftoneSpec =
  { dotSize :: Number     -- 1-100
  , angle :: Number       -- 0-360
  , shape :: String       -- "circle", "square", "line"
  }

halftone :: Number -> Effect
halftone dotSize = EffectHalftone
  { dotSize: Bounded.clampNumber 1.0 100.0 dotSize
  , angle: 45.0, shape: "circle" }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get display label for an effect.
effectLabel :: Effect -> String
effectLabel = show

-- | Get display label for an effect category.
categoryLabel :: EffectCategory -> String
categoryLabel = show
