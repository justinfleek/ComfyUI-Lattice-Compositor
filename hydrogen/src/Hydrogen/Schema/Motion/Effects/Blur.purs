-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // effects // blur
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blur Effects — Complete blur effect types for motion graphics.
-- |
-- | ## After Effects Parity
-- |
-- | Includes full property records for:
-- | - Gaussian Blur
-- | - Box Blur
-- | - Fast Blur
-- | - Directional Blur
-- | - Radial Blur
-- | - Camera Lens Blur
-- | - Compound Blur
-- | - Bilateral Blur (edge-preserving)
-- | - Smart Blur (edge-preserving, simplified)
-- | - Channel Blur (per-channel)
-- | - Sharpen
-- | - Unsharp Mask
-- |
-- | All blur amounts are in pixels.

module Hydrogen.Schema.Motion.Effects.Blur
  ( -- * Blur Dimension
    BlurDimension(..)
  , allBlurDimensions
  , blurDimensionToString
  , blurDimensionFromString
  
  -- * Radial Blur Type
  , RadialBlurType(..)
  , allRadialBlurTypes
  , radialBlurTypeToString
  , radialBlurTypeFromString
  
  -- * Antialiasing Quality
  , AntialiasingQuality(..)
  , allAntialiasingQualities
  , antialiasingQualityToString
  , antialiasingQualityFromString
  
  -- * Gaussian Blur
  , GaussianBlurEffect(..)
  , defaultGaussianBlur
  , mkGaussianBlur
  
  -- * Box Blur
  , BoxBlurEffect(..)
  , defaultBoxBlur
  , mkBoxBlur
  
  -- * Directional Blur
  , DirectionalBlurEffect(..)
  , defaultDirectionalBlur
  , mkDirectionalBlur
  
  -- * Radial Blur
  , RadialBlurEffect(..)
  , defaultRadialBlur
  , mkRadialBlur
  
  -- * Camera Lens Blur
  , CameraLensBlurEffect(..)
  , IrisShape(..)
  , DepthMapChannel(..)
  , defaultCameraLensBlur
  , mkCameraLensBlur
  , irisShapeToString
  , irisShapeFromString
  
  -- * Compound Blur
  , CompoundBlurEffect(..)
  , defaultCompoundBlur
  , mkCompoundBlur
  
  -- * Fast Blur (legacy)
  , FastBlurEffect(..)
  , defaultFastBlur
  , mkFastBlur
  
  -- * Bilateral Blur (edge-preserving)
  , BilateralBlurEffect(..)
  , defaultBilateralBlur
  , mkBilateralBlur
  
  -- * Smart Blur
  , SmartBlurEffect(..)
  , SmartBlurMode(..)
  , SmartBlurQuality(..)
  , defaultSmartBlur
  , mkSmartBlur
  
  -- * Channel Blur
  , ChannelBlurEffect(..)
  , defaultChannelBlur
  , mkChannelBlur
  
  -- * Sharpen
  , SharpenEffect(..)
  , defaultSharpen
  , mkSharpen
  
  -- * Unsharp Mask
  , UnsharpMaskEffect(..)
  , defaultUnsharpMask
  , mkUnsharpMask
  
  -- * Queries
  , isGaussianNeutral
  , isBoxNeutral
  , isDirectionalNeutral
  , isRadialNeutral
  , isCameraLensNeutral
  , isBilateralNeutral
  , isSmartBlurNeutral
  , isChannelBlurNeutral
  , isSharpenNeutral
  , isUnsharpMaskNeutral
  
  -- * Serialization
  , gaussianBlurToString
  , boxBlurToString
  , directionalBlurToString
  , radialBlurToString
  , bilateralBlurToString
  , channelBlurToString
  , sharpenToString
  , unsharpMaskToString
  
  -- * Comparisons
  , compareBlurIntensity
  , isStrongerBlur
  , isWeakerBlur
  
  -- * Composition
  , combineGaussianBlurs
  , negateDirectionalBlur
  , invertChannelBlur
  
  -- * Validation
  , BlurValidationError(..)
  , validateGaussianBlur
  , validateBoxBlur
  , validateRadialBlur
  , validateCameraLensBlur
  
  -- * Scaling
  , scaleGaussianBlur
  , scaleDirectionalBlur
  
  -- * Transitions
  , lerpGaussianBlur
  , lerpDirectionalBlur
  
  -- * Predicates
  , hasVisibleBlur
  , hasChannelDifference
  , isUniformChannelBlur
  
  -- * Batch Operations
  , validateAllGaussianBlurs
  , applyToAllChannels
  , normalizeChannelBlur
  
  -- * Functor Operations
  , mapBlurAmount
  , mapChannelBlurs
  
  -- * Combinable Blur (Semigroup)
  , CombinableGaussian(..)
  , toCombinableGaussian
  , fromCombinableGaussian
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , show
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , compare
  , map
  , pure
  , bind
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Ordering (Ordering)
import Data.Foldable (foldl)
import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // blur // dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction of blur effect.
data BlurDimension
  = BDHorizontal  -- ^ Blur only horizontally
  | BDVertical    -- ^ Blur only vertically
  | BDBoth        -- ^ Blur in both directions

derive instance eqBlurDimension :: Eq BlurDimension
derive instance ordBlurDimension :: Ord BlurDimension

instance showBlurDimension :: Show BlurDimension where
  show BDHorizontal = "BDHorizontal"
  show BDVertical = "BDVertical"
  show BDBoth = "BDBoth"

-- | All blur dimensions for enumeration
allBlurDimensions :: Array BlurDimension
allBlurDimensions = [ BDHorizontal, BDVertical, BDBoth ]

blurDimensionToString :: BlurDimension -> String
blurDimensionToString BDHorizontal = "horizontal"
blurDimensionToString BDVertical = "vertical"
blurDimensionToString BDBoth = "both"

blurDimensionFromString :: String -> Maybe BlurDimension
blurDimensionFromString "horizontal" = Just BDHorizontal
blurDimensionFromString "vertical" = Just BDVertical
blurDimensionFromString "both" = Just BDBoth
blurDimensionFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // radial // blur // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of radial blur.
data RadialBlurType
  = RBTSpin   -- ^ Rotational blur around center
  | RBTZoom   -- ^ Zoom blur from center

derive instance eqRadialBlurType :: Eq RadialBlurType
derive instance ordRadialBlurType :: Ord RadialBlurType

instance showRadialBlurType :: Show RadialBlurType where
  show RBTSpin = "RBTSpin"
  show RBTZoom = "RBTZoom"

-- | All radial blur types for enumeration
allRadialBlurTypes :: Array RadialBlurType
allRadialBlurTypes = [ RBTSpin, RBTZoom ]

radialBlurTypeToString :: RadialBlurType -> String
radialBlurTypeToString RBTSpin = "spin"
radialBlurTypeToString RBTZoom = "zoom"

radialBlurTypeFromString :: String -> Maybe RadialBlurType
radialBlurTypeFromString "spin" = Just RBTSpin
radialBlurTypeFromString "zoom" = Just RBTZoom
radialBlurTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // antialiasing // quality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Antialiasing quality level.
data AntialiasingQuality
  = AAQLow     -- ^ Fast, lower quality
  | AAQMedium  -- ^ Balanced
  | AAQHigh    -- ^ Best quality, slower

derive instance eqAntialiasingQuality :: Eq AntialiasingQuality
derive instance ordAntialiasingQuality :: Ord AntialiasingQuality

instance showAntialiasingQuality :: Show AntialiasingQuality where
  show AAQLow = "AAQLow"
  show AAQMedium = "AAQMedium"
  show AAQHigh = "AAQHigh"

-- | All antialiasing quality levels for enumeration
allAntialiasingQualities :: Array AntialiasingQuality
allAntialiasingQualities = [ AAQLow, AAQMedium, AAQHigh ]

antialiasingQualityToString :: AntialiasingQuality -> String
antialiasingQualityToString AAQLow = "low"
antialiasingQualityToString AAQMedium = "medium"
antialiasingQualityToString AAQHigh = "high"

antialiasingQualityFromString :: String -> Maybe AntialiasingQuality
antialiasingQualityFromString "low" = Just AAQLow
antialiasingQualityFromString "medium" = Just AAQMedium
antialiasingQualityFromString "high" = Just AAQHigh
antialiasingQualityFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // gaussian // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gaussian Blur effect — smooth, bell-curve weighted blur.
-- |
-- | Properties:
-- | - blurriness: Blur radius in pixels (0-1000)
-- | - dimensions: Horizontal, Vertical, or Both
-- | - repeatEdgePixels: Prevents edge transparency
type GaussianBlurEffect =
  { blurriness :: Number         -- ^ Blur radius in pixels (0-1000)
  , dimensions :: BlurDimension  -- ^ Direction of blur
  , repeatEdgePixels :: Boolean  -- ^ Extend edge pixels to avoid transparency
  }

defaultGaussianBlur :: GaussianBlurEffect
defaultGaussianBlur =
  { blurriness: 0.0
  , dimensions: BDBoth
  , repeatEdgePixels: true
  }

mkGaussianBlur :: Number -> BlurDimension -> Boolean -> GaussianBlurEffect
mkGaussianBlur blur dim repeat =
  { blurriness: clampNumber 0.0 1000.0 blur
  , dimensions: dim
  , repeatEdgePixels: repeat
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // box // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Box Blur effect — uniform-weighted rectangular blur.
-- |
-- | Faster than Gaussian but produces harsher edges.
-- | Multiple iterations approach Gaussian quality.
type BoxBlurEffect =
  { blurRadius :: Number         -- ^ Blur radius in pixels (0-1000)
  , iterations :: Int            -- ^ Number of passes (1-10)
  , dimensions :: BlurDimension  -- ^ Direction of blur
  , repeatEdgePixels :: Boolean  -- ^ Extend edge pixels
  }

defaultBoxBlur :: BoxBlurEffect
defaultBoxBlur =
  { blurRadius: 0.0
  , iterations: 1
  , dimensions: BDBoth
  , repeatEdgePixels: true
  }

mkBoxBlur :: Number -> Int -> BlurDimension -> Boolean -> BoxBlurEffect
mkBoxBlur radius iter dim repeat =
  { blurRadius: clampNumber 0.0 1000.0 radius
  , iterations: clampInt 1 10 iter
  , dimensions: dim
  , repeatEdgePixels: repeat
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // directional // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Directional Blur effect — motion blur along a specific angle.
-- |
-- | Simulates motion blur from camera or object movement.
type DirectionalBlurEffect =
  { direction :: Number  -- ^ Blur angle in degrees (0-360)
  , blurLength :: Number -- ^ Length of blur in pixels (0-1000)
  }

defaultDirectionalBlur :: DirectionalBlurEffect
defaultDirectionalBlur =
  { direction: 0.0
  , blurLength: 0.0
  }

mkDirectionalBlur :: Number -> Number -> DirectionalBlurEffect
mkDirectionalBlur dir len =
  { direction: wrapAngle dir
  , blurLength: clampNumber 0.0 1000.0 len
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // radial // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radial Blur effect — spin or zoom blur around a center point.
type RadialBlurEffect =
  { amount :: Number              -- ^ Blur intensity (0-100)
  , centerX :: Number             -- ^ Center X position (0-1 normalized)
  , centerY :: Number             -- ^ Center Y position (0-1 normalized)
  , blurType :: RadialBlurType    -- ^ Spin or Zoom
  , quality :: AntialiasingQuality -- ^ Render quality
  }

defaultRadialBlur :: RadialBlurEffect
defaultRadialBlur =
  { amount: 0.0
  , centerX: 0.5
  , centerY: 0.5
  , blurType: RBTSpin
  , quality: AAQHigh
  }

mkRadialBlur :: Number -> Number -> Number -> RadialBlurType -> AntialiasingQuality -> RadialBlurEffect
mkRadialBlur amt cx cy bt qual =
  { amount: clampNumber 0.0 100.0 amt
  , centerX: clampNumber 0.0 1.0 cx
  , centerY: clampNumber 0.0 1.0 cy
  , blurType: bt
  , quality: qual
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // iris // shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Iris shape for camera lens blur (bokeh shape).
data IrisShape
  = IrisTriangle     -- ^ 3-sided
  | IrisSquare       -- ^ 4-sided
  | IrisPentagon     -- ^ 5-sided
  | IrisHexagon      -- ^ 6-sided (most common)
  | IrisHeptagon     -- ^ 7-sided
  | IrisOctagon      -- ^ 8-sided
  | IrisDecagon      -- ^ 10-sided
  | IrisCircle       -- ^ Perfect circle (infinite sides)

derive instance eqIrisShape :: Eq IrisShape
derive instance ordIrisShape :: Ord IrisShape

instance showIrisShape :: Show IrisShape where
  show IrisTriangle = "Triangle"
  show IrisSquare = "Square"
  show IrisPentagon = "Pentagon"
  show IrisHexagon = "Hexagon"
  show IrisHeptagon = "Heptagon"
  show IrisOctagon = "Octagon"
  show IrisDecagon = "Decagon"
  show IrisCircle = "Circle"

irisShapeToString :: IrisShape -> String
irisShapeToString = show

irisShapeFromString :: String -> Maybe IrisShape
irisShapeFromString "Triangle" = Just IrisTriangle
irisShapeFromString "Square" = Just IrisSquare
irisShapeFromString "Pentagon" = Just IrisPentagon
irisShapeFromString "Hexagon" = Just IrisHexagon
irisShapeFromString "Heptagon" = Just IrisHeptagon
irisShapeFromString "Octagon" = Just IrisOctagon
irisShapeFromString "Decagon" = Just IrisDecagon
irisShapeFromString "Circle" = Just IrisCircle
irisShapeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // camera lens // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera Lens Blur effect — realistic depth-of-field blur.
-- |
-- | Simulates optical lens bokeh with iris shape control.
type CameraLensBlurEffect =
  { blurRadius :: Number          -- ^ Blur amount in pixels (0-500)
  , irisShape :: IrisShape        -- ^ Shape of out-of-focus highlights
  , irisRotation :: Number        -- ^ Rotation of iris shape in degrees (0-360)
  , irisRoundness :: Number       -- ^ Roundness of iris (0-100, 100 = circle)
  , irisAspectRatio :: Number     -- ^ Aspect ratio (0.5-2.0)
  , irisDiffractionFringe :: Number  -- ^ Edge fringing (0-100)
  , highlightGain :: Number       -- ^ Boost bright areas (0-100)
  , highlightThreshold :: Number  -- ^ Threshold for highlight boost (0-255)
  , highlightSaturation :: Number -- ^ Saturation of highlights (0-100)
  , useDepthMap :: Boolean        -- ^ Use depth map for variable blur
  , depthMapChannel :: DepthMapChannel -- ^ Which channel for depth
  , blurFocalDistance :: Number   -- ^ Focal distance when using depth map (0-100)
  }

-- | Depth map channel selection.
data DepthMapChannel
  = DepthLuminance   -- ^ Use luminance
  | DepthRed         -- ^ Use red channel
  | DepthGreen       -- ^ Use green channel
  | DepthBlue        -- ^ Use blue channel
  | DepthAlpha       -- ^ Use alpha channel

derive instance eqDepthMapChannel :: Eq DepthMapChannel
derive instance ordDepthMapChannel :: Ord DepthMapChannel

instance showDepthMapChannel :: Show DepthMapChannel where
  show DepthLuminance = "Luminance"
  show DepthRed = "Red"
  show DepthGreen = "Green"
  show DepthBlue = "Blue"
  show DepthAlpha = "Alpha"

defaultCameraLensBlur :: CameraLensBlurEffect
defaultCameraLensBlur =
  { blurRadius: 0.0
  , irisShape: IrisHexagon
  , irisRotation: 0.0
  , irisRoundness: 0.0
  , irisAspectRatio: 1.0
  , irisDiffractionFringe: 0.0
  , highlightGain: 0.0
  , highlightThreshold: 255.0
  , highlightSaturation: 100.0
  , useDepthMap: false
  , depthMapChannel: DepthLuminance
  , blurFocalDistance: 0.0
  }

mkCameraLensBlur :: Number -> IrisShape -> Number -> Number -> CameraLensBlurEffect
mkCameraLensBlur radius shape rotation roundness =
  { blurRadius: clampNumber 0.0 500.0 radius
  , irisShape: shape
  , irisRotation: wrapAngle rotation
  , irisRoundness: clampNumber 0.0 100.0 roundness
  , irisAspectRatio: 1.0
  , irisDiffractionFringe: 0.0
  , highlightGain: 0.0
  , highlightThreshold: 255.0
  , highlightSaturation: 100.0
  , useDepthMap: false
  , depthMapChannel: DepthLuminance
  , blurFocalDistance: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // compound // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compound Blur effect — variable blur based on a control layer.
-- |
-- | Uses another layer's luminance to control blur amount per-pixel.
type CompoundBlurEffect =
  { maxBlur :: Number             -- ^ Maximum blur amount (0-500)
  , stretchMapToFit :: Boolean    -- ^ Stretch blur map to layer size
  , invertBlur :: Boolean         -- ^ Invert blur map values
  }

defaultCompoundBlur :: CompoundBlurEffect
defaultCompoundBlur =
  { maxBlur: 20.0
  , stretchMapToFit: true
  , invertBlur: false
  }

mkCompoundBlur :: Number -> Boolean -> Boolean -> CompoundBlurEffect
mkCompoundBlur maxB stretch invert =
  { maxBlur: clampNumber 0.0 500.0 maxB
  , stretchMapToFit: stretch
  , invertBlur: invert
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // fast // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fast Blur effect — legacy blur for performance.
-- |
-- | Similar to Gaussian but optimized for speed.
type FastBlurEffect =
  { blurriness :: Number         -- ^ Blur amount (0-1000)
  , dimensions :: BlurDimension  -- ^ Direction
  , repeatEdgePixels :: Boolean  -- ^ Edge handling
  }

defaultFastBlur :: FastBlurEffect
defaultFastBlur =
  { blurriness: 0.0
  , dimensions: BDBoth
  , repeatEdgePixels: true
  }

mkFastBlur :: Number -> BlurDimension -> Boolean -> FastBlurEffect
mkFastBlur blur dim repeat =
  { blurriness: clampNumber 0.0 1000.0 blur
  , dimensions: dim
  , repeatEdgePixels: repeat
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // bilateral // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bilateral Blur effect — edge-preserving blur.
-- |
-- | Selectively blurs image while preserving edges. Areas with high contrast
-- | are blurred less than low-contrast areas. Creates a softer, dreamier look
-- | than Smart Blur.
-- |
-- | AE Properties:
-- | - Radius: Size of blur kernel (0-100)
-- | - Threshold: Edge preservation threshold (0-100, lower = more edges preserved)
-- | - Colorize: When true, operates on RGB channels; when false, luminance only
type BilateralBlurEffect =
  { radius :: Number      -- ^ Blur kernel size in pixels (0-100)
  , threshold :: Number   -- ^ Edge preservation threshold (0-100)
  , colorize :: Boolean   -- ^ True = color, False = monochrome (luminance only)
  }

defaultBilateralBlur :: BilateralBlurEffect
defaultBilateralBlur =
  { radius: 5.0
  , threshold: 10.0
  , colorize: true
  }

mkBilateralBlur :: Number -> Number -> Boolean -> BilateralBlurEffect
mkBilateralBlur rad thresh color =
  { radius: clampNumber 0.0 100.0 rad
  , threshold: clampNumber 0.0 100.0 thresh
  , colorize: color
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // smart // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smart Blur mode.
data SmartBlurMode
  = SBMNormal      -- ^ Standard blur with edge preservation
  | SBMEdgeOnly    -- ^ Show only detected edges (white on black)
  | SBMOverlay     -- ^ Overlay edges on blurred result

derive instance eqSmartBlurMode :: Eq SmartBlurMode
derive instance ordSmartBlurMode :: Ord SmartBlurMode

instance showSmartBlurMode :: Show SmartBlurMode where
  show SBMNormal = "Normal"
  show SBMEdgeOnly = "Edge Only"
  show SBMOverlay = "Overlay Edge"

-- | Smart Blur quality.
data SmartBlurQuality
  = SBQLow     -- ^ Fast, lower quality
  | SBQMedium  -- ^ Balanced
  | SBQHigh    -- ^ Best quality

derive instance eqSmartBlurQuality :: Eq SmartBlurQuality
derive instance ordSmartBlurQuality :: Ord SmartBlurQuality

instance showSmartBlurQuality :: Show SmartBlurQuality where
  show SBQLow = "Low"
  show SBQMedium = "Medium"
  show SBQHigh = "High"

-- | Smart Blur effect — edge-preserving blur with edge detection.
-- |
-- | More aggressive edge preservation than Bilateral Blur.
-- | Can visualize detected edges.
-- |
-- | AE Properties:
-- | - Radius: Blur amount (0.1-100)
-- | - Threshold: Edge detection threshold (0.1-100)
-- | - Mode: Normal, Edge Only, or Overlay Edge
-- | - Quality: Low, Medium, High
type SmartBlurEffect =
  { radius :: Number           -- ^ Blur radius (0.1-100)
  , threshold :: Number        -- ^ Edge threshold (0.1-100)
  , mode :: SmartBlurMode      -- ^ Output mode
  , quality :: SmartBlurQuality -- ^ Render quality
  }

defaultSmartBlur :: SmartBlurEffect
defaultSmartBlur =
  { radius: 3.0
  , threshold: 25.0
  , mode: SBMNormal
  , quality: SBQMedium
  }

mkSmartBlur :: Number -> Number -> SmartBlurMode -> SmartBlurQuality -> SmartBlurEffect
mkSmartBlur rad thresh mode qual =
  { radius: clampNumber 0.1 100.0 rad
  , threshold: clampNumber 0.1 100.0 thresh
  , mode: mode
  , quality: qual
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // channel // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Channel Blur effect — independent blur per color channel.
-- |
-- | Allows different blur amounts for Red, Green, Blue, and Alpha channels.
-- | Useful for chromatic aberration effects or selective channel softening.
-- |
-- | AE Properties:
-- | - Red Blurriness: Red channel blur (0-500)
-- | - Green Blurriness: Green channel blur (0-500)
-- | - Blue Blurriness: Blue channel blur (0-500)
-- | - Alpha Blurriness: Alpha channel blur (0-500)
-- | - Edge Behavior: How to handle pixels beyond frame edges
-- | - Repeat Edge Pixels: Extend edge pixels to prevent transparency
type ChannelBlurEffect =
  { redBlurriness :: Number    -- ^ Red channel blur (0-500)
  , greenBlurriness :: Number  -- ^ Green channel blur (0-500)
  , blueBlurriness :: Number   -- ^ Blue channel blur (0-500)
  , alphaBlurriness :: Number  -- ^ Alpha channel blur (0-500)
  , repeatEdgePixels :: Boolean -- ^ Extend edge pixels
  , dimensions :: BlurDimension -- ^ Blur direction per channel
  }

defaultChannelBlur :: ChannelBlurEffect
defaultChannelBlur =
  { redBlurriness: 0.0
  , greenBlurriness: 0.0
  , blueBlurriness: 0.0
  , alphaBlurriness: 0.0
  , repeatEdgePixels: true
  , dimensions: BDBoth
  }

mkChannelBlur :: Number -> Number -> Number -> Number -> ChannelBlurEffect
mkChannelBlur r g b a =
  { redBlurriness: clampNumber 0.0 500.0 r
  , greenBlurriness: clampNumber 0.0 500.0 g
  , blueBlurriness: clampNumber 0.0 500.0 b
  , alphaBlurriness: clampNumber 0.0 500.0 a
  , repeatEdgePixels: true
  , dimensions: BDBoth
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // sharpen
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sharpen effect — basic sharpening.
-- |
-- | Increases contrast between adjacent pixels to enhance edges.
-- | Simple but effective for subtle sharpening.
-- |
-- | AE Properties:
-- | - Sharpen Amount: Intensity of sharpening (0-500)
type SharpenEffect =
  { sharpenAmount :: Number  -- ^ Sharpening intensity (0-500)
  }

defaultSharpen :: SharpenEffect
defaultSharpen =
  { sharpenAmount: 0.0
  }

mkSharpen :: Number -> SharpenEffect
mkSharpen amt =
  { sharpenAmount: clampNumber 0.0 500.0 amt
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // unsharp // mask
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unsharp Mask effect — professional sharpening with controls.
-- |
-- | Uses the classic unsharp masking technique: subtracts a blurred version
-- | of the image to enhance edges. More control than basic Sharpen.
-- |
-- | AE Properties:
-- | - Amount: Sharpening intensity as percentage (0-500%)
-- | - Radius: Size of sharpening halo in pixels (0.1-250)
-- | - Threshold: Minimum brightness change to sharpen (0-255)
-- |   Lower values sharpen more of the image including noise.
type UnsharpMaskEffect =
  { amount :: Number     -- ^ Sharpening intensity (0-500%)
  , radius :: Number     -- ^ Halo radius in pixels (0.1-250)
  , threshold :: Number  -- ^ Minimum contrast to sharpen (0-255)
  }

defaultUnsharpMask :: UnsharpMaskEffect
defaultUnsharpMask =
  { amount: 100.0
  , radius: 1.0
  , threshold: 0.0
  }

mkUnsharpMask :: Number -> Number -> Number -> UnsharpMaskEffect
mkUnsharpMask amt rad thresh =
  { amount: clampNumber 0.0 500.0 amt
  , radius: clampNumber 0.1 250.0 rad
  , threshold: clampNumber 0.0 255.0 thresh
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

isGaussianNeutral :: GaussianBlurEffect -> Boolean
isGaussianNeutral effect = effect.blurriness == 0.0

isBoxNeutral :: BoxBlurEffect -> Boolean
isBoxNeutral effect = effect.blurRadius == 0.0

isDirectionalNeutral :: DirectionalBlurEffect -> Boolean
isDirectionalNeutral effect = effect.blurLength == 0.0

isRadialNeutral :: RadialBlurEffect -> Boolean
isRadialNeutral effect = effect.amount == 0.0

isCameraLensNeutral :: CameraLensBlurEffect -> Boolean
isCameraLensNeutral effect = effect.blurRadius == 0.0

isBilateralNeutral :: BilateralBlurEffect -> Boolean
isBilateralNeutral effect = effect.radius == 0.0

isSmartBlurNeutral :: SmartBlurEffect -> Boolean
isSmartBlurNeutral effect = effect.radius == 0.0

isChannelBlurNeutral :: ChannelBlurEffect -> Boolean
isChannelBlurNeutral effect =
  effect.redBlurriness == 0.0 &&
  effect.greenBlurriness == 0.0 &&
  effect.blueBlurriness == 0.0 &&
  effect.alphaBlurriness == 0.0

isSharpenNeutral :: SharpenEffect -> Boolean
isSharpenNeutral effect = effect.sharpenAmount == 0.0

isUnsharpMaskNeutral :: UnsharpMaskEffect -> Boolean
isUnsharpMaskNeutral effect = effect.amount == 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Gaussian blur to readable string.
gaussianBlurToString :: GaussianBlurEffect -> String
gaussianBlurToString effect =
  "GaussianBlur(" <> show effect.blurriness <> "px, " <>
  blurDimensionToString effect.dimensions <> 
  (if not effect.repeatEdgePixels then ", no-repeat" else "") <> ")"

-- | Serialize Box blur to readable string.
boxBlurToString :: BoxBlurEffect -> String
boxBlurToString effect =
  "BoxBlur(" <> show effect.blurRadius <> "px, " <>
  show effect.iterations <> "x, " <>
  blurDimensionToString effect.dimensions <> ")"

-- | Serialize Directional blur to readable string.
directionalBlurToString :: DirectionalBlurEffect -> String
directionalBlurToString effect =
  "DirectionalBlur(" <> show effect.blurLength <> "px @ " <>
  show effect.direction <> "°)"

-- | Serialize Radial blur to readable string.
radialBlurToString :: RadialBlurEffect -> String
radialBlurToString effect =
  "RadialBlur(" <> show effect.amount <> "%, " <>
  radialBlurTypeToString effect.blurType <> ", center=" <>
  show effect.centerX <> "," <> show effect.centerY <> ")"

-- | Serialize Bilateral blur to readable string.
bilateralBlurToString :: BilateralBlurEffect -> String
bilateralBlurToString effect =
  "BilateralBlur(r=" <> show effect.radius <> ", thresh=" <>
  show effect.threshold <> 
  (if not effect.colorize then ", mono" else "") <> ")"

-- | Serialize Channel blur to readable string.
channelBlurToString :: ChannelBlurEffect -> String
channelBlurToString effect =
  "ChannelBlur(R=" <> show effect.redBlurriness <>
  ", G=" <> show effect.greenBlurriness <>
  ", B=" <> show effect.blueBlurriness <>
  ", A=" <> show effect.alphaBlurriness <> ")"

-- | Serialize Sharpen to readable string.
sharpenToString :: SharpenEffect -> String
sharpenToString effect =
  "Sharpen(" <> show effect.sharpenAmount <> ")"

-- | Serialize Unsharp Mask to readable string.
unsharpMaskToString :: UnsharpMaskEffect -> String
unsharpMaskToString effect =
  "UnsharpMask(" <> show effect.amount <> "%, r=" <>
  show effect.radius <> ", thresh=" <> show effect.threshold <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // comparisons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare blur intensity of two Gaussian blurs.
-- | Returns LT if first is weaker, GT if stronger, EQ if equal.
compareBlurIntensity :: GaussianBlurEffect -> GaussianBlurEffect -> Ordering
compareBlurIntensity a b = compare a.blurriness b.blurriness

-- | Check if first Gaussian blur is stronger than second.
isStrongerBlur :: GaussianBlurEffect -> GaussianBlurEffect -> Boolean
isStrongerBlur a b = a.blurriness > b.blurriness

-- | Check if first Gaussian blur is weaker than second.
isWeakerBlur :: GaussianBlurEffect -> GaussianBlurEffect -> Boolean
isWeakerBlur a b = a.blurriness < b.blurriness

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two Gaussian blurs by adding their blur amounts.
-- | Resulting blur is clamped to valid range.
combineGaussianBlurs :: GaussianBlurEffect -> GaussianBlurEffect -> GaussianBlurEffect
combineGaussianBlurs a b =
  { blurriness: clampNumber 0.0 1000.0 (a.blurriness + b.blurriness)
  , dimensions: combineDimensions a.dimensions b.dimensions
  , repeatEdgePixels: a.repeatEdgePixels || b.repeatEdgePixels
  }

-- | Combine blur dimensions - if either is Both, result is Both.
combineDimensions :: BlurDimension -> BlurDimension -> BlurDimension
combineDimensions BDBoth _ = BDBoth
combineDimensions _ BDBoth = BDBoth
combineDimensions BDHorizontal BDVertical = BDBoth
combineDimensions BDVertical BDHorizontal = BDBoth
combineDimensions a _ = a

-- | Negate directional blur - reverse the direction by 180°.
negateDirectionalBlur :: DirectionalBlurEffect -> DirectionalBlurEffect
negateDirectionalBlur effect =
  { direction: wrapAngle (effect.direction + 180.0)
  , blurLength: effect.blurLength
  }

-- | Invert channel blur - swap Red/Blue channels.
-- | Useful for correcting chromatic aberration direction.
invertChannelBlur :: ChannelBlurEffect -> ChannelBlurEffect
invertChannelBlur effect =
  { redBlurriness: effect.blueBlurriness
  , greenBlurriness: effect.greenBlurriness
  , blueBlurriness: effect.redBlurriness
  , alphaBlurriness: effect.alphaBlurriness
  , repeatEdgePixels: effect.repeatEdgePixels
  , dimensions: effect.dimensions
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validation errors for blur effects.
data BlurValidationError
  = BlurOutOfRange String Number Number Number  -- ^ field, value, min, max
  | InvalidIterations Int
  | InvalidCenter Number Number

derive instance eqBlurValidationError :: Eq BlurValidationError

instance showBlurValidationError :: Show BlurValidationError where
  show (BlurOutOfRange field val minV maxV) =
    field <> " value " <> show val <> " out of range [" <> 
    show minV <> ", " <> show maxV <> "]"
  show (InvalidIterations n) =
    "iterations " <> show n <> " must be between 1 and 10"
  show (InvalidCenter x y) =
    "center (" <> show x <> ", " <> show y <> ") must be in [0, 1]"

-- | Validate Gaussian blur parameters.
-- | Returns Nothing if valid, Just error if invalid.
validateGaussianBlur :: GaussianBlurEffect -> Maybe BlurValidationError
validateGaussianBlur effect
  | effect.blurriness < 0.0 = Just (BlurOutOfRange "blurriness" effect.blurriness 0.0 1000.0)
  | effect.blurriness > 1000.0 = Just (BlurOutOfRange "blurriness" effect.blurriness 0.0 1000.0)
  | otherwise = Nothing

-- | Validate Box blur parameters.
validateBoxBlur :: BoxBlurEffect -> Maybe BlurValidationError
validateBoxBlur effect
  | effect.blurRadius < 0.0 = Just (BlurOutOfRange "blurRadius" effect.blurRadius 0.0 1000.0)
  | effect.blurRadius > 1000.0 = Just (BlurOutOfRange "blurRadius" effect.blurRadius 0.0 1000.0)
  | effect.iterations < 1 = Just (InvalidIterations effect.iterations)
  | effect.iterations > 10 = Just (InvalidIterations effect.iterations)
  | otherwise = Nothing

-- | Validate Radial blur parameters.
validateRadialBlur :: RadialBlurEffect -> Maybe BlurValidationError
validateRadialBlur effect
  | effect.amount < 0.0 = Just (BlurOutOfRange "amount" effect.amount 0.0 100.0)
  | effect.amount > 100.0 = Just (BlurOutOfRange "amount" effect.amount 0.0 100.0)
  | effect.centerX < 0.0 = Just (InvalidCenter effect.centerX effect.centerY)
  | effect.centerX > 1.0 = Just (InvalidCenter effect.centerX effect.centerY)
  | effect.centerY < 0.0 = Just (InvalidCenter effect.centerX effect.centerY)
  | effect.centerY > 1.0 = Just (InvalidCenter effect.centerX effect.centerY)
  | otherwise = Nothing

-- | Validate Camera Lens blur parameters.
validateCameraLensBlur :: CameraLensBlurEffect -> Maybe BlurValidationError
validateCameraLensBlur effect
  | effect.blurRadius < 0.0 = Just (BlurOutOfRange "blurRadius" effect.blurRadius 0.0 500.0)
  | effect.blurRadius > 500.0 = Just (BlurOutOfRange "blurRadius" effect.blurRadius 0.0 500.0)
  | effect.irisRoundness < 0.0 = Just (BlurOutOfRange "irisRoundness" effect.irisRoundness 0.0 100.0)
  | effect.irisRoundness > 100.0 = Just (BlurOutOfRange "irisRoundness" effect.irisRoundness 0.0 100.0)
  | effect.irisAspectRatio < 0.5 = Just (BlurOutOfRange "irisAspectRatio" effect.irisAspectRatio 0.5 2.0)
  | effect.irisAspectRatio > 2.0 = Just (BlurOutOfRange "irisAspectRatio" effect.irisAspectRatio 0.5 2.0)
  | otherwise = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // scaling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale a Gaussian blur by a factor.
-- | Negative factors are negated (blur cannot be negative).
scaleGaussianBlur :: Number -> GaussianBlurEffect -> GaussianBlurEffect
scaleGaussianBlur factor effect =
  let scaleFactor = if factor < 0.0 then negate factor else factor
  in effect { blurriness = clampNumber 0.0 1000.0 (effect.blurriness * scaleFactor) }

-- | Scale a Directional blur by a factor.
-- | Negative factors reverse the direction.
scaleDirectionalBlur :: Number -> DirectionalBlurEffect -> DirectionalBlurEffect
scaleDirectionalBlur factor effect
  | factor < 0.0 = 
      { direction: wrapAngle (effect.direction + 180.0)
      , blurLength: clampNumber 0.0 1000.0 (effect.blurLength * negate factor)
      }
  | otherwise =
      { direction: effect.direction
      , blurLength: clampNumber 0.0 1000.0 (effect.blurLength * factor)
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two Gaussian blurs.
-- | t=0 returns from, t=1 returns to.
lerpGaussianBlur :: Number -> GaussianBlurEffect -> GaussianBlurEffect -> GaussianBlurEffect
lerpGaussianBlur t from to =
  let t' = clampNumber 0.0 1.0 t
  in { blurriness: lerpNum t' from.blurriness to.blurriness
     , dimensions: if t' <= 0.5 then from.dimensions else to.dimensions
     , repeatEdgePixels: if t' <= 0.5 then from.repeatEdgePixels else to.repeatEdgePixels
     }

-- | Linear interpolation between two Directional blurs.
lerpDirectionalBlur :: Number -> DirectionalBlurEffect -> DirectionalBlurEffect -> DirectionalBlurEffect
lerpDirectionalBlur t from to =
  let t' = clampNumber 0.0 1.0 t
  in { direction: lerpAngle t' from.direction to.direction
     , blurLength: lerpNum t' from.blurLength to.blurLength
     }

-- | Interpolate between two numbers.
lerpNum :: Number -> Number -> Number -> Number
lerpNum t a b = a + t * (b - a)

-- | Interpolate between two angles (shortest path).
lerpAngle :: Number -> Number -> Number -> Number
lerpAngle t from to =
  let diff = to - from
      -- Adjust for shortest path around circle
      adjustedDiff = 
        if diff > 180.0 then diff - 360.0
        else if diff < (-180.0) then diff + 360.0
        else diff
  in wrapAngle (from + t * adjustedDiff)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a Gaussian blur has visible effect.
-- | A blur is visible if amount is greater than a small threshold.
hasVisibleBlur :: GaussianBlurEffect -> Boolean
hasVisibleBlur effect = effect.blurriness >= 0.5

-- | Check if channel blur has different values per channel.
-- | Returns true if any channel differs from another.
hasChannelDifference :: ChannelBlurEffect -> Boolean
hasChannelDifference effect =
  effect.redBlurriness /= effect.greenBlurriness ||
  effect.greenBlurriness /= effect.blueBlurriness ||
  effect.blueBlurriness /= effect.alphaBlurriness

-- | Check if channel blur applies same blur to all channels.
isUniformChannelBlur :: ChannelBlurEffect -> Boolean
isUniformChannelBlur effect =
  effect.redBlurriness == effect.greenBlurriness &&
  effect.greenBlurriness == effect.blueBlurriness &&
  effect.blueBlurriness == effect.alphaBlurriness

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // batch operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate an array of Gaussian blur effects.
-- | Returns array of errors for any invalid effects.
validateAllGaussianBlurs :: Array GaussianBlurEffect -> Array BlurValidationError
validateAllGaussianBlurs effects = 
  bind effects (\effect -> 
    case validateGaussianBlur effect of
      Nothing -> []
      Just err -> pure err
  )

-- | Apply a transformation function to all channels of a channel blur.
applyToAllChannels :: (Number -> Number) -> ChannelBlurEffect -> ChannelBlurEffect
applyToAllChannels f effect =
  { redBlurriness: clampNumber 0.0 500.0 (f effect.redBlurriness)
  , greenBlurriness: clampNumber 0.0 500.0 (f effect.greenBlurriness)
  , blueBlurriness: clampNumber 0.0 500.0 (f effect.blueBlurriness)
  , alphaBlurriness: clampNumber 0.0 500.0 (f effect.alphaBlurriness)
  , repeatEdgePixels: effect.repeatEdgePixels
  , dimensions: effect.dimensions
  }

-- | Normalize channel blur so the maximum channel becomes 100.
-- | All other channels scale proportionally.
normalizeChannelBlur :: ChannelBlurEffect -> ChannelBlurEffect
normalizeChannelBlur effect =
  let channels = [effect.redBlurriness, effect.greenBlurriness, effect.blueBlurriness, effect.alphaBlurriness]
      maxVal = findMax channels
  in if maxVal == 0.0 
     then effect
     else applyToAllChannels (\x -> (x / maxVal) * 100.0) effect

-- | Find maximum in array.
findMax :: Array Number -> Number
findMax arr = foldl maxOf 0.0 arr
  where
  maxOf a b = if b > a then b else a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // functor operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map over blur amounts in an array of Gaussian effects.
-- | Applies a transformation function to each blur's blurriness.
mapBlurAmount :: (Number -> Number) -> Array GaussianBlurEffect -> Array GaussianBlurEffect
mapBlurAmount f effects = map (transformGaussianBlur f) effects
  where
  transformGaussianBlur :: (Number -> Number) -> GaussianBlurEffect -> GaussianBlurEffect
  transformGaussianBlur g effect = 
    effect { blurriness = clampNumber 0.0 1000.0 (g effect.blurriness) }

-- | Map a function over an array of channel blur effects.
mapChannelBlurs :: (ChannelBlurEffect -> ChannelBlurEffect) -> Array ChannelBlurEffect -> Array ChannelBlurEffect
mapChannelBlurs = map

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // combinable // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wrapper for Gaussian blur that can be combined with Semigroup.
-- |
-- | Combining two blurs:
-- | - Adds blur amounts (clamped to max 1000)
-- | - Takes the wider dimension (Both wins over Horizontal/Vertical)
-- | - Preserves edge repetition if either has it
-- |
-- | This allows: blur1 <> blur2 <> blur3 for accumulating blur effects.
newtype CombinableGaussian = CombinableGaussian GaussianBlurEffect

derive instance eqCombinableGaussian :: Eq CombinableGaussian

instance semigroupCombinableGaussian :: Semigroup CombinableGaussian where
  append (CombinableGaussian a) (CombinableGaussian b) =
    CombinableGaussian
      { blurriness: clampNumber 0.0 1000.0 (a.blurriness + b.blurriness)
      , dimensions: combineDimensions a.dimensions b.dimensions
      , repeatEdgePixels: a.repeatEdgePixels || b.repeatEdgePixels
      }

instance showCombinableGaussian :: Show CombinableGaussian where
  show (CombinableGaussian g) = "CombinableGaussian(" <> gaussianBlurToString g <> ")"

-- | Wrap a Gaussian blur for combination.
toCombinableGaussian :: GaussianBlurEffect -> CombinableGaussian
toCombinableGaussian = CombinableGaussian

-- | Unwrap a combined Gaussian blur.
fromCombinableGaussian :: CombinableGaussian -> GaussianBlurEffect
fromCombinableGaussian (CombinableGaussian g) = g

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp an Int to a range.
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal val
  | val < minVal = minVal
  | val > maxVal = maxVal
  | otherwise = val

-- | Wrap angle to 0-360 range.
wrapAngle :: Number -> Number
wrapAngle angle =
  let normalized = angle - 360.0 * floor (angle / 360.0)
  in if normalized < 0.0 then normalized + 360.0 else normalized

-- | Floor function for wrapping.
floor :: Number -> Number
floor x = 
  let truncated = if x >= 0.0 then x else x - 1.0
  in truncated - (truncated - x)
