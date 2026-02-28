-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // motion // effects // generate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate Effects — Procedural content generation effects.
-- |
-- | ## After Effects Parity
-- |
-- | Implements AE's Generate effect category:
-- |
-- | - **Gradient Ramp**: Linear/radial gradient fills
-- | - **Cell Pattern**: Procedural cellular textures
-- | - **Checkerboard**: Checkerboard pattern
-- | - **Grid**: Lines/rectangles grid pattern
-- | - **Circle**: Simple circle shape
-- | - **Ellipse**: Ellipse with separate dimensions
-- | - **Fill**: Solid color fill
-- | - **Stroke**: Path stroke effect
-- | - **Vegas**: Animated stroke along path
-- | - **Fractal**: Fractal noise pattern
-- | - **4-Color Gradient**: Four-corner gradient
-- | - **Lens Flare**: Optical lens flare effect
-- |
-- | ## GPU Shader Pattern
-- |
-- | Generate effects are fully procedural, ideal for GPU shaders:
-- | ```glsl
-- | vec4 generateColor = computePattern(uv, params);
-- | outputColor = blend(inputColor, generateColor, blendMode);
-- | ```
-- |
-- | ## Bounded Properties
-- |
-- | All properties use bounded types for deterministic rendering.

module Hydrogen.Schema.Motion.Effects.Generate
  ( -- * Gradient Ramp
    GradientRampEffect
  , RampShape(..)
  , defaultGradientRamp
  , linearGradientRamp
  , radialGradientRamp
  
  -- * Cell Pattern
  , CellPatternEffect
  , CellType(..)
  , defaultCellPattern
  , cellPatternWithType
  
  -- * Checkerboard
  , CheckerboardEffect
  , defaultCheckerboard
  , checkerboardWithSize
  
  -- * Grid
  , GridEffect
  , GridType(..)
  , defaultGrid
  , gridWithSize
  
  -- * Circle
  , CircleEffect
  , CircleEdgeType(..)
  , defaultCircle
  , circleWithRadius
  
  -- * Ellipse
  , EllipseEffect
  , defaultEllipse
  , ellipseWithSize
  
  -- * Fill
  , FillEffect
  , FillMaskMode(..)
  , defaultFill
  , fillWithColor
  
  -- * Stroke
  , StrokeEffect
  , StrokePaintStyle(..)
  , defaultStroke
  , strokeWithWidth
  
  -- * Vegas
  , VegasEffect
  , VegasPathMode(..)
  , defaultVegas
  , vegasWithSegments
  
  -- * Fractal
  , FractalEffect
  , FractalNoiseType(..)
  , defaultFractal
  , fractalWithComplexity
  
  -- * Four-Color Gradient
  , FourColorGradientEffect
  , defaultFourColorGradient
  
  -- * Lens Flare
  , LensFlareEffect
  , LensType(..)
  , defaultLensFlare
  , lensFlareWithBrightness
  
  -- * Serialization
  , rampShapeToString
  , cellTypeToString
  , gridTypeToString
  , circleEdgeTypeToString
  , fillMaskModeToString
  , strokePaintStyleToString
  , vegasPathModeToString
  , fractalNoiseTypeToString
  , lensTypeToString
  
  -- * Effect Descriptions
  , describeGradientRamp
  , describeCellPattern
  , describeGrid
  , describeFractal
  , describeLensFlare
  , describeVegas
  
  -- * Effect Names
  , gradientRampEffectName
  , cellPatternEffectName
  , checkerboardEffectName
  , gridEffectName
  , circleEffectName
  , ellipseEffectName
  , fillEffectName
  , strokeEffectName
  , vegasEffectName
  , fractalEffectName
  , fourColorGradientEffectName
  , lensFlareEffectName
  
  -- * Queries
  , hasGradientScatter
  , isCellPatternInverted
  , isFractalInverted
  , isCircleInverted
  , isEllipseInverted
  
  -- * Composition
  , combineGradientScatter
  , combineCellEvolution
  , combineFractalEvolution
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , ($)
  , (<>)
  , (<)
  , (>)
  , (+)
  , show
  , otherwise
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Dimension.Point2D (Point2D, origin, point2D)
import Hydrogen.Schema.Motion.Composition (BlendMode(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // gradient // ramp
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ramp shape — gradient direction pattern.
data RampShape
  = RSLinear       -- ^ Linear gradient (straight line)
  | RSRadial       -- ^ Radial gradient (circular)

derive instance eqRampShape :: Eq RampShape
derive instance ordRampShape :: Ord RampShape

instance showRampShape :: Show RampShape where
  show RSLinear = "linear"
  show RSRadial = "radial"

-- | Gradient Ramp Effect — linear or radial gradient fill.
-- |
-- | ## AE Properties
-- |
-- | - Start of Ramp / End of Ramp: Points defining gradient vector
-- | - Start Color / End Color: Gradient endpoint colors
-- | - Ramp Shape: Linear or Radial
-- | - Ramp Scatter: Add noise to gradient
-- | - Blend With Original: How much to mix with original
type GradientRampEffect =
  { startPoint :: Point2D        -- ^ Start of gradient
  , endPoint :: Point2D          -- ^ End of gradient
  , startColor :: RGB            -- ^ Color at start
  , endColor :: RGB              -- ^ Color at end
  , rampShape :: RampShape       -- ^ Linear or radial
  , scatter :: Number            -- ^ Random scatter (0-100)
  , blendWithOriginal :: Number  -- ^ Blend amount (0-100)
  }

-- | Default gradient ramp: black to white, linear, top to bottom.
defaultGradientRamp :: GradientRampEffect
defaultGradientRamp =
  { startPoint: point2D 0.0 0.0
  , endPoint: point2D 0.0 100.0
  , startColor: rgb 0 0 0
  , endColor: rgb 255 255 255
  , rampShape: RSLinear
  , scatter: 0.0
  , blendWithOriginal: 0.0
  }

-- | Create linear gradient ramp.
linearGradientRamp :: Point2D -> Point2D -> RGB -> RGB -> GradientRampEffect
linearGradientRamp start end startCol endCol =
  { startPoint: start
  , endPoint: end
  , startColor: startCol
  , endColor: endCol
  , rampShape: RSLinear
  , scatter: 0.0
  , blendWithOriginal: 0.0
  }

-- | Create radial gradient ramp.
radialGradientRamp :: Point2D -> Point2D -> RGB -> RGB -> GradientRampEffect
radialGradientRamp start end startCol endCol =
  { startPoint: start
  , endPoint: end
  , startColor: startCol
  , endColor: endCol
  , rampShape: RSRadial
  , scatter: 0.0
  , blendWithOriginal: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // cell // pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cell type — pattern generated.
data CellType
  = CTBubbles          -- ^ Circular cells
  | CTPipes            -- ^ Connected pipe-like cells
  | CTCrystals         -- ^ Angular crystal-like cells
  | CTMixed            -- ^ Mix of cell types
  | CTPlates           -- ^ Flat plate-like cells
  | CTSoft             -- ^ Soft-edged cells

derive instance eqCellType :: Eq CellType
derive instance ordCellType :: Ord CellType

instance showCellType :: Show CellType where
  show CTBubbles = "bubbles"
  show CTPipes = "pipes"
  show CTCrystals = "crystals"
  show CTMixed = "mixed"
  show CTPlates = "plates"
  show CTSoft = "soft"

-- | Cell Pattern Effect — procedural cellular texture.
-- |
-- | ## AE Properties
-- |
-- | - Cell Type: Visual style of cells
-- | - Size: Cell size in pixels
-- | - Offset: Pattern offset for animation
-- | - Evolution: Animate the pattern over time
-- | - Contrast: Cell edge contrast
type CellPatternEffect =
  { cellType :: CellType         -- ^ Type of cell pattern
  , size :: Number               -- ^ Cell size (1-1000)
  , offset :: Point2D            -- ^ Pattern offset
  , evolution :: Number          -- ^ Evolution (0-360 degrees, animatable)
  , contrast :: Number           -- ^ Edge contrast (0-100)
  , randomSeed :: Int            -- ^ Random seed for reproducibility
  , invert :: Boolean            -- ^ Invert output
  }

-- | Default cell pattern: bubbles, size 50.
defaultCellPattern :: CellPatternEffect
defaultCellPattern =
  { cellType: CTBubbles
  , size: 50.0
  , offset: origin
  , evolution: 0.0
  , contrast: 100.0
  , randomSeed: 0
  , invert: false
  }

-- | Create cell pattern with specific type.
cellPatternWithType :: CellType -> Number -> CellPatternEffect
cellPatternWithType ct sz =
  { cellType: ct
  , size: clampNumber 1.0 1000.0 sz
  , offset: origin
  , evolution: 0.0
  , contrast: 100.0
  , randomSeed: 0
  , invert: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // checkerboard
-- ═════════════════════════════════════════════════════════════════════════════

-- | Checkerboard Effect — alternating square pattern.
-- |
-- | ## AE Properties
-- |
-- | - Anchor: Pattern anchor point
-- | - Size: Square size (width, height)
-- | - Feather: Edge softness
-- | - Color: Checker color (alternates with transparent)
-- | - Opacity: Overall opacity
-- | - Blend Mode: How to composite with original
type CheckerboardEffect =
  { anchor :: Point2D            -- ^ Pattern anchor
  , size :: { width :: Number, height :: Number }  -- ^ Square size (1-1000 each)
  , feather :: Number            -- ^ Edge feather (0-100)
  , color :: RGB                 -- ^ Checker color
  , opacity :: Number            -- ^ Opacity (0-100)
  , blendMode :: BlendMode       -- ^ Compositing mode
  }

-- | Default checkerboard: 100x100, black.
defaultCheckerboard :: CheckerboardEffect
defaultCheckerboard =
  { anchor: origin
  , size: { width: 100.0, height: 100.0 }
  , feather: 0.0
  , color: rgb 0 0 0
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- | Create checkerboard with specific size.
checkerboardWithSize :: Number -> Number -> RGB -> CheckerboardEffect
checkerboardWithSize w h col =
  { anchor: origin
  , size: { width: clampNumber 1.0 1000.0 w, height: clampNumber 1.0 1000.0 h }
  , feather: 0.0
  , color: col
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid type — line or rectangle grid.
data GridType
  = GTLines           -- ^ Lines only
  | GTRectangles      -- ^ Filled rectangles

derive instance eqGridType :: Eq GridType
derive instance ordGridType :: Ord GridType

instance showGridType :: Show GridType where
  show GTLines = "lines"
  show GTRectangles = "rectangles"

-- | Grid Effect — regular grid pattern.
-- |
-- | ## AE Properties
-- |
-- | - Anchor: Grid anchor point
-- | - Corner: Grid corner (defines size)
-- | - Border: Line thickness (for lines mode)
-- | - Feather: Edge softness
-- | - Color/Opacity: Grid appearance
type GridEffect =
  { anchor :: Point2D            -- ^ Grid anchor
  , corner :: Point2D            -- ^ Grid corner (defines cell size)
  , gridType :: GridType         -- ^ Lines or rectangles
  , border :: Number             -- ^ Line thickness (0-100)
  , feather :: Number            -- ^ Edge feather (0-100)
  , color :: RGB                 -- ^ Grid color
  , opacity :: Number            -- ^ Opacity (0-100)
  , blendMode :: BlendMode       -- ^ Compositing mode
  }

-- | Default grid: 100x100 cells, 1px lines, white.
defaultGrid :: GridEffect
defaultGrid =
  { anchor: origin
  , corner: point2D 100.0 100.0
  , gridType: GTLines
  , border: 1.0
  , feather: 0.0
  , color: rgb 255 255 255
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- | Create grid with specific cell size.
gridWithSize :: Number -> Number -> RGB -> GridEffect
gridWithSize w h col =
  { anchor: origin
  , corner: point2D (clampNumber 1.0 10000.0 w) (clampNumber 1.0 10000.0 h)
  , gridType: GTLines
  , border: 1.0
  , feather: 0.0
  , color: col
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // circle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Circle edge type — filled or ring.
data CircleEdgeType
  = CETNone            -- ^ Filled circle
  | CETThickness       -- ^ Ring with thickness

derive instance eqCircleEdgeType :: Eq CircleEdgeType
derive instance ordCircleEdgeType :: Ord CircleEdgeType

instance showCircleEdgeType :: Show CircleEdgeType where
  show CETNone = "none"
  show CETThickness = "thickness"

-- | Circle Effect — simple circle shape.
-- |
-- | ## AE Properties
-- |
-- | - Center: Circle center point
-- | - Radius: Circle radius
-- | - Edge: None (filled) or Thickness (ring)
-- | - Feather: Edge softness
-- | - Invert Circle: Swap inside/outside
-- | - Color/Opacity: Appearance
type CircleEffect =
  { center :: Point2D            -- ^ Circle center
  , radius :: Number             -- ^ Radius (0-10000)
  , edgeType :: CircleEdgeType   -- ^ Filled or ring
  , edgeThickness :: Number      -- ^ Ring thickness (0-1000)
  , feather :: { inner :: Number, outer :: Number }  -- ^ Feathering (0-100 each)
  , invertCircle :: Boolean      -- ^ Invert mask
  , color :: RGB                 -- ^ Circle color
  , opacity :: Number            -- ^ Opacity (0-100)
  , blendMode :: BlendMode       -- ^ Compositing mode
  }

-- | Default circle: center at 100,100, radius 50, white filled.
defaultCircle :: CircleEffect
defaultCircle =
  { center: point2D 100.0 100.0
  , radius: 50.0
  , edgeType: CETNone
  , edgeThickness: 0.0
  , feather: { inner: 0.0, outer: 0.0 }
  , invertCircle: false
  , color: rgb 255 255 255
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- | Create circle with specific radius.
circleWithRadius :: Point2D -> Number -> RGB -> CircleEffect
circleWithRadius center' radius' col =
  { center: center'
  , radius: clampNumber 0.0 10000.0 radius'
  , edgeType: CETNone
  , edgeThickness: 0.0
  , feather: { inner: 0.0, outer: 0.0 }
  , invertCircle: false
  , color: col
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // ellipse
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ellipse Effect — ellipse with separate width/height.
-- |
-- | Same properties as Circle but with separate dimensions.
type EllipseEffect =
  { center :: Point2D            -- ^ Ellipse center
  , size :: { width :: Number, height :: Number }  -- ^ Dimensions (0-10000 each)
  , edgeType :: CircleEdgeType   -- ^ Filled or ring
  , edgeThickness :: Number      -- ^ Ring thickness (0-1000)
  , feather :: { inner :: Number, outer :: Number }  -- ^ Feathering (0-100 each)
  , invertEllipse :: Boolean     -- ^ Invert mask
  , color :: RGB                 -- ^ Ellipse color
  , opacity :: Number            -- ^ Opacity (0-100)
  , blendMode :: BlendMode       -- ^ Compositing mode
  }

-- | Default ellipse: 100x60 at center, white filled.
defaultEllipse :: EllipseEffect
defaultEllipse =
  { center: point2D 100.0 100.0
  , size: { width: 100.0, height: 60.0 }
  , edgeType: CETNone
  , edgeThickness: 0.0
  , feather: { inner: 0.0, outer: 0.0 }
  , invertEllipse: false
  , color: rgb 255 255 255
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- | Create ellipse with specific size.
ellipseWithSize :: Point2D -> Number -> Number -> RGB -> EllipseEffect
ellipseWithSize center' w h col =
  { center: center'
  , size: { width: clampNumber 0.0 10000.0 w, height: clampNumber 0.0 10000.0 h }
  , edgeType: CETNone
  , edgeThickness: 0.0
  , feather: { inner: 0.0, outer: 0.0 }
  , invertEllipse: false
  , color: col
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // fill
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fill mask mode — which masks to use.
data FillMaskMode
  = FMMAllMasks        -- ^ Use all masks
  | FMMFillMask        -- ^ Use fill mask only
  | FMMNone            -- ^ Ignore masks

derive instance eqFillMaskMode :: Eq FillMaskMode
derive instance ordFillMaskMode :: Ord FillMaskMode

instance showFillMaskMode :: Show FillMaskMode where
  show FMMAllMasks = "all-masks"
  show FMMFillMask = "fill-mask"
  show FMMNone = "none"

-- | Fill Effect — solid color fill.
-- |
-- | Fills the layer (or mask area) with a solid color.
type FillEffect =
  { fillMask :: FillMaskMode     -- ^ Which masks to fill
  , allMasks :: Boolean          -- ^ Use all masks
  , color :: RGB                 -- ^ Fill color
  , invertMask :: Boolean        -- ^ Invert mask
  , horizontalFeather :: Number  -- ^ H feather (0-100)
  , verticalFeather :: Number    -- ^ V feather (0-100)
  , opacity :: Number            -- ^ Opacity (0-100)
  , blendMode :: BlendMode       -- ^ Compositing mode
  }

-- | Default fill: red, full opacity.
defaultFill :: FillEffect
defaultFill =
  { fillMask: FMMNone
  , allMasks: false
  , color: rgb 255 0 0
  , invertMask: false
  , horizontalFeather: 0.0
  , verticalFeather: 0.0
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- | Create fill with specific color.
fillWithColor :: RGB -> FillEffect
fillWithColor col =
  { fillMask: FMMNone
  , allMasks: false
  , color: col
  , invertMask: false
  , horizontalFeather: 0.0
  , verticalFeather: 0.0
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stroke paint style — how to render the stroke.
data StrokePaintStyle
  = SPSOnTransparent   -- ^ Stroke on transparent background
  | SPSOnOriginal      -- ^ Stroke over original image

derive instance eqStrokePaintStyle :: Eq StrokePaintStyle
derive instance ordStrokePaintStyle :: Ord StrokePaintStyle

instance showStrokePaintStyle :: Show StrokePaintStyle where
  show SPSOnTransparent = "on-transparent"
  show SPSOnOriginal = "on-original"

-- | Stroke Effect — draws stroke along path or mask.
-- |
-- | ## AE Properties
-- |
-- | - All Masks: Use all masks
-- | - Brush Size/Hardness: Brush properties
-- | - Spacing: Distance between brush stamps
-- | - Paint Style: On transparent or original
-- | - Color/Opacity: Stroke appearance
type StrokeEffect =
  { allMasks :: Boolean          -- ^ Use all masks
  , brushSize :: Number          -- ^ Brush diameter (0.1-200)
  , brushHardness :: Number      -- ^ Brush edge hardness (0-100)
  , opacity :: Number            -- ^ Stroke opacity (0-100)
  , spacing :: Number            -- ^ Brush spacing (1-1000 %)
  , paintStyle :: StrokePaintStyle -- ^ Paint mode
  , color :: RGB                 -- ^ Stroke color
  , blendMode :: BlendMode       -- ^ Compositing mode
  , start :: Number              -- ^ Start point (0-100 %)
  , end :: Number                -- ^ End point (0-100 %)
  }

-- | Default stroke: 4px, 100% hardness, black.
defaultStroke :: StrokeEffect
defaultStroke =
  { allMasks: true
  , brushSize: 4.0
  , brushHardness: 100.0
  , opacity: 100.0
  , spacing: 25.0
  , paintStyle: SPSOnTransparent
  , color: rgb 0 0 0
  , blendMode: BMNormal
  , start: 0.0
  , end: 100.0
  }

-- | Create stroke with specific width.
strokeWithWidth :: Number -> RGB -> StrokeEffect
strokeWithWidth width col =
  { allMasks: true
  , brushSize: clampNumber 0.1 200.0 width
  , brushHardness: 100.0
  , opacity: 100.0
  , spacing: 25.0
  , paintStyle: SPSOnTransparent
  , color: col
  , blendMode: BMNormal
  , start: 0.0
  , end: 100.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // vegas
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vegas path mode — source of path data.
data VegasPathMode
  = VPMMasks           -- ^ Use layer masks
  | VPMLayer           -- ^ Use layer outlines
  | VPMAllPaths        -- ^ All paths in layer

derive instance eqVegasPathMode :: Eq VegasPathMode
derive instance ordVegasPathMode :: Ord VegasPathMode

instance showVegasPathMode :: Show VegasPathMode where
  show VPMMasks = "masks"
  show VPMLayer = "layer"
  show VPMAllPaths = "all-paths"

-- | Vegas Effect — animated stroke along paths.
-- |
-- | ## AE Properties
-- |
-- | Creates animated segments that move along paths.
-- | Used for neon signs, animated outlines, etc.
type VegasEffect =
  { pathMode :: VegasPathMode    -- ^ Path source
  , segments :: Int              -- ^ Number of segments (1-100)
  , length :: Number             -- ^ Segment length (0-10000)
  , width :: Number              -- ^ Line width (0-100)
  , hardness :: Number           -- ^ Edge hardness (0-100)
  , rotation :: Number           -- ^ Segment rotation (0-360)
  , randomPhase :: Boolean       -- ^ Random start positions
  , blendMode :: BlendMode       -- ^ Compositing mode
  , color :: RGB                 -- ^ Primary color
  , startOpacity :: Number       -- ^ Segment start opacity (0-100)
  , endOpacity :: Number         -- ^ Segment end opacity (0-100)
  }

-- | Default vegas: 5 segments, 50px length.
defaultVegas :: VegasEffect
defaultVegas =
  { pathMode: VPMMasks
  , segments: 5
  , length: 50.0
  , width: 5.0
  , hardness: 75.0
  , rotation: 0.0
  , randomPhase: false
  , blendMode: BMNormal
  , color: rgb 255 255 255
  , startOpacity: 100.0
  , endOpacity: 0.0
  }

-- | Create vegas with specific segment count.
vegasWithSegments :: Int -> Number -> RGB -> VegasEffect
vegasWithSegments segs len col =
  { pathMode: VPMMasks
  , segments: clampInt 1 100 segs
  , length: clampNumber 0.0 10000.0 len
  , width: 5.0
  , hardness: 75.0
  , rotation: 0.0
  , randomPhase: false
  , blendMode: BMNormal
  , color: col
  , startOpacity: 100.0
  , endOpacity: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // fractal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fractal noise type — algorithm used.
data FractalNoiseType
  = FNTBasic           -- ^ Basic noise
  | FNTTurbulentSmooth -- ^ Turbulent smooth
  | FNTTurbulentSharp  -- ^ Turbulent sharp
  | FNTDynamic         -- ^ Dynamic (evolving)
  | FNTDynamicTwist    -- ^ Dynamic twist
  | FNTSplineTurbulence -- ^ Spline-based

derive instance eqFractalNoiseType :: Eq FractalNoiseType
derive instance ordFractalNoiseType :: Ord FractalNoiseType

instance showFractalNoiseType :: Show FractalNoiseType where
  show FNTBasic = "basic"
  show FNTTurbulentSmooth = "turbulent-smooth"
  show FNTTurbulentSharp = "turbulent-sharp"
  show FNTDynamic = "dynamic"
  show FNTDynamicTwist = "dynamic-twist"
  show FNTSplineTurbulence = "spline-turbulence"

-- | Fractal Effect — procedural fractal noise.
-- |
-- | ## AE Properties
-- |
-- | - Fractal Type: Algorithm type
-- | - Contrast/Brightness: Output adjustment
-- | - Overflow: How to handle values > 1
-- | - Transform: Scale, offset, rotation
-- | - Complexity: Number of octaves
-- | - Evolution: Animation parameter
type FractalEffect =
  { fractalType :: FractalNoiseType  -- ^ Noise algorithm
  , contrast :: Number           -- ^ Output contrast (-200 to 200)
  , brightness :: Number         -- ^ Output brightness (-200 to 200)
  , scale :: Number              -- ^ Pattern scale (1-10000 %)
  , uniformScaling :: Boolean    -- ^ Lock X/Y scale
  , offset :: Point2D            -- ^ Pattern offset
  , rotation :: Number           -- ^ Pattern rotation (0-360)
  , complexity :: Number         -- ^ Octave count (1-20)
  , subInfluence :: Number       -- ^ Sub-octave influence (0-100)
  , evolution :: Number          -- ^ Evolution (0-360, animatable)
  , cycleEvolution :: Boolean    -- ^ Cycle evolution
  , randomSeed :: Int            -- ^ Random seed
  , invert :: Boolean            -- ^ Invert output
  }

-- | Default fractal: basic, medium complexity.
defaultFractal :: FractalEffect
defaultFractal =
  { fractalType: FNTBasic
  , contrast: 100.0
  , brightness: 0.0
  , scale: 100.0
  , uniformScaling: true
  , offset: origin
  , rotation: 0.0
  , complexity: 6.0
  , subInfluence: 70.0
  , evolution: 0.0
  , cycleEvolution: false
  , randomSeed: 0
  , invert: false
  }

-- | Create fractal with specific complexity.
fractalWithComplexity :: FractalNoiseType -> Number -> FractalEffect
fractalWithComplexity ft cmplx =
  { fractalType: ft
  , contrast: 100.0
  , brightness: 0.0
  , scale: 100.0
  , uniformScaling: true
  , offset: origin
  , rotation: 0.0
  , complexity: clampNumber 1.0 20.0 cmplx
  , subInfluence: 70.0
  , evolution: 0.0
  , cycleEvolution: false
  , randomSeed: 0
  , invert: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // four // color // gradient
-- ═════════════════════════════════════════════════════════════════════════════

-- | Four-Color Gradient Effect — four-corner gradient.
-- |
-- | ## AE Properties
-- |
-- | Creates smooth gradient from four corner colors with
-- | adjustable blend and jitter.
type FourColorGradientEffect =
  { point1 :: Point2D            -- ^ Corner 1 position
  , color1 :: RGB                -- ^ Corner 1 color
  , point2 :: Point2D            -- ^ Corner 2 position
  , color2 :: RGB                -- ^ Corner 2 color
  , point3 :: Point2D            -- ^ Corner 3 position
  , color3 :: RGB                -- ^ Corner 3 color
  , point4 :: Point2D            -- ^ Corner 4 position
  , color4 :: RGB                -- ^ Corner 4 color
  , blend :: Number              -- ^ Gradient blend amount (0-100)
  , jitter :: Number             -- ^ Add noise (0-100)
  , opacity :: Number            -- ^ Overall opacity (0-100)
  , blendMode :: BlendMode       -- ^ Compositing mode
  }

-- | Default four-color gradient: corners of 200x200, RGBY.
defaultFourColorGradient :: FourColorGradientEffect
defaultFourColorGradient =
  { point1: point2D 0.0 0.0
  , color1: rgb 255 0 0        -- Red
  , point2: point2D 200.0 0.0
  , color2: rgb 0 255 0        -- Green
  , point3: point2D 200.0 200.0
  , color3: rgb 0 0 255        -- Blue
  , point4: point2D 0.0 200.0
  , color4: rgb 255 255 0      -- Yellow
  , blend: 50.0
  , jitter: 0.0
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // lens // flare
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lens type — simulated lens system.
data LensType
  = LT50_300mm         -- ^ 50-300mm zoom
  | LT35mm             -- ^ 35mm prime
  | LT105mm            -- ^ 105mm prime

derive instance eqLensType :: Eq LensType
derive instance ordLensType :: Ord LensType

instance showLensType :: Show LensType where
  show LT50_300mm = "50-300mm"
  show LT35mm = "35mm"
  show LT105mm = "105mm"

-- | Lens Flare Effect — optical lens flare.
-- |
-- | ## AE Properties
-- |
-- | Simulates lens flare from bright light source.
-- | Classic motion graphics effect.
type LensFlareEffect =
  { flareCenter :: Point2D       -- ^ Light source position
  , flareBrightness :: Number    -- ^ Brightness (0-500 %)
  , lensType :: LensType         -- ^ Simulated lens
  , blendWithOriginal :: Number  -- ^ Blend amount (0-100)
  }

-- | Default lens flare: center, 100% brightness.
defaultLensFlare :: LensFlareEffect
defaultLensFlare =
  { flareCenter: point2D 100.0 100.0
  , flareBrightness: 100.0
  , lensType: LT50_300mm
  , blendWithOriginal: 0.0
  }

-- | Create lens flare with specific brightness.
lensFlareWithBrightness :: Point2D -> Number -> LensFlareEffect
lensFlareWithBrightness center bright =
  { flareCenter: center
  , flareBrightness: clampNumber 0.0 500.0 bright
  , lensType: LT50_300mm
  , blendWithOriginal: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp integer to bounds.
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RampShape to string for serialization.
rampShapeToString :: RampShape -> String
rampShapeToString rs = show rs

-- | Convert CellType to string for serialization.
cellTypeToString :: CellType -> String
cellTypeToString ct = show ct

-- | Convert GridType to string for serialization.
gridTypeToString :: GridType -> String
gridTypeToString gt = show gt

-- | Convert CircleEdgeType to string for serialization.
circleEdgeTypeToString :: CircleEdgeType -> String
circleEdgeTypeToString cet = show cet

-- | Convert FillMaskMode to string for serialization.
fillMaskModeToString :: FillMaskMode -> String
fillMaskModeToString fmm = show fmm

-- | Convert StrokePaintStyle to string for serialization.
strokePaintStyleToString :: StrokePaintStyle -> String
strokePaintStyleToString sps = show sps

-- | Convert VegasPathMode to string for serialization.
vegasPathModeToString :: VegasPathMode -> String
vegasPathModeToString vpm = show vpm

-- | Convert FractalNoiseType to string for serialization.
fractalNoiseTypeToString :: FractalNoiseType -> String
fractalNoiseTypeToString fnt = show fnt

-- | Convert LensType to string for serialization.
lensTypeToString :: LensType -> String
lensTypeToString lt = show lt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create gradient ramp effect description.
describeGradientRamp :: GradientRampEffect -> String
describeGradientRamp e = 
  "GradientRamp(" <> show e.rampShape <> ", scatter: " <> show e.scatter <> "%)"

-- | Create cell pattern effect description.
describeCellPattern :: CellPatternEffect -> String
describeCellPattern e = 
  "CellPattern(" <> show e.cellType <> ", size: " <> show e.size <> ")"

-- | Create grid effect description.
describeGrid :: GridEffect -> String
describeGrid e = 
  "Grid(" <> show e.gridType <> ", border: " <> show e.border <> ")"

-- | Create fractal effect description.
describeFractal :: FractalEffect -> String
describeFractal e = 
  "Fractal(" <> show e.fractalType <> ", complexity: " <> show e.complexity <> ")"

-- | Create lens flare effect description.
describeLensFlare :: LensFlareEffect -> String
describeLensFlare e = 
  "LensFlare(" <> show e.lensType <> ", brightness: " <> show e.flareBrightness <> "%)"

-- | Create vegas effect description.
describeVegas :: VegasEffect -> String
describeVegas e =
  "Vegas(" <> show e.segments <> " segments, length: " <> show e.length <> ")"

-- | Check if gradient ramp has scatter.
hasGradientScatter :: GradientRampEffect -> Boolean
hasGradientScatter e = e.scatter > 0.0

-- | Check if cell pattern is inverted.
isCellPatternInverted :: CellPatternEffect -> Boolean
isCellPatternInverted e = e.invert

-- | Check if fractal is inverted.
isFractalInverted :: FractalEffect -> Boolean
isFractalInverted e = e.invert

-- | Check if circle is inverted.
isCircleInverted :: CircleEffect -> Boolean
isCircleInverted e = e.invertCircle

-- | Check if ellipse is inverted.
isEllipseInverted :: EllipseEffect -> Boolean
isEllipseInverted e = e.invertEllipse

-- | Create composite effect name from gradient ramp.
gradientRampEffectName :: GradientRampEffect -> String
gradientRampEffectName _ = "Gradient Ramp"

-- | Create composite effect name from cell pattern.
cellPatternEffectName :: CellPatternEffect -> String
cellPatternEffectName _ = "Cell Pattern"

-- | Create composite effect name from checkerboard.
checkerboardEffectName :: CheckerboardEffect -> String
checkerboardEffectName _ = "Checkerboard"

-- | Create composite effect name from grid.
gridEffectName :: GridEffect -> String
gridEffectName _ = "Grid"

-- | Create composite effect name from circle.
circleEffectName :: CircleEffect -> String
circleEffectName _ = "Circle"

-- | Create composite effect name from ellipse.
ellipseEffectName :: EllipseEffect -> String
ellipseEffectName _ = "Ellipse"

-- | Create composite effect name from fill.
fillEffectName :: FillEffect -> String
fillEffectName _ = "Fill"

-- | Create composite effect name from stroke.
strokeEffectName :: StrokeEffect -> String
strokeEffectName _ = "Stroke"

-- | Create composite effect name from vegas.
vegasEffectName :: VegasEffect -> String
vegasEffectName _ = "Vegas"

-- | Create composite effect name from fractal.
fractalEffectName :: FractalEffect -> String
fractalEffectName _ = "Fractal"

-- | Create composite effect name from four-color gradient.
fourColorGradientEffectName :: FourColorGradientEffect -> String
fourColorGradientEffectName _ = "4-Color Gradient"

-- | Create composite effect name from lens flare.
lensFlareEffectName :: LensFlareEffect -> String
lensFlareEffectName _ = "Lens Flare"

-- | Combine gradient ramp scatter values (for effect stacking).
combineGradientScatter :: GradientRampEffect -> GradientRampEffect -> Number
combineGradientScatter e1 e2 = clampNumber 0.0 100.0 $ e1.scatter + e2.scatter

-- | Combine cell pattern evolution values.
combineCellEvolution :: CellPatternEffect -> CellPatternEffect -> Number
combineCellEvolution e1 e2 = clampNumber 0.0 360.0 $ e1.evolution + e2.evolution

-- | Combine fractal evolution values.
combineFractalEvolution :: FractalEffect -> FractalEffect -> Number
combineFractalEvolution e1 e2 = clampNumber 0.0 360.0 $ e1.evolution + e2.evolution
