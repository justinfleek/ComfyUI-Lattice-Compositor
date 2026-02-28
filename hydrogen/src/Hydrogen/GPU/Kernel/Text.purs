-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // gpu // kernel // text
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text Rendering Kernels — SDF Glyph Rendering for Ghostty-class Terminals
-- |
-- | ## Purpose
-- |
-- | High-performance text rendering requires GPU acceleration. SDF (Signed
-- | Distance Field) rendering enables:
-- |
-- | - Resolution-independent glyphs (infinite zoom without pixelation)
-- | - Smooth anti-aliasing at any scale
-- | - GPU-efficient text effects (outlines, shadows, glow)
-- | - Subpixel positioning for crisp text
-- |
-- | ## SDF Rendering Pipeline
-- |
-- | ```
-- | Font → SDF Atlas Generation → Glyph Cache
-- |                                    ↓
-- | Text String → Layout → Glyph Instances → SDF Render Kernel
-- |                                                ↓
-- |                                          Composited Output
-- | ```
-- |
-- | ## Ghostty Architecture Reference
-- |
-- | Ghostty achieves 120fps terminal rendering via:
-- | - Pre-rasterized SDF atlas (one-time cost per font)
-- | - Instanced rendering (one draw call for entire screen)
-- | - Subpixel anti-aliasing (ClearType-style LCD rendering)
-- | - Compute shader for text layout
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Text kernels are deterministic:
-- | - Same font + text + size = same output (always)
-- | - Glyph atlases are content-addressed (UUID5 from font data)
-- | - Text layout is pure function of input string + font metrics
-- | - Multiple agents can share atlas cache efficiently

module Hydrogen.GPU.Kernel.Text
  ( -- * Core Types
    TextKernel
      ( KernelGlyphRasterize
      , KernelTextLayout
      , KernelSubpixelAA
      , KernelCursorBlink
      , KernelTextMask
      , KernelTextSequence
      , KernelTextNoop
      )
  , KernelInput
      ( InputAtlas
      , InputGlyphBuffer
      , InputUniform
      , InputPrevious
      )
  , KernelOutput
      ( OutputTexture
      , OutputBuffer
      , OutputScreen
      )
  , WorkgroupSize
  , DispatchSize
  
  -- * SDF Atlas Types
  , SDFAtlas
  , AtlasConfig
  , AtlasRegion
  , SDFGlyph
  , SDFPadding
  , SDFSpread
  
  -- * Glyph Rasterization
  , GlyphRasterizeKernel
  , RasterizeMode
      ( RasterizeSDF
      , RasterizeMSDF
      , RasterizeMTSDF
      )
  , SDFConfig
  , mkGlyphRasterizeKernel
  
  -- * Text Layout
  , TextLayoutKernel
  , LayoutDirection
      ( LayoutLTR
      , LayoutRTL
      , LayoutTTB
      , LayoutBTT
      )
  , GlyphInstance
  , TextRun
  , mkTextLayoutKernel
  
  -- * Subpixel Anti-Aliasing
  , SubpixelAAKernel
  , SubpixelMode
      ( SubpixelNone
      , SubpixelRGB
      , SubpixelBGR
      , SubpixelVRGB
      , SubpixelVBGR
      )
  , SubpixelFilter
      ( FilterBox
      , FilterLinear
      , FilterGaussian
      )
  , mkSubpixelAAKernel
  
  -- * Cursor Rendering
  , CursorBlinkKernel
  , CursorStyle
      ( CursorBlock
      , CursorUnderline
      , CursorBar
      , CursorHollow
      )
  , BlinkState
      ( BlinkVisible
      , BlinkHidden
      , BlinkFading
      )
  , mkCursorBlinkKernel
  
  -- * Text Effects
  , TextMaskKernel
  , TextEffect
      ( EffectOutline
      , EffectShadow
      , EffectGlow
      , EffectBevel
      , EffectNone
      )
  , OutlineConfig
  , ShadowConfig
  , GlowConfig
  , mkTextMaskKernel
  
  -- * Kernel Configuration
  , TextKernelConfig
  , defaultTextKernelConfig
  , terminalConfig
  , editorConfig
  , uiConfig
  
  -- * Kernel Composition
  , sequenceTextKernels
  , conditionalTextKernel
  
  -- * Dispatch Calculation
  , computeTextWorkgroupSize
  , computeTextDispatchSize
  , estimateTextKernelCost
  
  -- * Kernel Analysis & Utilities
  , isKernelCheaper
  , isKernelCostAcceptable
  , isZeroCostKernel
  , mapKernels
  , isKernelDimensionsValid
  , isWorkgroupSizeValid
  , exceedsCostBudget
  , flipShadowOffset
  , invertShadowDirection
  , allKernelsSatisfy
  , anyKernelSatisfies
  , cheaperKernel
  , categorizeKernelCost
  
  -- * GPU Vector Types
  , Vec2
  , Vec3
  , Vec4
  , IVec2
  , IVec3
  , TensorShape
  , vec2
  , vec3
  , vec4
  , ivec2
  , ivec3
  , addVec2
  , subVec2
  , scaleVec2
  , mulVec2
  , dotVec2
  , addVec3
  , subVec3
  , scaleVec3
  , dotVec3
  , vec4FromRGBA
  , vec4ToTuple
  , tupleToVec4
  , swapVec2
  , zeroVec2
  , zeroVec3
  , zeroVec4
  , oneVec2
  , oneVec3
  , oneVec4
  
  -- * Tensor Operations
  , textureShape
  , tensorElements
  , tensorByteSize
  , isTensorShapeValid
  , tensorShapeEq
  
  -- * Math Utilities
  , saturate
  , clampInt
  , clampNumber
  , lerp
  , invLerp
  , remap
  , step
  , smoothstep
  
  -- * Color Packing
  , packRGB
  , unpackRGB
  , packRGBA
  , unpackRGBA
  
  -- * Dispatch Utilities
  , computeDispatchGroups
  , totalInvocations
  , isDispatchValid
  , pixelToUV
  , uvToPixel
  
  -- * SDF Utilities
  , evalSDF
  , sdfEdge
  , sdfOutline
  
  -- * Predicate Utilities
  , usesSubpixelRendering
  , hasValue
  , noValue
  , valueOr
  , whenJust
  , findKernel
  , hasGlyphMatching
  , totalGlyphAdvanceX
  , totalCharCount
  , isPlainText
  , isEffectNone
  , findFirstEffect
  
  -- * Kernel Composition
  , andThen
  , applyTo
  , composeTransforms
  , pipeTransforms
  , identityKernel
  , isIdentityKernel
  , sequenceAll
  , mapSequence
  , foldKernels
  , traverseKernels
  , compareKernelCost
  , kernelCostOrder
  
  -- * Workgroup Utilities
  , boundedWorkgroupDim
  , isPowerOfTwo
  , nextPowerOfTwo
  , optimalWorkgroupSize
  
  -- * Array Utilities
  , productArray
  , sumArray
  , containsInt
  
  -- * Algebraic Utilities
  , addVecSemiring
  , negateVecRing
  , identityTransform
  , selectKernel
  , chainKernelEffects
  , curryKernelConfig
  , uncurryKernelConfig
  , swapDimensions
  , foldrKernels
  , foldMapKernels
  , sequenceKernelEffects
  , forEachKernel
  , isNumberFinite
  , isWorkgroupInBounds
  , boundedRange
  , orderKernelsByCost
  , dimensionPair
  , traversableArrayWitness
  
  -- * Presets
  , ghosttyTerminalPipeline
  , ideEditorPipeline
  , uiLabelPipeline
  , gameHUDPipeline
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semiring
  , class Ring
  , class Bounded
  , class Applicative
  , class Bind
  , Ordering(LT, EQ, GT)
  , show
  , map
  , pure
  , bind
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (/=)
  , (<>)
  , (&&)
  , (||)
  , (<<<)
  , (>>>)
  , otherwise
  , negate
  , min
  , max
  , compare
  , top
  , bottom
  , zero
  , one
  , not
  , identity
  )

import Data.Array as Array
import Data.Int as Int
import Data.Int.Bits as Bits
import Data.Maybe (Maybe(Nothing, Just), fromMaybe, maybe, isJust, isNothing)
import Data.Tuple (Tuple(Tuple), fst, snd, curry, uncurry, swap)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Monoid (class Monoid)
import Data.Foldable (class Foldable, foldl, foldr, foldMap, sum, product, any, all, elem, find)
import Data.Traversable (class Traversable, traverse, sequence, for)
import Data.Number as Number
import Data.String as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Workgroup size for text compute dispatch
type WorkgroupSize =
  { x :: Int
  , y :: Int
  , z :: Int
  }

-- | Dispatch dimensions
type DispatchSize =
  { x :: Int
  , y :: Int
  , z :: Int
  }

-- | Text kernel input source
data KernelInput
  = InputAtlas Int           -- SDF atlas texture
  | InputGlyphBuffer Int     -- Glyph instance buffer
  | InputUniform Int         -- Uniform buffer
  | InputPrevious            -- Previous kernel output

derive instance eqKernelInput :: Eq KernelInput

instance showKernelInput :: Show KernelInput where
  show (InputAtlas i) = "(InputAtlas " <> show i <> ")"
  show (InputGlyphBuffer i) = "(InputGlyphBuffer " <> show i <> ")"
  show (InputUniform i) = "(InputUniform " <> show i <> ")"
  show InputPrevious = "InputPrevious"

-- | Text kernel output target
data KernelOutput
  = OutputTexture Int        -- Render to texture
  | OutputBuffer Int         -- Write to buffer
  | OutputScreen             -- Final screen output

derive instance eqKernelOutput :: Eq KernelOutput

instance showKernelOutput :: Show KernelOutput where
  show (OutputTexture i) = "(OutputTexture " <> show i <> ")"
  show (OutputBuffer i) = "(OutputBuffer " <> show i <> ")"
  show OutputScreen = "OutputScreen"

-- | Text kernel configuration
type TextKernelConfig =
  { workgroupSize :: WorkgroupSize
  , input :: KernelInput
  , output :: KernelOutput
  , width :: Int
  , height :: Int
  , dpi :: Number
  }

-- | Default text kernel configuration
defaultTextKernelConfig :: TextKernelConfig
defaultTextKernelConfig =
  { workgroupSize: { x: 8, y: 8, z: 1 }
  , input: InputAtlas 0
  , output: OutputScreen
  , width: 1920
  , height: 1080
  , dpi: 96.0
  }

-- | Terminal-optimized configuration
terminalConfig :: Int -> Int -> TextKernelConfig
terminalConfig cols rows =
  { workgroupSize: { x: 16, y: 16, z: 1 }
  , input: InputAtlas 0
  , output: OutputScreen
  , width: cols * 10   -- Approximate cell width
  , height: rows * 20  -- Approximate cell height
  , dpi: 96.0
  }

-- | Editor-optimized configuration
editorConfig :: Int -> Int -> TextKernelConfig
editorConfig width height =
  { workgroupSize: { x: 8, y: 8, z: 1 }
  , input: InputAtlas 0
  , output: OutputScreen
  , width
  , height
  , dpi: 96.0
  }

-- | UI label configuration
uiConfig :: Int -> Int -> Number -> TextKernelConfig
uiConfig width height dpi =
  { workgroupSize: { x: 8, y: 8, z: 1 }
  , input: InputAtlas 0
  , output: OutputScreen
  , width
  , height
  , dpi
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // text kernel adt
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text rendering kernel variants
data TextKernel
  = KernelGlyphRasterize GlyphRasterizeKernel
  | KernelTextLayout TextLayoutKernel
  | KernelSubpixelAA SubpixelAAKernel
  | KernelCursorBlink CursorBlinkKernel
  | KernelTextMask TextMaskKernel
  | KernelTextSequence (Array TextKernel)
  | KernelTextNoop

derive instance eqTextKernel :: Eq TextKernel

instance showTextKernel :: Show TextKernel where
  show (KernelGlyphRasterize k) = "(KernelGlyphRasterize " <> show k <> ")"
  show (KernelTextLayout k) = "(KernelTextLayout " <> show k <> ")"
  show (KernelSubpixelAA k) = "(KernelSubpixelAA " <> show k <> ")"
  show (KernelCursorBlink k) = "(KernelCursorBlink " <> show k <> ")"
  show (KernelTextMask k) = "(KernelTextMask " <> show k <> ")"
  show (KernelTextSequence _) = "(KernelTextSequence [...])"
  show KernelTextNoop = "KernelTextNoop"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // sdf atlas types
-- ═════════════════════════════════════════════════════════════════════════════

-- | SDF spread distance (pixels around glyph edge)
newtype SDFSpread = SDFSpread Int

derive instance eqSDFSpread :: Eq SDFSpread

instance showSDFSpread :: Show SDFSpread where
  show (SDFSpread s) = "(SDFSpread " <> show s <> ")"

-- | SDF padding (extra space around glyph in atlas)
newtype SDFPadding = SDFPadding Int

derive instance eqSDFPadding :: Eq SDFPadding

instance showSDFPadding :: Show SDFPadding where
  show (SDFPadding p) = "(SDFPadding " <> show p <> ")"

-- | Region within the SDF atlas for a single glyph
type AtlasRegion =
  { x :: Int           -- X offset in atlas
  , y :: Int           -- Y offset in atlas
  , width :: Int       -- Glyph width in atlas
  , height :: Int      -- Glyph height in atlas
  }

-- | SDF glyph data
type SDFGlyph =
  { codepoint :: Int           -- Unicode codepoint
  , region :: AtlasRegion      -- Location in atlas
  , bearingX :: Number         -- Left side bearing
  , bearingY :: Number         -- Top bearing (from baseline)
  , advanceX :: Number         -- Horizontal advance
  , advanceY :: Number         -- Vertical advance (for vertical text)
  }

-- | Atlas configuration
type AtlasConfig =
  { width :: Int               -- Atlas texture width
  , height :: Int              -- Atlas texture height
  , spread :: SDFSpread        -- SDF spread distance
  , padding :: SDFPadding      -- Padding between glyphs
  , scale :: Number            -- Render scale (1.0 = native size)
  }

-- | SDF atlas containing multiple glyphs
type SDFAtlas =
  { config :: AtlasConfig
  , glyphs :: Array SDFGlyph
  , textureId :: Int           -- GPU texture handle
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // glyph rasterize kernel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rasterization mode for SDF generation
data RasterizeMode
  = RasterizeSDF         -- Single-channel SDF
  | RasterizeMSDF        -- Multi-channel SDF (sharper corners)
  | RasterizeMTSDF       -- Multi-channel + true SDF (best quality)

derive instance eqRasterizeMode :: Eq RasterizeMode
derive instance ordRasterizeMode :: Ord RasterizeMode

instance showRasterizeMode :: Show RasterizeMode where
  show RasterizeSDF = "RasterizeSDF"
  show RasterizeMSDF = "RasterizeMSDF"
  show RasterizeMTSDF = "RasterizeMTSDF"

-- | SDF generation configuration
type SDFConfig =
  { mode :: RasterizeMode
  , spread :: SDFSpread
  , scale :: Number            -- Output scale factor
  , angleThreshold :: Number   -- Corner angle threshold (degrees, for MSDF)
  }

-- | Glyph rasterization kernel
-- |
-- | Converts vector font data to SDF atlas.
-- | This is typically a one-time cost per font.
newtype GlyphRasterizeKernel = GlyphRasterizeKernel
  { fontIndex :: Int           -- Which font to rasterize
  , codepointStart :: Int      -- First codepoint to rasterize
  , codepointEnd :: Int        -- Last codepoint to rasterize
  , sdfConfig :: SDFConfig
  , atlasConfig :: AtlasConfig
  , config :: TextKernelConfig
  }

derive instance eqGlyphRasterizeKernel :: Eq GlyphRasterizeKernel

instance showGlyphRasterizeKernel :: Show GlyphRasterizeKernel where
  show (GlyphRasterizeKernel k) = 
    "(GlyphRasterizeKernel font:" <> show k.fontIndex <> 
    " range:" <> show k.codepointStart <> "-" <> show k.codepointEnd <> ")"

-- | Create glyph rasterization kernel
mkGlyphRasterizeKernel 
  :: Int 
  -> Int 
  -> Int 
  -> SDFConfig 
  -> AtlasConfig 
  -> TextKernelConfig 
  -> GlyphRasterizeKernel
mkGlyphRasterizeKernel fontIndex codepointStart codepointEnd sdfConfig atlasConfig config =
  GlyphRasterizeKernel
    { fontIndex
    , codepointStart
    , codepointEnd
    , sdfConfig
    , atlasConfig
    , config
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // text layout kernel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text layout direction
data LayoutDirection
  = LayoutLTR      -- Left to right (English, etc.)
  | LayoutRTL      -- Right to left (Arabic, Hebrew)
  | LayoutTTB      -- Top to bottom (Traditional Chinese, Japanese)
  | LayoutBTT      -- Bottom to top (rare)

derive instance eqLayoutDirection :: Eq LayoutDirection

instance showLayoutDirection :: Show LayoutDirection where
  show LayoutLTR = "LayoutLTR"
  show LayoutRTL = "LayoutRTL"
  show LayoutTTB = "LayoutTTB"
  show LayoutBTT = "LayoutBTT"

-- | A positioned glyph instance for GPU rendering
type GlyphInstance =
  { glyphIndex :: Int          -- Index into glyph atlas
  , x :: Number                -- X position (pixels)
  , y :: Number                -- Y position (pixels)
  , scaleX :: Number           -- Horizontal scale
  , scaleY :: Number           -- Vertical scale
  , colorR :: Number           -- Red (0-1)
  , colorG :: Number           -- Green (0-1)
  , colorB :: Number           -- Blue (0-1)
  , colorA :: Number           -- Alpha (0-1)
  }

-- | A run of text with consistent styling
type TextRun =
  { text :: String
  , fontIndex :: Int
  , fontSize :: Number
  , colorR :: Number
  , colorG :: Number
  , colorB :: Number
  , colorA :: Number
  }

-- | Text layout kernel
-- |
-- | Computes glyph positions from text string.
-- | Handles line breaking, alignment, and direction.
newtype TextLayoutKernel = TextLayoutKernel
  { runs :: Array TextRun
  , direction :: LayoutDirection
  , lineHeight :: Number
  , maxWidth :: Number         -- For line breaking (0 = no limit)
  , alignX :: Number           -- 0 = left, 0.5 = center, 1 = right
  , alignY :: Number           -- 0 = top, 0.5 = middle, 1 = bottom
  , tabWidth :: Int            -- Tab stop width in spaces
  , config :: TextKernelConfig
  }

derive instance eqTextLayoutKernel :: Eq TextLayoutKernel

instance showTextLayoutKernel :: Show TextLayoutKernel where
  show (TextLayoutKernel k) = 
    "(TextLayoutKernel runs:" <> show (Array.length k.runs) <> 
    " dir:" <> show k.direction <> ")"

-- | Create text layout kernel
mkTextLayoutKernel 
  :: Array TextRun 
  -> LayoutDirection 
  -> Number 
  -> Number 
  -> TextKernelConfig 
  -> TextLayoutKernel
mkTextLayoutKernel runs direction lineHeight maxWidth config =
  TextLayoutKernel
    { runs
    , direction
    , lineHeight
    , maxWidth
    , alignX: 0.0
    , alignY: 0.0
    , tabWidth: 4
    , config
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // subpixel aa kernel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subpixel rendering mode
data SubpixelMode
  = SubpixelNone       -- No subpixel (grayscale AA)
  | SubpixelRGB        -- Horizontal RGB (most common LCD)
  | SubpixelBGR        -- Horizontal BGR
  | SubpixelVRGB       -- Vertical RGB
  | SubpixelVBGR       -- Vertical BGR

derive instance eqSubpixelMode :: Eq SubpixelMode
derive instance ordSubpixelMode :: Ord SubpixelMode

instance showSubpixelMode :: Show SubpixelMode where
  show SubpixelNone = "SubpixelNone"
  show SubpixelRGB = "SubpixelRGB"
  show SubpixelBGR = "SubpixelBGR"
  show SubpixelVRGB = "SubpixelVRGB"
  show SubpixelVBGR = "SubpixelVBGR"

-- | Subpixel filter type
data SubpixelFilter
  = FilterBox          -- Simple box filter
  | FilterLinear       -- Linear interpolation
  | FilterGaussian     -- Gaussian blur (smoothest)

derive instance eqSubpixelFilter :: Eq SubpixelFilter

instance showSubpixelFilter :: Show SubpixelFilter where
  show FilterBox = "FilterBox"
  show FilterLinear = "FilterLinear"
  show FilterGaussian = "FilterGaussian"

-- | Subpixel anti-aliasing kernel
-- |
-- | Applies ClearType-style subpixel rendering.
-- | Triples effective horizontal resolution on LCD displays.
newtype SubpixelAAKernel = SubpixelAAKernel
  { mode :: SubpixelMode
  , filter :: SubpixelFilter
  , gamma :: Number            -- Gamma correction (typically 1.8-2.2)
  , contrast :: Number         -- Contrast boost (0-1)
  , config :: TextKernelConfig
  }

derive instance eqSubpixelAAKernel :: Eq SubpixelAAKernel

instance showSubpixelAAKernel :: Show SubpixelAAKernel where
  show (SubpixelAAKernel k) = 
    "(SubpixelAAKernel mode:" <> show k.mode <> 
    " filter:" <> show k.filter <> ")"

-- | Create subpixel AA kernel
mkSubpixelAAKernel 
  :: SubpixelMode 
  -> SubpixelFilter 
  -> Number 
  -> TextKernelConfig 
  -> SubpixelAAKernel
mkSubpixelAAKernel mode filter gamma config =
  SubpixelAAKernel
    { mode
    , filter
    , gamma
    , contrast: 0.5
    , config
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // cursor blink kernel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cursor visual style
data CursorStyle
  = CursorBlock        -- Solid block (covers cell)
  | CursorUnderline    -- Line under text
  | CursorBar          -- Vertical bar (I-beam)
  | CursorHollow       -- Outline block

derive instance eqCursorStyle :: Eq CursorStyle
derive instance ordCursorStyle :: Ord CursorStyle

instance showCursorStyle :: Show CursorStyle where
  show CursorBlock = "CursorBlock"
  show CursorUnderline = "CursorUnderline"
  show CursorBar = "CursorBar"
  show CursorHollow = "CursorHollow"

-- | Cursor blink state
data BlinkState
  = BlinkVisible       -- Fully visible
  | BlinkHidden        -- Fully hidden
  | BlinkFading        -- Transitioning

derive instance eqBlinkState :: Eq BlinkState
derive instance ordBlinkState :: Ord BlinkState

instance showBlinkState :: Show BlinkState where
  show BlinkVisible = "BlinkVisible"
  show BlinkHidden = "BlinkHidden"
  show BlinkFading = "BlinkFading"

-- | Cursor rendering kernel
-- |
-- | Handles cursor display with optional blinking.
newtype CursorBlinkKernel = CursorBlinkKernel
  { style :: CursorStyle
  , blinkRate :: Number        -- Blinks per second (0 = no blink)
  , blinkDuty :: Number        -- Fraction visible (0-1, typically 0.5)
  , fadeTime :: Number         -- Fade transition time (ms)
  , cursorX :: Int             -- Cell X position
  , cursorY :: Int             -- Cell Y position
  , colorR :: Number           -- Cursor color red
  , colorG :: Number           -- Cursor color green
  , colorB :: Number           -- Cursor color blue
  , config :: TextKernelConfig
  }

derive instance eqCursorBlinkKernel :: Eq CursorBlinkKernel

instance showCursorBlinkKernel :: Show CursorBlinkKernel where
  show (CursorBlinkKernel k) = 
    "(CursorBlinkKernel style:" <> show k.style <> 
    " pos:" <> show k.cursorX <> "," <> show k.cursorY <> ")"

-- | Create cursor blink kernel
mkCursorBlinkKernel 
  :: CursorStyle 
  -> Number 
  -> Int 
  -> Int 
  -> TextKernelConfig 
  -> CursorBlinkKernel
mkCursorBlinkKernel style blinkRate cursorX cursorY config =
  CursorBlinkKernel
    { style
    , blinkRate
    , blinkDuty: 0.5
    , fadeTime: 100.0
    , cursorX
    , cursorY
    , colorR: 1.0
    , colorG: 1.0
    , colorB: 1.0
    , config
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // text effect kernel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Outline configuration
type OutlineConfig =
  { width :: Number            -- Outline width (pixels)
  , colorR :: Number
  , colorG :: Number
  , colorB :: Number
  , colorA :: Number
  }

-- | Shadow configuration
type ShadowConfig =
  { offsetX :: Number          -- Shadow X offset
  , offsetY :: Number          -- Shadow Y offset
  , blur :: Number             -- Shadow blur radius
  , colorR :: Number
  , colorG :: Number
  , colorB :: Number
  , colorA :: Number
  }

-- | Glow configuration
type GlowConfig =
  { radius :: Number           -- Glow radius
  , intensity :: Number        -- Glow intensity (0-1)
  , colorR :: Number
  , colorG :: Number
  , colorB :: Number
  }

-- | Text effect variants
data TextEffect
  = EffectOutline OutlineConfig
  | EffectShadow ShadowConfig
  | EffectGlow GlowConfig
  | EffectBevel                -- Emboss/bevel effect
      { depth :: Number
      , lightAngle :: Number
      }
  | EffectNone

derive instance eqTextEffect :: Eq TextEffect

instance showTextEffect :: Show TextEffect where
  show (EffectOutline _) = "(EffectOutline ...)"
  show (EffectShadow _) = "(EffectShadow ...)"
  show (EffectGlow _) = "(EffectGlow ...)"
  show (EffectBevel _) = "(EffectBevel ...)"
  show EffectNone = "EffectNone"

-- | Text mask/effect kernel
-- |
-- | Applies effects like outlines, shadows, glow using SDF.
newtype TextMaskKernel = TextMaskKernel
  { effects :: Array TextEffect
  , config :: TextKernelConfig
  }

derive instance eqTextMaskKernel :: Eq TextMaskKernel

instance showTextMaskKernel :: Show TextMaskKernel where
  show (TextMaskKernel k) = 
    "(TextMaskKernel effects:" <> show (Array.length k.effects) <> ")"

-- | Create text mask kernel
mkTextMaskKernel :: Array TextEffect -> TextKernelConfig -> TextMaskKernel
mkTextMaskKernel effects config =
  TextMaskKernel { effects, config }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // kernel composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sequence multiple text kernels
sequenceTextKernels :: Array TextKernel -> TextKernel
sequenceTextKernels kernels =
  case Array.length kernels of
    0 -> KernelTextNoop
    1 -> case Array.head kernels of
           Nothing -> KernelTextNoop
           Just k -> k
    _ -> KernelTextSequence kernels

-- | Conditional text kernel execution
conditionalTextKernel 
  :: Boolean 
  -> TextKernel 
  -> TextKernel 
  -> TextKernel
conditionalTextKernel condition thenKernel elseKernel =
  if condition
    then thenKernel
    else elseKernel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // dispatch calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute workgroup size for text kernel
computeTextWorkgroupSize :: TextKernel -> WorkgroupSize
computeTextWorkgroupSize kernel =
  case kernel of
    KernelGlyphRasterize (GlyphRasterizeKernel k) -> k.config.workgroupSize
    KernelTextLayout (TextLayoutKernel k) -> k.config.workgroupSize
    KernelSubpixelAA (SubpixelAAKernel k) -> k.config.workgroupSize
    KernelCursorBlink (CursorBlinkKernel k) -> k.config.workgroupSize
    KernelTextMask (TextMaskKernel k) -> k.config.workgroupSize
    KernelTextSequence kernels -> 
      case Array.head kernels of
        Nothing -> { x: 8, y: 8, z: 1 }
        Just k -> computeTextWorkgroupSize k
    KernelTextNoop -> { x: 1, y: 1, z: 1 }

-- | Compute dispatch size for text kernel
computeTextDispatchSize :: TextKernel -> DispatchSize
computeTextDispatchSize kernel =
  let
    workgroup = computeTextWorkgroupSize kernel
    dims = getKernelDimensions kernel
    divCeil a b = (a + b - 1) / b
  in
    { x: divCeil dims.width workgroup.x
    , y: divCeil dims.height workgroup.y
    , z: 1
    }

-- | Get kernel dimensions
getKernelDimensions :: TextKernel -> { width :: Int, height :: Int }
getKernelDimensions kernel =
  case kernel of
    KernelGlyphRasterize (GlyphRasterizeKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelTextLayout (TextLayoutKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelSubpixelAA (SubpixelAAKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelCursorBlink (CursorBlinkKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelTextMask (TextMaskKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelTextSequence kernels ->
      case Array.head kernels of
        Nothing -> { width: 0, height: 0 }
        Just k -> getKernelDimensions k
    KernelTextNoop -> { width: 0, height: 0 }

-- | Estimate kernel execution cost (microseconds)
estimateTextKernelCost :: TextKernel -> Number
estimateTextKernelCost kernel =
  case kernel of
    KernelGlyphRasterize (GlyphRasterizeKernel k) ->
      -- SDF generation is expensive: ~100μs per glyph
      Int.toNumber (k.codepointEnd - k.codepointStart + 1) * 100.0
    KernelTextLayout (TextLayoutKernel k) ->
      -- Layout is fast: ~1μs per character
      Int.toNumber (Array.length k.runs) * 100.0
    KernelSubpixelAA (SubpixelAAKernel k) ->
      -- Subpixel AA: ~10μs per 1K pixels
      Int.toNumber (k.config.width * k.config.height) / 100.0
    KernelCursorBlink _ ->
      -- Cursor is trivial: ~1μs
      1.0
    KernelTextMask (TextMaskKernel k) ->
      -- Effects: ~5μs per effect per 1K pixels
      Int.toNumber (Array.length k.effects) * 
      Int.toNumber (k.config.width * k.config.height) / 200.0
    KernelTextSequence kernels ->
      foldlArray (\acc k -> acc + estimateTextKernelCost k) 0.0 kernels
    KernelTextNoop -> 0.0

-- | Compare two kernels by estimated cost
-- | Returns true if the first kernel is cheaper than the second
isKernelCheaper :: TextKernel -> TextKernel -> Boolean
isKernelCheaper k1 k2 = estimateTextKernelCost k1 < estimateTextKernelCost k2

-- | Check if kernel cost is within acceptable bounds
-- | Bounds are in microseconds
isKernelCostAcceptable :: Number -> Number -> TextKernel -> Boolean
isKernelCostAcceptable minCost maxCost kernel =
  let cost = estimateTextKernelCost kernel
  in cost >= minCost && cost <= maxCost

-- | Check if a kernel has zero cost (noop or empty sequence)
isZeroCostKernel :: TextKernel -> Boolean
isZeroCostKernel kernel = estimateTextKernelCost kernel == 0.0

-- | Map a transformation over all kernels in a sequence
-- | For non-sequence kernels, applies the transform directly
mapKernels :: (TextKernel -> TextKernel) -> TextKernel -> TextKernel
mapKernels f kernel =
  case kernel of
    KernelTextSequence kernels -> KernelTextSequence (map f kernels)
    other -> f other

-- | Validate kernel dimensions are positive
isKernelDimensionsValid :: TextKernel -> Boolean
isKernelDimensionsValid kernel =
  let dims = getKernelDimensions kernel
  in dims.width > 0 && dims.height > 0 || isZeroCostKernel kernel

-- | Validate workgroup size is reasonable (1-1024 per dimension)
isWorkgroupSizeValid :: TextKernel -> Boolean
isWorkgroupSizeValid kernel =
  let ws = computeTextWorkgroupSize kernel
  in ws.x > 0 && ws.x <= 1024 
  && ws.y > 0 && ws.y <= 1024 
  && ws.z > 0 && ws.z <= 64

-- | Check if kernel exceeds a cost threshold (for budgeting)
exceedsCostBudget :: Number -> TextKernel -> Boolean
exceedsCostBudget budget kernel = estimateTextKernelCost kernel > budget

-- | Negate shadow offset (flip shadow direction)
flipShadowOffset :: ShadowConfig -> ShadowConfig
flipShadowOffset cfg = cfg 
  { offsetX = negate cfg.offsetX
  , offsetY = negate cfg.offsetY
  }

-- | Create inverted shadow effect (light from opposite direction)
invertShadowDirection :: TextEffect -> TextEffect
invertShadowDirection effect =
  case effect of
    EffectShadow cfg -> EffectShadow (flipShadowOffset cfg)
    other -> other

-- | Check if all kernels in a sequence meet a predicate
allKernelsSatisfy :: (TextKernel -> Boolean) -> TextKernel -> Boolean
allKernelsSatisfy pred kernel =
  case kernel of
    KernelTextSequence kernels -> foldlArray (\acc k -> acc && pred k) true kernels
    KernelTextNoop -> true
    other -> pred other

-- | Check if any kernel in a sequence meets a predicate
anyKernelSatisfies :: (TextKernel -> Boolean) -> TextKernel -> Boolean
anyKernelSatisfies pred kernel =
  case kernel of
    KernelTextSequence kernels -> foldlArray (\acc k -> acc || pred k) false kernels
    KernelTextNoop -> false
    other -> pred other

-- | Select the cheaper of two kernels
cheaperKernel :: TextKernel -> TextKernel -> TextKernel
cheaperKernel k1 k2 =
  if isKernelCheaper k1 k2
    then k1
    else k2

-- | Categorize kernel cost
-- | Returns "trivial" (<10μs), "fast" (<100μs), "moderate" (<1000μs), "expensive"
categorizeKernelCost :: TextKernel -> String
categorizeKernelCost kernel =
  let cost = estimateTextKernelCost kernel
  in if cost < 10.0 then "trivial"
     else if cost < 100.0 then "fast"
     else if cost < 1000.0 then "moderate"
     else "expensive"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // gpu compute utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D vector type for GPU coordinates
type Vec2 = { x :: Number, y :: Number }

-- | 3D vector type for colors/positions
type Vec3 = { x :: Number, y :: Number, z :: Number }

-- | 4D vector type for RGBA colors
type Vec4 = { x :: Number, y :: Number, z :: Number, w :: Number }

-- | Integer 2D vector for pixel coordinates
type IVec2 = { x :: Int, y :: Int }

-- | Integer 3D vector for voxels/workgroups
type IVec3 = { x :: Int, y :: Int, z :: Int }

-- | Tensor shape for GPU buffers
type TensorShape = 
  { width :: Int
  , height :: Int
  , channels :: Int
  , batch :: Int
  }

-- | Create a vec2
vec2 :: Number -> Number -> Vec2
vec2 x y = { x, y }

-- | Create a vec3
vec3 :: Number -> Number -> Number -> Vec3
vec3 x y z = { x, y, z }

-- | Create a vec4
vec4 :: Number -> Number -> Number -> Number -> Vec4
vec4 x y z w = { x, y, z, w }

-- | Create an ivec2
ivec2 :: Int -> Int -> IVec2
ivec2 x y = { x, y }

-- | Create an ivec3
ivec3 :: Int -> Int -> Int -> IVec3
ivec3 x y z = { x, y, z }

-- | Vec2 addition
addVec2 :: Vec2 -> Vec2 -> Vec2
addVec2 a b = { x: a.x + b.x, y: a.y + b.y }

-- | Vec2 subtraction
subVec2 :: Vec2 -> Vec2 -> Vec2
subVec2 a b = { x: a.x - b.x, y: a.y - b.y }

-- | Vec2 scalar multiply
scaleVec2 :: Number -> Vec2 -> Vec2
scaleVec2 s v = { x: v.x * s, y: v.y * s }

-- | Vec2 component-wise multiply
mulVec2 :: Vec2 -> Vec2 -> Vec2
mulVec2 a b = { x: a.x * b.x, y: a.y * b.y }

-- | Vec2 dot product
dotVec2 :: Vec2 -> Vec2 -> Number
dotVec2 a b = a.x * b.x + a.y * b.y

-- | Vec3 addition
addVec3 :: Vec3 -> Vec3 -> Vec3
addVec3 a b = { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z }

-- | Vec3 subtraction
subVec3 :: Vec3 -> Vec3 -> Vec3
subVec3 a b = { x: a.x - b.x, y: a.y - b.y, z: a.z - b.z }

-- | Vec3 scalar multiply
scaleVec3 :: Number -> Vec3 -> Vec3
scaleVec3 s v = { x: v.x * s, y: v.y * s, z: v.z * s }

-- | Vec3 dot product
dotVec3 :: Vec3 -> Vec3 -> Number
dotVec3 a b = a.x * b.x + a.y * b.y + a.z * b.z

-- | Vec4 from RGBA (0-255 to 0-1)
vec4FromRGBA :: Int -> Int -> Int -> Int -> Vec4
vec4FromRGBA r g b a =
  { x: Int.toNumber r / 255.0
  , y: Int.toNumber g / 255.0
  , z: Int.toNumber b / 255.0
  , w: Int.toNumber a / 255.0
  }

-- | Convert Vec4 to tuple for interop
vec4ToTuple :: Vec4 -> Tuple (Tuple Number Number) (Tuple Number Number)
vec4ToTuple v = Tuple (Tuple v.x v.y) (Tuple v.z v.w)

-- | Convert tuple to Vec4
tupleToVec4 :: Tuple (Tuple Number Number) (Tuple Number Number) -> Vec4
tupleToVec4 t = 
  let xy = fst t
      zw = snd t
  in { x: fst xy, y: snd xy, z: fst zw, w: snd zw }

-- | Swap vec2 components
swapVec2 :: Vec2 -> Vec2
swapVec2 v = { x: v.y, y: v.x }

-- | Tensor shape for a 2D texture
textureShape :: Int -> Int -> Int -> TensorShape
textureShape w h channels = { width: w, height: h, channels, batch: 1 }

-- | Total elements in tensor
tensorElements :: TensorShape -> Int
tensorElements s = s.width * s.height * s.channels * s.batch

-- | Tensor byte size (assuming float32)
tensorByteSize :: TensorShape -> Int
tensorByteSize s = tensorElements s * 4

-- | Check if tensor shape is valid
isTensorShapeValid :: TensorShape -> Boolean
isTensorShapeValid s =
  s.width > 0 && s.height > 0 && s.channels > 0 && s.batch > 0

-- | Compare tensor shapes
tensorShapeEq :: TensorShape -> TensorShape -> Boolean
tensorShapeEq a b =
  a.width == b.width && a.height == b.height && 
  a.channels == b.channels && a.batch == b.batch

-- | Clamp a number to [0, 1]
saturate :: Number -> Number
saturate x = min 1.0 (max 0.0 x)

-- | Clamp int to range
clampInt :: Int -> Int -> Int -> Int
clampInt lo hi x = min hi (max lo x)

-- | Clamp number to range
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = min hi (max lo x)

-- | Linear interpolation
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Inverse lerp (find t given value)
invLerp :: Number -> Number -> Number -> Number
invLerp a b v = (v - a) / (b - a)

-- | Remap value from one range to another
remap :: Number -> Number -> Number -> Number -> Number -> Number
remap inMin inMax outMin outMax v =
  lerp outMin outMax (invLerp inMin inMax v)

-- | Step function (0 if x < edge, 1 otherwise)
step :: Number -> Number -> Number
step edge x = if x < edge then 0.0 else 1.0

-- | Smooth step (cubic interpolation between edges)
smoothstep :: Number -> Number -> Number -> Number
smoothstep edge0 edge1 x =
  let t = saturate (invLerp edge0 edge1 x)
  in t * t * (3.0 - 2.0 * t)

-- | Pack RGB to 24-bit int
packRGB :: Int -> Int -> Int -> Int
packRGB r g b = 
  Bits.shl (clampInt 0 255 r) 16 `Bits.or`
  Bits.shl (clampInt 0 255 g) 8 `Bits.or`
  clampInt 0 255 b

-- | Unpack 24-bit int to RGB tuple
unpackRGB :: Int -> Tuple Int (Tuple Int Int)
unpackRGB packed =
  let r = Bits.and (Bits.shr packed 16) 255
      g = Bits.and (Bits.shr packed 8) 255
      b = Bits.and packed 255
  in Tuple r (Tuple g b)

-- | Pack RGBA to 32-bit int
packRGBA :: Int -> Int -> Int -> Int -> Int
packRGBA r g b a =
  Bits.shl (clampInt 0 255 a) 24 `Bits.or`
  Bits.shl (clampInt 0 255 r) 16 `Bits.or`
  Bits.shl (clampInt 0 255 g) 8 `Bits.or`
  clampInt 0 255 b

-- | Unpack 32-bit int to RGBA
unpackRGBA :: Int -> Vec4
unpackRGBA packed =
  { x: Int.toNumber (Bits.and (Bits.shr packed 16) 255) / 255.0
  , y: Int.toNumber (Bits.and (Bits.shr packed 8) 255) / 255.0
  , z: Int.toNumber (Bits.and packed 255) / 255.0
  , w: Int.toNumber (Bits.and (Bits.shr packed 24) 255) / 255.0
  }

-- | Compute dispatch groups for a given work size
computeDispatchGroups :: IVec3 -> IVec3 -> IVec3
computeDispatchGroups workSize groupSize =
  { x: divCeil workSize.x groupSize.x
  , y: divCeil workSize.y groupSize.y
  , z: divCeil workSize.z groupSize.z
  }
  where
    divCeil a b = (a + b - 1) / b

-- | Total invocations for dispatch
totalInvocations :: IVec3 -> IVec3 -> Int
totalInvocations groups groupSize =
  groups.x * groupSize.x * groups.y * groupSize.y * groups.z * groupSize.z

-- | Check if dispatch size is within GPU limits
isDispatchValid :: IVec3 -> Boolean
isDispatchValid d =
  d.x > 0 && d.x <= 65535 &&
  d.y > 0 && d.y <= 65535 &&
  d.z > 0 && d.z <= 65535

-- | UV coordinates from pixel position
pixelToUV :: IVec2 -> IVec2 -> Vec2
pixelToUV pixel size =
  { x: (Int.toNumber pixel.x + 0.5) / Int.toNumber size.x
  , y: (Int.toNumber pixel.y + 0.5) / Int.toNumber size.y
  }

-- | Pixel position from UV coordinates
uvToPixel :: Vec2 -> IVec2 -> IVec2
uvToPixel uv size =
  { x: min (size.x - 1) (max 0 (Int.floor (uv.x * Int.toNumber size.x)))
  , y: min (size.y - 1) (max 0 (Int.floor (uv.y * Int.toNumber size.y)))
  }

-- | SDF evaluation: negative inside, positive outside
-- | This is the core primitive for text rendering
evalSDF :: Number -> Number -> Number
evalSDF distance threshold = distance - threshold

-- | Anti-aliased edge from SDF
sdfEdge :: Number -> Number -> Number
sdfEdge distance edgeWidth =
  saturate (0.5 - distance / edgeWidth)

-- | Outline from SDF
sdfOutline :: Number -> Number -> Number -> Number
sdfOutline distance outlineWidth edgeWidth =
  let inner = sdfEdge distance edgeWidth
      outer = sdfEdge (distance - outlineWidth) edgeWidth
  in outer - inner

-- | Check if a config uses subpixel rendering
usesSubpixelRendering :: SubpixelMode -> Boolean
usesSubpixelRendering mode = mode /= SubpixelNone

-- | Check if a Maybe value is present
hasValue :: forall a. Maybe a -> Boolean
hasValue = isJust

-- | Check if a Maybe value is absent
noValue :: forall a. Maybe a -> Boolean
noValue = isNothing

-- | Get value or default
valueOr :: forall a. a -> Maybe a -> a
valueOr = fromMaybe

-- | Apply function if value present
whenJust :: forall a b. Maybe a -> (a -> b) -> Maybe b
whenJust m f = maybe Nothing (Just <<< f) m

-- | Find first kernel matching predicate
findKernel :: (TextKernel -> Boolean) -> TextKernel -> Maybe TextKernel
findKernel pred kernel =
  case kernel of
    KernelTextSequence kernels -> find pred kernels
    KernelTextNoop -> Nothing
    other -> if pred other then Just other else Nothing

-- | Check if any glyph in array matches predicate
hasGlyphMatching :: (GlyphInstance -> Boolean) -> Array GlyphInstance -> Boolean
hasGlyphMatching pred glyphs = any pred glyphs

-- | Sum all glyph X advances (horizontal spacing)
totalGlyphAdvanceX :: Array GlyphInstance -> Number
totalGlyphAdvanceX glyphs = sum (map (\g -> g.x * g.scaleX) glyphs)

-- | Count total characters across all runs
totalCharCount :: Array TextRun -> Int
totalCharCount runs = sum (map (\r -> String.length r.text) runs)

-- | Check if all effects are EffectNone (plain text)
isPlainText :: Array TextEffect -> Boolean
isPlainText effects = all isEffectNone effects

-- | Check if effect is EffectNone
isEffectNone :: TextEffect -> Boolean
isEffectNone EffectNone = true
isEffectNone _ = false

-- | Find first non-none effect
findFirstEffect :: Array TextEffect -> Maybe TextEffect
findFirstEffect effects = find (not <<< isEffectNone) effects

-- | Pipeline composition: sequence two kernels
-- | Uses >>> internally for function chaining
andThen :: TextKernel -> TextKernel -> TextKernel
andThen k1 k2 = sequenceTextKernels [k1, k2]

-- | Pipeline composition: apply transform then kernel
-- | Uses <<< internally for function composition
applyTo :: (TextKernel -> TextKernel) -> TextKernel -> TextKernel
applyTo f k = f k

-- | Compose two kernel transforms (right to left)
composeTransforms :: (TextKernel -> TextKernel) -> (TextKernel -> TextKernel) -> (TextKernel -> TextKernel)
composeTransforms f g = f <<< g

-- | Compose two kernel transforms (left to right)
pipeTransforms :: (TextKernel -> TextKernel) -> (TextKernel -> TextKernel) -> (TextKernel -> TextKernel)
pipeTransforms f g = f >>> g

-- | Identity kernel (for composition)
identityKernel :: TextKernel
identityKernel = KernelTextNoop

-- | Zero-cost operation check
isIdentityKernel :: TextKernel -> Boolean
isIdentityKernel KernelTextNoop = true
isIdentityKernel _ = false

-- | Sequence all kernels from foldable
sequenceAll :: forall f. Foldable f => f TextKernel -> TextKernel
sequenceAll kernels = 
  KernelTextSequence (foldl (\acc k -> Array.snoc acc k) [] kernels)

-- | Map and sequence kernels  
mapSequence :: forall a. (a -> TextKernel) -> Array a -> TextKernel
mapSequence f items = sequenceTextKernels (map f items)

-- | Fold over kernel sequence with accumulator
foldKernels :: forall a. (a -> TextKernel -> a) -> a -> TextKernel -> a
foldKernels f acc kernel =
  case kernel of
    KernelTextSequence kernels -> foldl f acc kernels
    KernelTextNoop -> acc
    other -> f acc other

-- | Traverse kernel sequence with effect
traverseKernels :: forall m. Applicative m => (TextKernel -> m TextKernel) -> TextKernel -> m TextKernel
traverseKernels f kernel =
  case kernel of
    KernelTextSequence kernels -> 
      map KernelTextSequence (traverse f kernels)
    KernelTextNoop -> pure KernelTextNoop
    other -> f other

-- | Compare kernel costs
compareKernelCost :: TextKernel -> TextKernel -> Ordering
compareKernelCost k1 k2 = compare (estimateTextKernelCost k1) (estimateTextKernelCost k2)

-- | Sort kernels by cost (returns indices)
-- | Useful for scheduling optimization
kernelCostOrder :: Array TextKernel -> Array Int
kernelCostOrder kernels =
  map fst (Array.sortBy compareCosts indexed)
  where
    indexed = Array.mapWithIndex Tuple kernels
    compareCosts (Tuple _ k1) (Tuple _ k2) = compareKernelCost k1 k2

-- | Get bounded workgroup dimension
boundedWorkgroupDim :: Int -> Int
boundedWorkgroupDim d = clampInt (bottom :: Int) (top :: Int) d

-- | Check if workgroup is power of two (optimal for GPU)
isPowerOfTwo :: Int -> Boolean
isPowerOfTwo n = n > 0 && Bits.and n (n - 1) == 0

-- | Round up to next power of two
nextPowerOfTwo :: Int -> Int
nextPowerOfTwo n =
  if isPowerOfTwo n then n
  else 
    let n1 = Bits.or n (Bits.shr n 1)
        n2 = Bits.or n1 (Bits.shr n1 2)
        n3 = Bits.or n2 (Bits.shr n2 4)
        n4 = Bits.or n3 (Bits.shr n3 8)
        n5 = Bits.or n4 (Bits.shr n4 16)
    in n5 + 1

-- | Optimal workgroup size (power of two, max 256)
optimalWorkgroupSize :: Int -> Int
optimalWorkgroupSize requested =
  clampInt 1 256 (nextPowerOfTwo requested)

-- | Product of array elements
productArray :: Array Int -> Int
productArray = product

-- | Sum of array elements
sumArray :: Array Number -> Number
sumArray = sum

-- | Check if value is in array
containsInt :: Int -> Array Int -> Boolean
containsInt = elem

-- | Zero vector constants
zeroVec2 :: Vec2
zeroVec2 = { x: zero, y: zero }

zeroVec3 :: Vec3
zeroVec3 = { x: zero, y: zero, z: zero }

zeroVec4 :: Vec4
zeroVec4 = { x: zero, y: zero, z: zero, w: zero }

-- | One vector constants
oneVec2 :: Vec2
oneVec2 = { x: one, y: one }

oneVec3 :: Vec3
oneVec3 = { x: one, y: one, z: one }

oneVec4 :: Vec4
oneVec4 = { x: one, y: one, z: one, w: one }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // algebraic utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add vectors using Semiring
addVecSemiring :: forall a. Semiring a => { x :: a, y :: a } -> { x :: a, y :: a } -> { x :: a, y :: a }
addVecSemiring v1 v2 = { x: v1.x + v2.x, y: v1.y + v2.y }

-- | Negate vector using Ring
negateVecRing :: forall a. Ring a => { x :: a, y :: a } -> { x :: a, y :: a }
negateVecRing v = { x: negate v.x, y: negate v.y }

-- | Identity function for kernel transforms
identityTransform :: TextKernel -> TextKernel
identityTransform = identity

-- | Conditional kernel selection using otherwise pattern
selectKernel :: Boolean -> TextKernel -> TextKernel -> TextKernel
selectKernel cond k1 k2
  | cond = k1
  | otherwise = k2

-- | Chain kernel operations using bind
chainKernelEffects :: forall m a b. Bind m => m a -> (a -> m b) -> m b
chainKernelEffects ma f = ma `bind` f

-- | Curry a kernel config function
curryKernelConfig :: ((Int /\ Int) -> TextKernel) -> Int -> Int -> TextKernel
curryKernelConfig f = curry f

-- | Uncurry a kernel config function
uncurryKernelConfig :: (Int -> Int -> TextKernel) -> (Int /\ Int) -> TextKernel
uncurryKernelConfig f = uncurry f

-- | Swap dimensions in a tuple
swapDimensions :: forall a b. Tuple a b -> Tuple b a
swapDimensions = swap

-- | Right fold over kernels (builds structure from right)
foldrKernels :: forall a. (TextKernel -> a -> a) -> a -> Array TextKernel -> a
foldrKernels f z kernels = foldr f z kernels

-- | Map kernels to monoidal summary
foldMapKernels :: forall m. Monoid m => (TextKernel -> m) -> Array TextKernel -> m
foldMapKernels f kernels = foldMap f kernels

-- | Sequence kernel effects
sequenceKernelEffects :: forall m. Applicative m => Array (m TextKernel) -> m (Array TextKernel)
sequenceKernelEffects = sequence

-- | For-each kernel (flipped traverse)
forEachKernel :: forall m a. Applicative m => Array a -> (a -> m TextKernel) -> m (Array TextKernel)
forEachKernel = for

-- | Check if a number is finite using Data.Number
isNumberFinite :: Number -> Boolean
isNumberFinite n = Number.isFinite n

-- | Bounded workgroup check using top/bottom
isWorkgroupInBounds :: Int -> Boolean
isWorkgroupInBounds x = x >= (bottom :: Int) && x <= (top :: Int)

-- | Get bounded range for a type
boundedRange :: forall a. Bounded a => { min :: a, max :: a }
boundedRange = { min: bottom, max: top }

-- | Compare kernel costs returning Ordering
orderKernelsByCost :: TextKernel -> TextKernel -> Ordering
orderKernelsByCost k1 k2 =
  let c1 = estimateTextKernelCost k1
      c2 = estimateTextKernelCost k2
  in if c1 < c2 then LT
     else if c1 > c2 then GT
     else EQ

-- | Create a dimension tuple directly
dimensionPair :: Int -> Int -> Int /\ Int
dimensionPair w h = w /\ h

-- | Witness that Array is Traversable
traversableArrayWitness :: forall a. Traversable Array => Array a -> Array a
traversableArrayWitness = identity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ghostty-style terminal rendering pipeline
-- |
-- | Optimized for 120fps terminal with:
-- | - MSDF for sharp text at any size
-- | - RGB subpixel rendering
-- | - Block cursor with blink
ghosttyTerminalPipeline :: Int -> Int -> TextKernel
ghosttyTerminalPipeline cols rows =
  let
    config = terminalConfig cols rows
    
    layout = KernelTextLayout $ TextLayoutKernel
      { runs: []
      , direction: LayoutLTR
      , lineHeight: 1.0
      , maxWidth: 0.0
      , alignX: 0.0
      , alignY: 0.0
      , tabWidth: 8
      , config
      }
    
    subpixel = KernelSubpixelAA $ SubpixelAAKernel
      { mode: SubpixelRGB
      , filter: FilterGaussian
      , gamma: 1.8
      , contrast: 0.5
      , config
      }
    
    cursor = KernelCursorBlink $ CursorBlinkKernel
      { style: CursorBlock
      , blinkRate: 1.0
      , blinkDuty: 0.5
      , fadeTime: 150.0
      , cursorX: 0
      , cursorY: 0
      , colorR: 0.9
      , colorG: 0.9
      , colorB: 0.9
      , config
      }
  in
    KernelTextSequence [layout, subpixel, cursor]

-- | IDE editor pipeline
-- |
-- | Balanced quality/performance for code editing:
-- | - SDF for flexibility
-- | - Optional subpixel
-- | - Bar cursor
ideEditorPipeline :: Int -> Int -> TextKernel
ideEditorPipeline width height =
  let
    config = editorConfig width height
    
    layout = KernelTextLayout $ TextLayoutKernel
      { runs: []
      , direction: LayoutLTR
      , lineHeight: 1.4
      , maxWidth: Int.toNumber width
      , alignX: 0.0
      , alignY: 0.0
      , tabWidth: 4
      , config
      }
    
    subpixel = KernelSubpixelAA $ SubpixelAAKernel
      { mode: SubpixelRGB
      , filter: FilterLinear
      , gamma: 2.0
      , contrast: 0.4
      , config
      }
    
    cursor = KernelCursorBlink $ CursorBlinkKernel
      { style: CursorBar
      , blinkRate: 0.5
      , blinkDuty: 0.5
      , fadeTime: 200.0
      , cursorX: 0
      , cursorY: 0
      , colorR: 0.3
      , colorG: 0.5
      , colorB: 1.0
      , config
      }
  in
    KernelTextSequence [layout, subpixel, cursor]

-- | UI label pipeline
-- |
-- | High quality for UI text:
-- | - MSDF for crisp rendering
-- | - Grayscale AA (works on any display)
-- | - No cursor
uiLabelPipeline :: Int -> Int -> TextKernel
uiLabelPipeline width height =
  let
    config = editorConfig width height
    
    layout = KernelTextLayout $ TextLayoutKernel
      { runs: []
      , direction: LayoutLTR
      , lineHeight: 1.2
      , maxWidth: Int.toNumber width
      , alignX: 0.5
      , alignY: 0.5
      , tabWidth: 4
      , config
      }
    
    subpixel = KernelSubpixelAA $ SubpixelAAKernel
      { mode: SubpixelNone
      , filter: FilterGaussian
      , gamma: 2.2
      , contrast: 0.5
      , config
      }
  in
    KernelTextSequence [layout, subpixel]

-- | Game HUD pipeline
-- |
-- | Performance-optimized for games:
-- | - Basic SDF
-- | - No subpixel (too expensive)
-- | - Outline for visibility
gameHUDPipeline :: Int -> Int -> TextKernel
gameHUDPipeline width height =
  let
    config = editorConfig width height
    
    layout = KernelTextLayout $ TextLayoutKernel
      { runs: []
      , direction: LayoutLTR
      , lineHeight: 1.0
      , maxWidth: 0.0
      , alignX: 0.0
      , alignY: 0.0
      , tabWidth: 4
      , config
      }
    
    effects = KernelTextMask $ TextMaskKernel
      { effects: 
          [ EffectOutline
              { width: 2.0
              , colorR: 0.0
              , colorG: 0.0
              , colorB: 0.0
              , colorA: 0.8
              }
          ]
      , config
      }
  in
    KernelTextSequence [layout, effects]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fold left over array
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f init arr =
  case Array.uncons arr of
    Nothing -> init
    Just { head, tail } -> foldlArray f (f init head) tail
