-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // motion // effects // matte
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Matte Effects — Alpha channel and edge refinement effects.
-- |
-- | ## After Effects Parity
-- |
-- | Implements AE's Matte effect category:
-- |
-- | - **Simple Choker**: Expand/contract matte edges
-- | - **Matte Choker**: Advanced matte edge refinement
-- | - **Refine Matte**: Professional edge refinement (Roto Brush output)
-- | - **Set Matte**: Use another layer's channel as matte
-- | - **Channel Combiner**: Combine channels from multiple sources
-- |
-- | ## GPU Shader Pattern
-- |
-- | Matte effects operate on alpha channels:
-- | ```glsl
-- | float newAlpha = refineAlpha(inputAlpha, edgeParams);
-- | outputColor = vec4(inputColor.rgb, newAlpha);
-- | ```
-- |
-- | ## Bounded Properties
-- |
-- | All properties use bounded types for deterministic rendering.

module Hydrogen.Schema.Motion.Effects.Matte
  ( -- * Simple Choker
    SimpleChokerEffect
  , defaultSimpleChoker
  , simpleChokerExpand
  , simpleChokerContract
  , simpleChokerWithAmount
  
  -- * Matte Choker
  , MatteChokerEffect
  , GeometricSoftness
  , geometricSoftness
  , unwrapGeometricSoftness
  , defaultMatteChoker
  , matteChokerWithSpread
  
  -- * Refine Matte
  , RefineMatteEffect
  , RefinementType(..)
  , MotionBlurMode(..)
  , defaultRefineMatte
  , refineMatteWithSmooth
  , refineMatteWithFeather
  
  -- * Set Matte
  , SetMatteEffect
  , SetMatteChannel(..)
  , SetMatteStretch(..)
  , defaultSetMatte
  , setMatteFromLayer
  , setMatteFromChannel
  
  -- * Channel Combiner
  , ChannelCombinerEffect
  , CombinerSource(..)
  , defaultChannelCombiner
  , channelCombinerWithSources
  
  -- * Matte Cleanup
  , MatteCleanupEffect
  , CleanupOperation(..)
  , defaultMatteCleanup
  , matteCleanupWithBlur
  
  -- * Serialization
  , refinementTypeToString
  , motionBlurModeToString
  , setMatteChannelToString
  , setMatteStretchToString
  , combinerSourceToString
  , cleanupOperationToString
  
  -- * Effect Names
  , simpleChokerEffectName
  , matteChokerEffectName
  , refineMatteEffectName
  , setMatteEffectName
  , channelCombinerEffectName
  , matteCleanupEffectName
  
  -- * Effect Descriptions
  , describeSimpleChoker
  , describeMatteChoker
  , describeRefineMatte
  , describeSetMatte
  
  -- * Queries
  , isChokerExpanding
  , isChokerContracting
  , hasRefineMotionBlur
  , hasRefineSmooth
  , hasRefineFeather
  , isSetMatteInverted
  , hasCleanupBlur
  , hasCleanupContrast
  
  -- * Value Clamping
  , clampSimpleChokerValues
  , clampMatteChokerValues
  , clampRefineMatteValues
  
  -- * Composition
  , combineChokerAmounts
  , combineRefineSmooth
  
  -- * Advanced Queries
  , isChokerSignificant
  , isMatteChokerDualPass
  , isRefineMatteComplete
  , effectiveChokeAmount
  , chokerIntensityRatio
  , scaleChokerAmount
  , chokerDifference
  , compareChokerMagnitude
  , effectiveFeatherRadius
  , classifyRefineIntensity
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , Ordering
  , ($)
  , (<>)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , show
  , otherwise
  , compare
  , min
  , max
  )

import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // simple // choker
-- ═════════════════════════════════════════════════════════════════════════════

-- | Simple Choker Effect — Basic matte edge expansion/contraction.
-- |
-- | ## AE Properties
-- |
-- | - Choke Matte: Positive values contract, negative expand (-100 to 100)
-- |
-- | ## Use Cases
-- |
-- | - Remove green/blue fringing from keys
-- | - Clean up garbage matte edges
-- | - Expand slightly transparent edges
type SimpleChokerEffect =
  { chokeMatte :: Number  -- ^ Choke amount (-100 to 100)
  }

-- | Default simple choker: no change.
defaultSimpleChoker :: SimpleChokerEffect
defaultSimpleChoker =
  { chokeMatte: 0.0
  }

-- | Create simple choker that expands matte.
simpleChokerExpand :: Number -> SimpleChokerEffect
simpleChokerExpand amt =
  { chokeMatte: clampNumber (-100.0) 0.0 $ negate amt
  }

-- | Create simple choker that contracts matte.
simpleChokerContract :: Number -> SimpleChokerEffect
simpleChokerContract amt =
  { chokeMatte: clampNumber 0.0 100.0 amt
  }

-- | Create simple choker with specific amount (positive = contract).
simpleChokerWithAmount :: Number -> SimpleChokerEffect
simpleChokerWithAmount amt =
  { chokeMatte: clampNumber (-100.0) 100.0 amt
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // matte // choker
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geometric softness — bounded edge softness for Matte Choker.
-- | Range: 0.0 to 100.0 (percentage of edge softening)
newtype GeometricSoftness = GeometricSoftness Number

derive instance eqGeometricSoftness :: Eq GeometricSoftness
derive instance ordGeometricSoftness :: Ord GeometricSoftness

instance showGeometricSoftness :: Show GeometricSoftness where
  show (GeometricSoftness n) = "GeometricSoftness " <> show n

instance semigroupGeometricSoftness :: Semigroup GeometricSoftness where
  append (GeometricSoftness a) (GeometricSoftness b) = 
    GeometricSoftness $ min 100.0 (a + b)

-- | Create geometric softness (clamped to 0-100).
geometricSoftness :: Number -> GeometricSoftness
geometricSoftness n = GeometricSoftness $ clampNumber 0.0 100.0 n

-- | Extract numeric value.
unwrapGeometricSoftness :: GeometricSoftness -> Number
unwrapGeometricSoftness (GeometricSoftness n) = n

-- | Matte Choker Effect — Advanced matte edge refinement.
-- |
-- | ## AE Properties
-- |
-- | - Geometric Softness 1: First pass softness (0-100)
-- | - Choke 1: First pass choke (-100 to 100)
-- | - Geometric Softness 2: Second pass softness (0-100)
-- | - Choke 2: Second pass choke (-100 to 100)
-- | - Gray Level Softness: Gray edge handling (0-100)
-- |
-- | ## Use Cases
-- |
-- | - Multi-pass edge refinement
-- | - Complex key cleanup
-- | - Hair/fine detail preservation
type MatteChokerEffect =
  { geometricSoftness1 :: GeometricSoftness  -- ^ First pass softness
  , choke1 :: Number                          -- ^ First pass choke (-100 to 100)
  , geometricSoftness2 :: GeometricSoftness  -- ^ Second pass softness
  , choke2 :: Number                          -- ^ Second pass choke (-100 to 100)
  , grayLevelSoftness :: Number               -- ^ Gray edge handling (0-100)
  }

-- | Default matte choker: no change.
defaultMatteChoker :: MatteChokerEffect
defaultMatteChoker =
  { geometricSoftness1: geometricSoftness 0.0
  , choke1: 0.0
  , geometricSoftness2: geometricSoftness 0.0
  , choke2: 0.0
  , grayLevelSoftness: 0.0
  }

-- | Create matte choker with specific spread.
matteChokerWithSpread :: Number -> Number -> MatteChokerEffect
matteChokerWithSpread soft choke =
  { geometricSoftness1: geometricSoftness soft
  , choke1: clampNumber (-100.0) 100.0 choke
  , geometricSoftness2: geometricSoftness 0.0
  , choke2: 0.0
  , grayLevelSoftness: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // refine // matte
-- ═════════════════════════════════════════════════════════════════════════════

-- | Refinement type — edge processing algorithm.
data RefinementType
  = RTSmooth           -- ^ Smooth edges
  | RTFeather          -- ^ Feathered edges
  | RTChoke            -- ^ Contract edges
  | RTShiftEdge        -- ^ Shift edge inward/outward
  | RTReduceChatter    -- ^ Temporal consistency

derive instance eqRefinementType :: Eq RefinementType
derive instance ordRefinementType :: Ord RefinementType

instance showRefinementType :: Show RefinementType where
  show RTSmooth = "smooth"
  show RTFeather = "feather"
  show RTChoke = "choke"
  show RTShiftEdge = "shift-edge"
  show RTReduceChatter = "reduce-chatter"

-- | Motion blur mode — how to handle motion blur on mattes.
data MotionBlurMode
  = MBMNone            -- ^ No motion blur
  | MBMNormal          -- ^ Standard motion blur
  | MBMHighQuality     -- ^ High quality (more samples)

derive instance eqMotionBlurMode :: Eq MotionBlurMode
derive instance ordMotionBlurMode :: Ord MotionBlurMode

instance showMotionBlurMode :: Show MotionBlurMode where
  show MBMNone = "none"
  show MBMNormal = "normal"
  show MBMHighQuality = "high-quality"

-- | Refine Matte Effect — Professional edge refinement.
-- |
-- | ## AE Properties
-- |
-- | Based on Roto Brush Refine Edge functionality:
-- | - Smooth: Edge smoothing (0-100)
-- | - Feather: Edge feathering (0-250 pixels)
-- | - Choke: Edge contraction (-100 to 100%)
-- | - Shift Edge: Move edge position (-100 to 100%)
-- | - Reduce Chatter: Temporal consistency (0-100)
-- | - Motion Blur: Apply motion blur to matte
-- |
-- | ## Use Cases
-- |
-- | - Roto Brush output refinement
-- | - Hair and fine detail edges
-- | - Motion-tracked mattes
type RefineMatteEffect =
  { smooth :: Number               -- ^ Edge smoothing (0-100)
  , feather :: Number              -- ^ Edge feathering (0-250 pixels)
  , choke :: Number                -- ^ Edge contraction (-100 to 100%)
  , shiftEdge :: Number            -- ^ Edge shift (-100 to 100%)
  , reduceChatter :: Number        -- ^ Temporal consistency (0-100)
  , motionBlurMode :: MotionBlurMode
  , motionBlurSamples :: Int       -- ^ Blur samples (1-64)
  , motionBlurShutter :: Number    -- ^ Shutter angle (0-720 degrees)
  , decontaminate :: Boolean       -- ^ Color decontamination
  , decontaminateAmount :: Number  -- ^ Decontamination strength (0-100)
  }

-- | Default refine matte: minimal processing.
defaultRefineMatte :: RefineMatteEffect
defaultRefineMatte =
  { smooth: 0.0
  , feather: 0.0
  , choke: 0.0
  , shiftEdge: 0.0
  , reduceChatter: 0.0
  , motionBlurMode: MBMNone
  , motionBlurSamples: 16
  , motionBlurShutter: 180.0
  , decontaminate: false
  , decontaminateAmount: 100.0
  }

-- | Create refine matte with smooth.
refineMatteWithSmooth :: Number -> RefineMatteEffect
refineMatteWithSmooth amt =
  { smooth: clampNumber 0.0 100.0 amt
  , feather: 0.0
  , choke: 0.0
  , shiftEdge: 0.0
  , reduceChatter: 0.0
  , motionBlurMode: MBMNone
  , motionBlurSamples: 16
  , motionBlurShutter: 180.0
  , decontaminate: false
  , decontaminateAmount: 100.0
  }

-- | Create refine matte with feather.
refineMatteWithFeather :: Number -> RefineMatteEffect
refineMatteWithFeather amt =
  { smooth: 0.0
  , feather: clampNumber 0.0 250.0 amt
  , choke: 0.0
  , shiftEdge: 0.0
  , reduceChatter: 0.0
  , motionBlurMode: MBMNone
  , motionBlurSamples: 16
  , motionBlurShutter: 180.0
  , decontaminate: false
  , decontaminateAmount: 100.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // set // matte
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set Matte channel source — which channel to use as matte.
data SetMatteChannel
  = SMCRed             -- ^ Red channel
  | SMCGreen           -- ^ Green channel
  | SMCBlue            -- ^ Blue channel
  | SMCAlpha           -- ^ Alpha channel
  | SMCLuminance       -- ^ Luminance (brightness)
  | SMCHue             -- ^ Hue value
  | SMCSaturation      -- ^ Saturation value
  | SMCLightness       -- ^ Lightness value
  | SMCFullOn          -- ^ Full white (no mask)
  | SMCFullOff         -- ^ Full black (full mask)

derive instance eqSetMatteChannel :: Eq SetMatteChannel
derive instance ordSetMatteChannel :: Ord SetMatteChannel

instance showSetMatteChannel :: Show SetMatteChannel where
  show SMCRed = "red"
  show SMCGreen = "green"
  show SMCBlue = "blue"
  show SMCAlpha = "alpha"
  show SMCLuminance = "luminance"
  show SMCHue = "hue"
  show SMCSaturation = "saturation"
  show SMCLightness = "lightness"
  show SMCFullOn = "full-on"
  show SMCFullOff = "full-off"

-- | Set Matte stretch mode — how to fit matte to layer.
data SetMatteStretch
  = SMSStretch         -- ^ Stretch matte to fit
  | SMSTile            -- ^ Tile matte
  | SMSCenter          -- ^ Center matte (no stretch)

derive instance eqSetMatteStretch :: Eq SetMatteStretch
derive instance ordSetMatteStretch :: Ord SetMatteStretch

instance showSetMatteStretch :: Show SetMatteStretch where
  show SMSStretch = "stretch"
  show SMSTile = "tile"
  show SMSCenter = "center"

-- | Set Matte Effect — Use another layer's channel as matte.
-- |
-- | ## AE Properties
-- |
-- | - Take Matte From Layer: Source layer index
-- | - Use For Matte: Which channel (red/green/blue/alpha/luminance)
-- | - Invert Matte: Flip black/white
-- | - If Layer Sizes Differ: How to fit (stretch/tile/center)
-- | - Stretch Matte to Fit: Resize matte to layer bounds
-- | - Premultiply Matte Layer: Handle premultiplied alpha
-- |
-- | ## Use Cases
-- |
-- | - Luma matte from luminance
-- | - Custom channel extraction
-- | - Layer-based masking
type SetMatteEffect =
  { takeMatteFromLayer :: Int        -- ^ Source layer index
  , useForMatte :: SetMatteChannel   -- ^ Channel to use
  , invertMatte :: Boolean           -- ^ Invert the matte
  , stretchMode :: SetMatteStretch   -- ^ How to fit
  , premultiplyMatte :: Boolean      -- ^ Handle premultiplied
  }

-- | Default set matte: alpha from layer 1.
defaultSetMatte :: SetMatteEffect
defaultSetMatte =
  { takeMatteFromLayer: 1
  , useForMatte: SMCAlpha
  , invertMatte: false
  , stretchMode: SMSStretch
  , premultiplyMatte: false
  }

-- | Create set matte from specific layer.
setMatteFromLayer :: Int -> SetMatteEffect
setMatteFromLayer layer =
  { takeMatteFromLayer: layer
  , useForMatte: SMCAlpha
  , invertMatte: false
  , stretchMode: SMSStretch
  , premultiplyMatte: false
  }

-- | Create set matte from specific channel.
setMatteFromChannel :: Int -> SetMatteChannel -> SetMatteEffect
setMatteFromChannel layer channel =
  { takeMatteFromLayer: layer
  , useForMatte: channel
  , invertMatte: false
  , stretchMode: SMSStretch
  , premultiplyMatte: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // channel // combiner
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combiner source — where to get channel data.
data CombinerSource
  = CSSourceRed        -- ^ Source red channel
  | CSSourceGreen      -- ^ Source green channel
  | CSSourceBlue       -- ^ Source blue channel
  | CSSourceAlpha      -- ^ Source alpha channel
  | CSSourceLuma       -- ^ Source luminance
  | CSLayerRed Int     -- ^ Layer red (by index)
  | CSLayerGreen Int   -- ^ Layer green (by index)
  | CSLayerBlue Int    -- ^ Layer blue (by index)
  | CSLayerAlpha Int   -- ^ Layer alpha (by index)
  | CSLayerLuma Int    -- ^ Layer luminance (by index)
  | CSFullOn           -- ^ Full white
  | CSFullOff          -- ^ Full black
  | CSInvert CombinerSource  -- ^ Inverted source

derive instance eqCombinerSource :: Eq CombinerSource
derive instance ordCombinerSource :: Ord CombinerSource

instance showCombinerSource :: Show CombinerSource where
  show CSSourceRed = "source-red"
  show CSSourceGreen = "source-green"
  show CSSourceBlue = "source-blue"
  show CSSourceAlpha = "source-alpha"
  show CSSourceLuma = "source-luma"
  show (CSLayerRed i) = "layer-" <> show i <> "-red"
  show (CSLayerGreen i) = "layer-" <> show i <> "-green"
  show (CSLayerBlue i) = "layer-" <> show i <> "-blue"
  show (CSLayerAlpha i) = "layer-" <> show i <> "-alpha"
  show (CSLayerLuma i) = "layer-" <> show i <> "-luma"
  show CSFullOn = "full-on"
  show CSFullOff = "full-off"
  show (CSInvert s) = "invert(" <> show s <> ")"

-- | Channel Combiner Effect — Combine channels from multiple sources.
-- |
-- | ## AE Properties
-- |
-- | Allows mapping any input channel to any output channel:
-- | - Red Output: Source for red channel
-- | - Green Output: Source for green channel
-- | - Blue Output: Source for blue channel
-- | - Alpha Output: Source for alpha channel
-- |
-- | ## Use Cases
-- |
-- | - Channel swapping
-- | - Multi-layer channel composition
-- | - Custom matte construction
type ChannelCombinerEffect =
  { redOutput :: CombinerSource      -- ^ Source for red
  , greenOutput :: CombinerSource    -- ^ Source for green
  , blueOutput :: CombinerSource     -- ^ Source for blue
  , alphaOutput :: CombinerSource    -- ^ Source for alpha
  }

-- | Default channel combiner: passthrough.
defaultChannelCombiner :: ChannelCombinerEffect
defaultChannelCombiner =
  { redOutput: CSSourceRed
  , greenOutput: CSSourceGreen
  , blueOutput: CSSourceBlue
  , alphaOutput: CSSourceAlpha
  }

-- | Create channel combiner with custom sources.
channelCombinerWithSources :: CombinerSource -> CombinerSource -> CombinerSource -> CombinerSource -> ChannelCombinerEffect
channelCombinerWithSources r g b a =
  { redOutput: r
  , greenOutput: g
  , blueOutput: b
  , alphaOutput: a
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // matte // cleanup
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cleanup operation — what processing to apply.
data CleanupOperation
  = COBlur             -- ^ Blur edges
  | COContrast         -- ^ Increase contrast
  | COGamma            -- ^ Gamma correction
  | COShrink           -- ^ Shrink matte
  | COExpand           -- ^ Expand matte
  | COSimplify         -- ^ Simplify edges

derive instance eqCleanupOperation :: Eq CleanupOperation
derive instance ordCleanupOperation :: Ord CleanupOperation

instance showCleanupOperation :: Show CleanupOperation where
  show COBlur = "blur"
  show COContrast = "contrast"
  show COGamma = "gamma"
  show COShrink = "shrink"
  show COExpand = "expand"
  show COSimplify = "simplify"

-- | Matte Cleanup Effect — General-purpose matte refinement.
-- |
-- | ## Properties
-- |
-- | Combines multiple cleanup operations:
-- | - Blur: Edge blur amount (0-100)
-- | - Contrast: Edge contrast (-100 to 100)
-- | - Gamma: Gamma curve (0.1 to 10.0)
-- | - Shrink/Expand: Size adjustment (-100 to 100)
-- | - Simplify: Edge simplification (0-100)
-- |
-- | ## Use Cases
-- |
-- | - Post-key cleanup
-- | - Garbage matte refinement
-- | - Quick edge fixes
type MatteCleanupEffect =
  { blur :: Number                   -- ^ Edge blur (0-100)
  , contrast :: Number               -- ^ Edge contrast (-100 to 100)
  , gamma :: Number                  -- ^ Gamma (0.1-10.0)
  , sizeAdjust :: Number             -- ^ Shrink/expand (-100 to 100)
  , simplify :: Number               -- ^ Edge simplification (0-100)
  , primaryOperation :: CleanupOperation  -- ^ Main operation
  }

-- | Default matte cleanup: no change.
defaultMatteCleanup :: MatteCleanupEffect
defaultMatteCleanup =
  { blur: 0.0
  , contrast: 0.0
  , gamma: 1.0
  , sizeAdjust: 0.0
  , simplify: 0.0
  , primaryOperation: COBlur
  }

-- | Create matte cleanup with blur.
matteCleanupWithBlur :: Number -> MatteCleanupEffect
matteCleanupWithBlur amt =
  { blur: clampNumber 0.0 100.0 amt
  , contrast: 0.0
  , gamma: 1.0
  , sizeAdjust: 0.0
  , simplify: 0.0
  , primaryOperation: COBlur
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RefinementType to string.
refinementTypeToString :: RefinementType -> String
refinementTypeToString = show

-- | Convert MotionBlurMode to string.
motionBlurModeToString :: MotionBlurMode -> String
motionBlurModeToString = show

-- | Convert SetMatteChannel to string.
setMatteChannelToString :: SetMatteChannel -> String
setMatteChannelToString = show

-- | Convert SetMatteStretch to string.
setMatteStretchToString :: SetMatteStretch -> String
setMatteStretchToString = show

-- | Convert CombinerSource to string.
combinerSourceToString :: CombinerSource -> String
combinerSourceToString = show

-- | Convert CleanupOperation to string.
cleanupOperationToString :: CleanupOperation -> String
cleanupOperationToString = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for Simple Choker.
simpleChokerEffectName :: SimpleChokerEffect -> String
simpleChokerEffectName _ = "Simple Choker"

-- | Effect name for Matte Choker.
matteChokerEffectName :: MatteChokerEffect -> String
matteChokerEffectName _ = "Matte Choker"

-- | Effect name for Refine Matte.
refineMatteEffectName :: RefineMatteEffect -> String
refineMatteEffectName _ = "Refine Matte"

-- | Effect name for Set Matte.
setMatteEffectName :: SetMatteEffect -> String
setMatteEffectName _ = "Set Matte"

-- | Effect name for Channel Combiner.
channelCombinerEffectName :: ChannelCombinerEffect -> String
channelCombinerEffectName _ = "Channel Combiner"

-- | Effect name for Matte Cleanup.
matteCleanupEffectName :: MatteCleanupEffect -> String
matteCleanupEffectName _ = "Matte Cleanup"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // effect // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Describe simple choker effect.
describeSimpleChoker :: SimpleChokerEffect -> String
describeSimpleChoker e =
  let
    typeStr = if e.chokeMatte > 0.0 then "contract" else if e.chokeMatte < 0.0 then "expand" else "none"
  in
    "SimpleChoker(" <> typeStr <> ": " <> show e.chokeMatte <> ")"

-- | Describe matte choker effect.
describeMatteChoker :: MatteChokerEffect -> String
describeMatteChoker e =
  "MatteChoker(choke1: " <> show e.choke1 
    <> ", soft1: " <> show (unwrapGeometricSoftness e.geometricSoftness1)
    <> ", choke2: " <> show e.choke2
    <> ")"

-- | Describe refine matte effect.
describeRefineMatte :: RefineMatteEffect -> String
describeRefineMatte e =
  "RefineMatte(smooth: " <> show e.smooth
    <> ", feather: " <> show e.feather <> "px"
    <> ", choke: " <> show e.choke <> "%"
    <> ")"

-- | Describe set matte effect.
describeSetMatte :: SetMatteEffect -> String
describeSetMatte e =
  let
    invertStr = if e.invertMatte then " inverted" else ""
  in
    "SetMatte(layer: " <> show e.takeMatteFromLayer
      <> ", channel: " <> show e.useForMatte
      <> invertStr
      <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if choker is expanding (negative value).
isChokerExpanding :: SimpleChokerEffect -> Boolean
isChokerExpanding e = e.chokeMatte < 0.0

-- | Check if choker is contracting (positive value).
isChokerContracting :: SimpleChokerEffect -> Boolean
isChokerContracting e = e.chokeMatte > 0.0

-- | Check if refine matte has motion blur enabled.
hasRefineMotionBlur :: RefineMatteEffect -> Boolean
hasRefineMotionBlur e = case e.motionBlurMode of
  MBMNone -> false
  _ -> true

-- | Check if refine matte has smoothing.
hasRefineSmooth :: RefineMatteEffect -> Boolean
hasRefineSmooth e = e.smooth > 0.0

-- | Check if refine matte has feathering.
hasRefineFeather :: RefineMatteEffect -> Boolean
hasRefineFeather e = e.feather > 0.0

-- | Check if set matte is inverted.
isSetMatteInverted :: SetMatteEffect -> Boolean
isSetMatteInverted e = e.invertMatte

-- | Check if cleanup has blur.
hasCleanupBlur :: MatteCleanupEffect -> Boolean
hasCleanupBlur e = e.blur > 0.0

-- | Check if cleanup has contrast adjustment.
hasCleanupContrast :: MatteCleanupEffect -> Boolean
hasCleanupContrast e = e.contrast > 0.0 || e.contrast < 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // value // clamping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp simple choker values to valid ranges.
clampSimpleChokerValues :: SimpleChokerEffect -> SimpleChokerEffect
clampSimpleChokerValues e =
  { chokeMatte: clampNumber (-100.0) 100.0 e.chokeMatte
  }

-- | Clamp matte choker values to valid ranges.
clampMatteChokerValues :: MatteChokerEffect -> MatteChokerEffect
clampMatteChokerValues e =
  { geometricSoftness1: geometricSoftness $ unwrapGeometricSoftness e.geometricSoftness1
  , choke1: clampNumber (-100.0) 100.0 e.choke1
  , geometricSoftness2: geometricSoftness $ unwrapGeometricSoftness e.geometricSoftness2
  , choke2: clampNumber (-100.0) 100.0 e.choke2
  , grayLevelSoftness: clampNumber 0.0 100.0 e.grayLevelSoftness
  }

-- | Clamp refine matte values to valid ranges.
clampRefineMatteValues :: RefineMatteEffect -> RefineMatteEffect
clampRefineMatteValues e =
  { smooth: clampNumber 0.0 100.0 e.smooth
  , feather: clampNumber 0.0 250.0 e.feather
  , choke: clampNumber (-100.0) 100.0 e.choke
  , shiftEdge: clampNumber (-100.0) 100.0 e.shiftEdge
  , reduceChatter: clampNumber 0.0 100.0 e.reduceChatter
  , motionBlurMode: e.motionBlurMode
  , motionBlurSamples: min 64 $ max 1 e.motionBlurSamples
  , motionBlurShutter: clampNumber 0.0 720.0 e.motionBlurShutter
  , decontaminate: e.decontaminate
  , decontaminateAmount: clampNumber 0.0 100.0 e.decontaminateAmount
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two choker amounts (additive, clamped).
combineChokerAmounts :: SimpleChokerEffect -> SimpleChokerEffect -> SimpleChokerEffect
combineChokerAmounts a b =
  { chokeMatte: clampNumber (-100.0) 100.0 $ a.chokeMatte + b.chokeMatte
  }

-- | Combine two refine matte smooth amounts (max).
combineRefineSmooth :: RefineMatteEffect -> RefineMatteEffect -> Number
combineRefineSmooth a b = max a.smooth b.smooth

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // advanced // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if choker amount is significant (>= 5 or <= -5).
isChokerSignificant :: SimpleChokerEffect -> Boolean
isChokerSignificant e = e.chokeMatte >= 5.0 || e.chokeMatte <= (-5.0)

-- | Check if matte choker uses both passes.
isMatteChokerDualPass :: MatteChokerEffect -> Boolean
isMatteChokerDualPass e = 
  (e.choke1 > 0.0 || e.choke1 < 0.0) && (e.choke2 > 0.0 || e.choke2 < 0.0)

-- | Check if refine matte is fully configured (smooth AND feather).
isRefineMatteComplete :: RefineMatteEffect -> Boolean
isRefineMatteComplete e = e.smooth >= 1.0 && e.feather >= 1.0

-- | Compute effective choke (taking into account all passes).
effectiveChokeAmount :: MatteChokerEffect -> Number
effectiveChokeAmount e = e.choke1 + e.choke2

-- | Compute choker intensity ratio (percentage of max).
chokerIntensityRatio :: SimpleChokerEffect -> Number
chokerIntensityRatio e
  | e.chokeMatte >= 0.0 = e.chokeMatte / 100.0
  | otherwise = negate e.chokeMatte / 100.0

-- | Scale a simple choker effect by a factor.
scaleChokerAmount :: Number -> SimpleChokerEffect -> SimpleChokerEffect
scaleChokerAmount factor e =
  { chokeMatte: clampNumber (-100.0) 100.0 $ e.chokeMatte * factor
  }

-- | Compute difference between two choker effects.
chokerDifference :: SimpleChokerEffect -> SimpleChokerEffect -> Number
chokerDifference a b = a.chokeMatte - b.chokeMatte

-- | Compare two simple choker effects by absolute magnitude.
compareChokerMagnitude :: SimpleChokerEffect -> SimpleChokerEffect -> Ordering
compareChokerMagnitude a b = 
  let
    absA = if a.chokeMatte >= 0.0 then a.chokeMatte else negate a.chokeMatte
    absB = if b.chokeMatte >= 0.0 then b.chokeMatte else negate b.chokeMatte
  in
    compare absA absB

-- | Compute the effective feather radius accounting for smooth.
effectiveFeatherRadius :: RefineMatteEffect -> Number
effectiveFeatherRadius e = e.feather + (e.smooth * 0.5)

-- | Classify refine matte by processing intensity.
classifyRefineIntensity :: RefineMatteEffect -> String
classifyRefineIntensity e
  | e.smooth >= 50.0 && e.feather >= 100.0 = "heavy"
  | e.smooth >= 20.0 || e.feather >= 50.0 = "medium"
  | e.smooth <= 5.0 && e.feather <= 10.0 = "light"
  | otherwise = "moderate"
