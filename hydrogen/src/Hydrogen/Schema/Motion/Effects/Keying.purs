-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // motion // effects // keying
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keying Effects — Professional compositing key extraction.
-- |
-- | ## After Effects Parity
-- |
-- | Implements industry-standard keying effects:
-- |
-- | - **Keylight**: Screen-based chroma keyer (industry standard)
-- | - **ChromaKey**: Simple YUV-based chroma keyer
-- | - **LumaKey**: Luminance-based key extraction
-- | - **ColorRange**: Select pixels by color range
-- | - **LinearColorKey**: Linear color space keyer
-- |
-- | ## GPU Shader Pattern
-- |
-- | All keying effects output an alpha channel:
-- | ```glsl
-- | float keyAlpha = computeKey(inputColor, keyParams);
-- | outputColor = vec4(inputColor.rgb, keyAlpha);
-- | ```
-- |
-- | ## Bounded Properties
-- |
-- | All properties use bounded types for deterministic rendering.

module Hydrogen.Schema.Motion.Effects.Keying
  ( -- * Keylight (Screen-Based Chroma Key)
    KeylightEffect
  , defaultKeylight
  , keylightWithScreenColor
  
  -- * Keylight Properties
  , ScreenGain
  , screenGain
  , unwrapScreenGain
  , ScreenBalance
  , screenBalance
  , unwrapScreenBalance
  , DespillBias
  , despillBias
  , unwrapDespillBias
  
  -- * Chroma Key
  , ChromaKeyEffect
  , defaultChromaKey
  , chromaKeyWithColor
  
  -- * Luma Key
  , LumaKeyEffect
  , LumaKeyType(..)
  , defaultLumaKey
  , lumaKeyBrightness
  , lumaKeyDarkness
  
  -- * Color Range
  , ColorRangeEffect
  , defaultColorRange
  
  -- * Linear Color Key
  , LinearColorKeyEffect
  , LinearKeyOperation(..)
  , defaultLinearColorKey
  
  -- * Edge Refinement (shared)
  , EdgeRefinement
  , defaultEdgeRefinement
  , edgeRefinement
  
  -- * Spill Suppression (shared)
  , SpillSuppression
  , defaultSpillSuppression
  , spillSuppression
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , ($)
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
  , compare
  , min
  , max
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , show
  , map
  , pure
  )
import Data.Ord (abs)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // bounded // key types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Screen Gain — amplifies screen difference (0.0 to 200.0).
-- |
-- | Higher values = more aggressive key extraction.
newtype ScreenGain = ScreenGain Number

derive instance eqScreenGain :: Eq ScreenGain
derive instance ordScreenGain :: Ord ScreenGain

instance showScreenGain :: Show ScreenGain where
  show (ScreenGain g) = show g

-- | Create ScreenGain (clamped 0.0-200.0).
screenGain :: Number -> ScreenGain
screenGain n = ScreenGain (clampNumber 0.0 200.0 n)

-- | Extract value.
unwrapScreenGain :: ScreenGain -> Number
unwrapScreenGain (ScreenGain g) = g

-- | Screen Balance — color channel weighting (-100.0 to 100.0).
-- |
-- | Negative = favors secondary screen color.
-- | Positive = favors primary screen color.
newtype ScreenBalance = ScreenBalance Number

derive instance eqScreenBalance :: Eq ScreenBalance
derive instance ordScreenBalance :: Ord ScreenBalance

instance showScreenBalance :: Show ScreenBalance where
  show (ScreenBalance b) = show b

-- | Create ScreenBalance (clamped -100.0 to 100.0).
screenBalance :: Number -> ScreenBalance
screenBalance n = ScreenBalance (clampNumber (-100.0) 100.0 n)

-- | Extract value.
unwrapScreenBalance :: ScreenBalance -> Number
unwrapScreenBalance (ScreenBalance b) = b

-- | Despill Bias — shifts spill correction color (-100.0 to 100.0).
-- |
-- | Used to adjust the color replacement for spill areas.
newtype DespillBias = DespillBias Number

derive instance eqDespillBias :: Eq DespillBias
derive instance ordDespillBias :: Ord DespillBias

instance showDespillBias :: Show DespillBias where
  show (DespillBias b) = show b

-- | Create DespillBias (clamped -100.0 to 100.0).
despillBias :: Number -> DespillBias
despillBias n = DespillBias (clampNumber (-100.0) 100.0 n)

-- | Extract value.
unwrapDespillBias :: DespillBias -> Number
unwrapDespillBias (DespillBias b) = b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // edge // refinement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Edge Refinement — shared edge treatment settings.
-- |
-- | Used by all keying effects for edge quality control.
type EdgeRefinement =
  { grow :: Number           -- ^ Expand/contract matte (-100 to 100)
  , softness :: Number       -- ^ Edge softness (0 to 100)
  , clip :: Number           -- ^ Clip edge (0 to 100)
  , choke :: Number          -- ^ Choke matte (-100 to 100)
  }

-- | Default edge refinement (no modification).
defaultEdgeRefinement :: EdgeRefinement
defaultEdgeRefinement =
  { grow: 0.0
  , softness: 0.0
  , clip: 0.0
  , choke: 0.0
  }

-- | Create edge refinement with bounds checking.
edgeRefinement :: Number -> Number -> Number -> Number -> EdgeRefinement
edgeRefinement g s cl ch =
  { grow: clampNumber (-100.0) 100.0 g
  , softness: clampNumber 0.0 100.0 s
  , clip: clampNumber 0.0 100.0 cl
  , choke: clampNumber (-100.0) 100.0 ch
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // spill // suppression
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spill Suppression — remove color spill from keyed edges.
type SpillSuppression =
  { enabled :: Boolean
  , amount :: Number         -- ^ Suppression strength (0 to 100)
  , saturation :: Number     -- ^ Affect saturation (0 to 100)
  , luminance :: Number      -- ^ Affect luminance (0 to 100)
  }

-- | Default spill suppression (enabled, moderate strength).
defaultSpillSuppression :: SpillSuppression
defaultSpillSuppression =
  { enabled: true
  , amount: 50.0
  , saturation: 100.0
  , luminance: 100.0
  }

-- | Create spill suppression with bounds checking.
spillSuppression :: Boolean -> Number -> Number -> Number -> SpillSuppression
spillSuppression e a s l =
  { enabled: e
  , amount: clampNumber 0.0 100.0 a
  , saturation: clampNumber 0.0 100.0 s
  , luminance: clampNumber 0.0 100.0 l
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // keylight
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keylight Effect — Industry-standard screen-based chroma keyer.
-- |
-- | Based on the Foundry Keylight algorithm. Analyzes screen color
-- | and extracts foreground with high-quality edge detail.
-- |
-- | ## Key Properties
-- |
-- | - screenColor: The green/blue screen color to remove
-- | - screenGain: How aggressively to extract the key
-- | - screenBalance: Adjust for uneven lighting
-- | - despillBias: Color to replace spill areas
-- | - clipBlack/clipWhite: Clean up matte edges
type KeylightEffect =
  { screenColor :: RGB           -- ^ Primary screen color to key
  , screenGain :: ScreenGain     -- ^ Gain applied to screen difference
  , screenBalance :: ScreenBalance -- ^ Balance between channels
  , despillBias :: DespillBias   -- ^ Despill color shift
  , clipBlack :: Number          -- ^ Clip dark values (0-100)
  , clipWhite :: Number          -- ^ Clip light values (0-100)
  , screenSoftness :: Number     -- ^ Screen extraction softness (0-100)
  , edge :: EdgeRefinement       -- ^ Edge treatment
  , spill :: SpillSuppression    -- ^ Spill suppression
  }

-- | Default Keylight (green screen).
defaultKeylight :: KeylightEffect
defaultKeylight =
  { screenColor: rgb 0 177 64    -- Standard green screen
  , screenGain: screenGain 100.0
  , screenBalance: screenBalance 0.0
  , despillBias: despillBias 0.0
  , clipBlack: 0.0
  , clipWhite: 100.0
  , screenSoftness: 0.0
  , edge: defaultEdgeRefinement
  , spill: defaultSpillSuppression
  }

-- | Create Keylight with specified screen color.
keylightWithScreenColor :: RGB -> KeylightEffect
keylightWithScreenColor color =
  { screenColor: color
  , screenGain: screenGain 100.0
  , screenBalance: screenBalance 0.0
  , despillBias: despillBias 0.0
  , clipBlack: 0.0
  , clipWhite: 100.0
  , screenSoftness: 0.0
  , edge: defaultEdgeRefinement
  , spill: defaultSpillSuppression
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // chroma // key
-- ═════════════════════════════════════════════════════════════════════════════

-- | ChromaKey Effect — Simple YUV-based chroma keyer.
-- |
-- | Less sophisticated than Keylight but faster and useful for
-- | clean screen shots.
type ChromaKeyEffect =
  { keyColor :: RGB              -- ^ Color to key out
  , tolerance :: Number          -- ^ Color matching tolerance (0-100)
  , softness :: Number           -- ^ Edge softness (0-100)
  , thinning :: Number           -- ^ Thin the matte (0-100)
  , edge :: EdgeRefinement       -- ^ Edge treatment
  }

-- | Default ChromaKey (green).
defaultChromaKey :: ChromaKeyEffect
defaultChromaKey =
  { keyColor: rgb 0 177 64
  , tolerance: 25.0
  , softness: 10.0
  , thinning: 0.0
  , edge: defaultEdgeRefinement
  }

-- | Create ChromaKey with specified color.
chromaKeyWithColor :: RGB -> ChromaKeyEffect
chromaKeyWithColor color =
  { keyColor: color
  , tolerance: 25.0
  , softness: 10.0
  , thinning: 0.0
  , edge: defaultEdgeRefinement
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // luma // key
-- ═════════════════════════════════════════════════════════════════════════════

-- | Luma Key Type — what to key out.
data LumaKeyType
  = LKTKeyOutBrighter  -- ^ Key out pixels brighter than threshold
  | LKTKeyOutDarker    -- ^ Key out pixels darker than threshold
  | LKTKeyOutSimilar   -- ^ Key out pixels with similar luminance
  | LKTKeyOutDissimilar -- ^ Key out pixels with different luminance

derive instance eqLumaKeyType :: Eq LumaKeyType
derive instance ordLumaKeyType :: Ord LumaKeyType

instance showLumaKeyType :: Show LumaKeyType where
  show LKTKeyOutBrighter = "key-out-brighter"
  show LKTKeyOutDarker = "key-out-darker"
  show LKTKeyOutSimilar = "key-out-similar"
  show LKTKeyOutDissimilar = "key-out-dissimilar"

-- | LumaKey Effect — Luminance-based key extraction.
-- |
-- | Keys based on brightness values rather than color.
-- | Useful for shadows, highlights, or grayscale sources.
type LumaKeyEffect =
  { keyType :: LumaKeyType       -- ^ What to key out
  , threshold :: Number          -- ^ Luminance threshold (0-100)
  , tolerance :: Number          -- ^ Luminance tolerance (0-100)
  , softness :: Number           -- ^ Edge softness (0-100)
  , edge :: EdgeRefinement       -- ^ Edge treatment
  }

-- | Default LumaKey (key out dark).
defaultLumaKey :: LumaKeyEffect
defaultLumaKey =
  { keyType: LKTKeyOutDarker
  , threshold: 50.0
  , tolerance: 25.0
  , softness: 10.0
  , edge: defaultEdgeRefinement
  }

-- | LumaKey preset for extracting bright areas.
lumaKeyBrightness :: LumaKeyEffect
lumaKeyBrightness =
  { keyType: LKTKeyOutDarker
  , threshold: 25.0
  , tolerance: 20.0
  , softness: 5.0
  , edge: defaultEdgeRefinement
  }

-- | LumaKey preset for extracting dark areas.
lumaKeyDarkness :: LumaKeyEffect
lumaKeyDarkness =
  { keyType: LKTKeyOutBrighter
  , threshold: 75.0
  , tolerance: 20.0
  , softness: 5.0
  , edge: defaultEdgeRefinement
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // color // range
-- ═════════════════════════════════════════════════════════════════════════════

-- | ColorRange Effect — Select pixels by LAB color range.
-- |
-- | Uses LAB color space for perceptually uniform selection.
type ColorRangeEffect =
  { previewMode :: Boolean       -- ^ Show selection visualization
  , selectionColor :: RGB        -- ^ Center of color range
  , fuzziness :: Number          -- ^ Selection falloff (0-200)
  , rangeL :: { low :: Number, high :: Number }  -- ^ Lightness range
  , rangeA :: { low :: Number, high :: Number }  -- ^ A channel range
  , rangeB :: { low :: Number, high :: Number }  -- ^ B channel range
  , edge :: EdgeRefinement       -- ^ Edge treatment
  }

-- | Default ColorRange.
defaultColorRange :: ColorRangeEffect
defaultColorRange =
  { previewMode: false
  , selectionColor: rgb 0 177 64
  , fuzziness: 40.0
  , rangeL: { low: 0.0, high: 100.0 }
  , rangeA: { low: -128.0, high: 127.0 }
  , rangeB: { low: -128.0, high: 127.0 }
  , edge: defaultEdgeRefinement
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // linear // color // key
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear Key Operation — how to combine key with original.
data LinearKeyOperation
  = LKOKeyColors         -- ^ Key based on color
  | LKOMask              -- ^ Output as mask
  | LKOKeepColors        -- ^ Keep matched colors
  | LKODropColors        -- ^ Drop matched colors

derive instance eqLinearKeyOperation :: Eq LinearKeyOperation
derive instance ordLinearKeyOperation :: Ord LinearKeyOperation

instance showLinearKeyOperation :: Show LinearKeyOperation where
  show LKOKeyColors = "key-colors"
  show LKOMask = "mask"
  show LKOKeepColors = "keep-colors"
  show LKODropColors = "drop-colors"

-- | LinearColorKey Effect — Linear color space keyer.
-- |
-- | Works in linear color space for more accurate keying.
type LinearColorKeyEffect =
  { keyColor :: RGB              -- ^ Color to key
  , operation :: LinearKeyOperation -- ^ Key operation mode
  , matchingTolerance :: Number  -- ^ Color match tolerance (0-100)
  , matchingSoftness :: Number   -- ^ Match edge softness (0-100)
  , edge :: EdgeRefinement       -- ^ Edge treatment
  }

-- | Default LinearColorKey (green).
defaultLinearColorKey :: LinearColorKeyEffect
defaultLinearColorKey =
  { keyColor: rgb 0 177 64
  , operation: LKOKeyColors
  , matchingTolerance: 10.0
  , matchingSoftness: 10.0
  , edge: defaultEdgeRefinement
  }
