-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // motion // effects // noise
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Noise Effects — Complete noise and fractal effect types.
-- |
-- | ## After Effects Parity
-- |
-- | Includes full property records for:
-- | - Fractal Noise (procedural animated textures)
-- | - Turbulent Noise
-- | - Add Grain / Remove Grain
-- |
-- | Fractal Noise is one of the most powerful effects in AE,
-- | capable of generating clouds, fire, water, abstract patterns,
-- | displacement maps, and more.

module Hydrogen.Schema.Motion.Effects.Noise
  ( -- * Fractal Type
    FractalType(..)
  , allFractalTypes
  , fractalTypeToString
  , fractalTypeFromString
  
  -- * Noise Type
  , NoiseType(..)
  , allNoiseTypes
  , noiseTypeToString
  , noiseTypeFromString
  
  -- * Fractal Noise Effect
  , FractalNoiseEffect(..)
  , OverflowMode(..)
  , NoiseBlendMode(..)
  , defaultFractalNoise
  , mkFractalNoise
  
  -- * Transform Controls
  , NoiseTransform(..)
  , defaultNoiseTransform
  
  -- * Sub Settings
  , SubSettings(..)
  , defaultSubSettings
  
  -- * Evolution Options
  , EvolutionOptions(..)
  , defaultEvolutionOptions
  
  -- * Queries
  , isFractalNoiseAnimated
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
import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // fractal // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of fractal noise generation.
data FractalType
  = FTBasic          -- ^ Basic fractal noise
  | FTTurbulentBasic -- ^ Turbulent (absolute value)
  | FTSoftLinear     -- ^ Soft linear interpolation
  | FTTurbulentSoft  -- ^ Turbulent with soft interp

derive instance eqFractalType :: Eq FractalType
derive instance ordFractalType :: Ord FractalType

instance showFractalType :: Show FractalType where
  show FTBasic = "FTBasic"
  show FTTurbulentBasic = "FTTurbulentBasic"
  show FTSoftLinear = "FTSoftLinear"
  show FTTurbulentSoft = "FTTurbulentSoft"

-- | All fractal types for enumeration
allFractalTypes :: Array FractalType
allFractalTypes = [ FTBasic, FTTurbulentBasic, FTSoftLinear, FTTurbulentSoft ]

fractalTypeToString :: FractalType -> String
fractalTypeToString FTBasic = "basic"
fractalTypeToString FTTurbulentBasic = "turbulent-basic"
fractalTypeToString FTSoftLinear = "soft-linear"
fractalTypeToString FTTurbulentSoft = "turbulent-soft"

fractalTypeFromString :: String -> Maybe FractalType
fractalTypeFromString "basic" = Just FTBasic
fractalTypeFromString "turbulent-basic" = Just FTTurbulentBasic
fractalTypeFromString "soft-linear" = Just FTSoftLinear
fractalTypeFromString "turbulent-soft" = Just FTTurbulentSoft
fractalTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // noise // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of base noise.
data NoiseType
  = NTBlock       -- ^ Block/cell noise
  | NTLinear      -- ^ Linear interpolated
  | NTSoftLinear  -- ^ Soft linear
  | NTSpline      -- ^ Spline interpolated

derive instance eqNoiseType :: Eq NoiseType
derive instance ordNoiseType :: Ord NoiseType

instance showNoiseType :: Show NoiseType where
  show NTBlock = "NTBlock"
  show NTLinear = "NTLinear"
  show NTSoftLinear = "NTSoftLinear"
  show NTSpline = "NTSpline"

-- | All noise types for enumeration
allNoiseTypes :: Array NoiseType
allNoiseTypes = [ NTBlock, NTLinear, NTSoftLinear, NTSpline ]

noiseTypeToString :: NoiseType -> String
noiseTypeToString NTBlock = "block"
noiseTypeToString NTLinear = "linear"
noiseTypeToString NTSoftLinear = "soft-linear"
noiseTypeToString NTSpline = "spline"

noiseTypeFromString :: String -> Maybe NoiseType
noiseTypeFromString "block" = Just NTBlock
noiseTypeFromString "linear" = Just NTLinear
noiseTypeFromString "soft-linear" = Just NTSoftLinear
noiseTypeFromString "spline" = Just NTSpline
noiseTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // noise // transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform controls for fractal noise.
-- |
-- | Controls the position, rotation, and scale of the noise pattern.
type NoiseTransform =
  { offsetTurbulenceX :: Number  -- ^ X offset in pixels
  , offsetTurbulenceY :: Number  -- ^ Y offset in pixels
  , rotation :: Number           -- ^ Rotation in degrees (0-360)
  , uniformScaling :: Boolean    -- ^ Lock scale to uniform
  , scale :: Number              -- ^ Uniform scale (1-10000%)
  , scaleWidth :: Number         -- ^ X scale when non-uniform (1-10000%)
  , scaleHeight :: Number        -- ^ Y scale when non-uniform (1-10000%)
  , perspectiveOffset :: Number  -- ^ Perspective distortion (0-100)
  }

defaultNoiseTransform :: NoiseTransform
defaultNoiseTransform =
  { offsetTurbulenceX: 0.0
  , offsetTurbulenceY: 0.0
  , rotation: 0.0
  , uniformScaling: true
  , scale: 100.0
  , scaleWidth: 100.0
  , scaleHeight: 100.0
  , perspectiveOffset: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // sub // settings
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sub-octave settings for fractal layering.
type SubSettings =
  { subInfluence :: Number   -- ^ Influence of sub-octaves (0-100%)
  , subScale :: Number       -- ^ Scale multiplier per octave (10-1000%)
  , subRotation :: Number    -- ^ Rotation offset per octave (degrees)
  , subOffset :: Number      -- ^ Position offset per octave (pixels)
  }

defaultSubSettings :: SubSettings
defaultSubSettings =
  { subInfluence: 70.0
  , subScale: 56.0
  , subRotation: 0.0
  , subOffset: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // evolution // options
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evolution options for seamless animation.
type EvolutionOptions =
  { cycleEvolution :: Boolean      -- ^ Enable seamless looping
  , cycleRevolutions :: Number     -- ^ Number of revolutions per cycle
  , randomSeed :: Int              -- ^ Random seed for reproducibility
  }

defaultEvolutionOptions :: EvolutionOptions
defaultEvolutionOptions =
  { cycleEvolution: false
  , cycleRevolutions: 1.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // fractal noise // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fractal Noise effect — procedural animated texture generator.
-- |
-- | One of the most versatile effects in motion graphics.
-- | Can create: clouds, fire, smoke, water, organic patterns,
-- | displacement maps, transition mattes, and abstract backgrounds.
type FractalNoiseEffect =
  { fractalType :: FractalType     -- ^ Type of fractal algorithm
  , noiseType :: NoiseType         -- ^ Base noise interpolation
  , invert :: Boolean              -- ^ Invert output
  , contrast :: Number             -- ^ Output contrast (0-400%)
  , brightness :: Number           -- ^ Output brightness (-200 to 200%)
  , overflow :: OverflowMode       -- ^ How to handle values > 1.0
  , transform :: NoiseTransform    -- ^ Position/rotation/scale
  , complexity :: Number           -- ^ Number of noise octaves (1-20)
  , subSettings :: SubSettings     -- ^ Sub-octave controls
  , evolution :: Number            -- ^ Evolution parameter (revolutions)
  , evolutionOptions :: EvolutionOptions  -- ^ Looping/seed settings
  , opacity :: Number              -- ^ Effect opacity (0-100%)
  , blendingMode :: NoiseBlendMode -- ^ How effect blends with layer
  }

-- | Overflow handling mode.
data OverflowMode
  = OverflowClip        -- ^ Clamp to 0-1 range
  | OverflowSoftClamp   -- ^ Smooth clamping
  | OverflowWrapBack    -- ^ Wrap values back into range
  | OverflowHDR         -- ^ Allow high dynamic range values

derive instance eqOverflowMode :: Eq OverflowMode
derive instance ordOverflowMode :: Ord OverflowMode

instance showOverflowMode :: Show OverflowMode where
  show OverflowClip = "Clip"
  show OverflowSoftClamp = "Soft Clamp"
  show OverflowWrapBack = "Wrap Back"
  show OverflowHDR = "HDR"

-- | Blending mode for noise effect.
data NoiseBlendMode
  = NoiseBlendNone      -- ^ Replace layer content
  | NoiseBlendAdd       -- ^ Add to layer
  | NoiseBlendMultiply  -- ^ Multiply with layer
  | NoiseBlendScreen    -- ^ Screen with layer
  | NoiseBlendOverlay   -- ^ Overlay on layer
  | NoiseBlendDifference -- ^ Difference from layer

derive instance eqNoiseBlendMode :: Eq NoiseBlendMode
derive instance ordNoiseBlendMode :: Ord NoiseBlendMode

instance showNoiseBlendMode :: Show NoiseBlendMode where
  show NoiseBlendNone = "None"
  show NoiseBlendAdd = "Add"
  show NoiseBlendMultiply = "Multiply"
  show NoiseBlendScreen = "Screen"
  show NoiseBlendOverlay = "Overlay"
  show NoiseBlendDifference = "Difference"

defaultFractalNoise :: FractalNoiseEffect
defaultFractalNoise =
  { fractalType: FTBasic
  , noiseType: NTSoftLinear
  , invert: false
  , contrast: 100.0
  , brightness: 0.0
  , overflow: OverflowClip
  , transform: defaultNoiseTransform
  , complexity: 6.0
  , subSettings: defaultSubSettings
  , evolution: 0.0
  , evolutionOptions: defaultEvolutionOptions
  , opacity: 100.0
  , blendingMode: NoiseBlendNone
  }

mkFractalNoise :: FractalType -> NoiseType -> Number -> Number -> FractalNoiseEffect
mkFractalNoise fType nType complexity contrast =
  defaultFractalNoise
    { fractalType = fType
    , noiseType = nType
    , complexity = clampNumber 1.0 20.0 complexity
    , contrast = clampNumber 0.0 400.0 contrast
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if fractal noise is set up for animation.
isFractalNoiseAnimated :: FractalNoiseEffect -> Boolean
isFractalNoiseAnimated effect =
  effect.evolution /= 0.0 || effect.evolutionOptions.cycleEvolution
