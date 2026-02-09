-- | Lattice.Services.Video.Types - Video processing types
-- |
-- | Pure types for video frame interpolation and processing.
-- | No FFI required - just data types and pure functions.
-- |
-- | Source: ui/src/services/video/frameInterpolation.ts (types section)

module Lattice.Services.Video.Types
  ( -- * Model Types
    RIFEModel(..)
  , InterpolationFactor(..)
  , InterpolationModel
    -- * Result Types
  , PairInterpolationResult
  , SequenceInterpolationResult
  , SlowMoResult
  , InterpolatedFrame
    -- * Request Types
  , InterpolationRequest
  , SequenceRequest
  , SlowMoRequest
    -- * Preset Types
  , InterpolationPreset
  , InterpolationPresets
    -- * Helpers
  , rifeModelToString
  , stringToRifeModel
  , factorToInt
  , intToFactor
  , defaultPresets
  , getPreset
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Foreign.Object (Object)
import Foreign.Object as Obj

--------------------------------------------------------------------------------
-- Model Types
--------------------------------------------------------------------------------

-- | RIFE model variants
data RIFEModel
  = RIFE46
  | RIFE47
  | RIFE48
  | RIFEAnime

derive instance Eq RIFEModel
derive instance Ord RIFEModel
derive instance Generic RIFEModel _
instance Show RIFEModel where show = genericShow

-- | Interpolation factor (powers of 2)
data InterpolationFactor
  = Factor2x
  | Factor4x
  | Factor8x
  | Factor16x

derive instance Eq InterpolationFactor
derive instance Ord InterpolationFactor
derive instance Generic InterpolationFactor _
instance Show InterpolationFactor where show = genericShow

-- | Interpolation model info from API
type InterpolationModel =
  { id :: String
  , name :: String
  , description :: String
  , rifeModel :: RIFEModel
  , maxFactor :: InterpolationFactor
  , supportsEnsemble :: Boolean
  , supportsFastMode :: Boolean
  }

--------------------------------------------------------------------------------
-- Result Types
--------------------------------------------------------------------------------

-- | Single interpolated frame
type InterpolatedFrame =
  { frameIndex :: Int        -- Position in sequence
  , timestamp :: Number      -- Time in seconds
  , dataUrl :: String        -- Base64 encoded image
  , confidence :: Number     -- 0-1 quality confidence
  }

-- | Result from interpolating a pair of frames
type PairInterpolationResult =
  { success :: Boolean
  , frames :: Array InterpolatedFrame
  , processingTime :: Number  -- Milliseconds
  , modelUsed :: String
  , error :: Maybe String
  }

-- | Result from interpolating a sequence
type SequenceInterpolationResult =
  { success :: Boolean
  , originalFrameCount :: Int
  , outputFrameCount :: Int
  , frames :: Array InterpolatedFrame
  , totalProcessingTime :: Number
  , averageTimePerPair :: Number
  , error :: Maybe String
  }

-- | Result from slow motion processing
type SlowMoResult =
  { success :: Boolean
  , slowdownFactor :: Number
  , originalFps :: Number
  , outputFps :: Number
  , frames :: Array InterpolatedFrame
  , totalProcessingTime :: Number
  , error :: Maybe String
  }

--------------------------------------------------------------------------------
-- Request Types
--------------------------------------------------------------------------------

-- | Request for pair interpolation
type InterpolationRequest =
  { frame1 :: String         -- Base64 encoded
  , frame2 :: String         -- Base64 encoded
  , factor :: InterpolationFactor
  , model :: RIFEModel
  , ensemble :: Boolean      -- Use ensemble mode
  , fastMode :: Boolean      -- Use fast mode
  }

-- | Request for sequence interpolation
type SequenceRequest =
  { frames :: Array String   -- Base64 encoded frames
  , factor :: InterpolationFactor
  , model :: RIFEModel
  , ensemble :: Boolean
  , fastMode :: Boolean
  , preserveOriginal :: Boolean  -- Keep original frames in output
  }

-- | Request for slow motion
type SlowMoRequest =
  { frames :: Array String
  , slowdownFactor :: Number  -- 2.0 = half speed, 4.0 = quarter speed
  , targetFps :: Number       -- Output FPS
  , sourceFps :: Number       -- Original FPS
  , model :: RIFEModel
  , ensemble :: Boolean
  , fastMode :: Boolean
  }

--------------------------------------------------------------------------------
-- Preset Types
--------------------------------------------------------------------------------

-- | Interpolation preset configuration
type InterpolationPreset =
  { name :: String
  , description :: String
  , model :: RIFEModel
  , factor :: InterpolationFactor
  , ensemble :: Boolean
  , fastMode :: Boolean
  }

-- | Collection of presets
type InterpolationPresets = Object InterpolationPreset

--------------------------------------------------------------------------------
-- Conversion Functions
--------------------------------------------------------------------------------

-- | Convert RIFE model to API string
rifeModelToString :: RIFEModel -> String
rifeModelToString = case _ of
  RIFE46 -> "rife-v4.6"
  RIFE47 -> "rife-v4.7"
  RIFE48 -> "rife-v4.8"
  RIFEAnime -> "rife-anime"

-- | Parse API string to RIFE model
stringToRifeModel :: String -> Maybe RIFEModel
stringToRifeModel = case _ of
  "rife-v4.6" -> Just RIFE46
  "rife-v4.7" -> Just RIFE47
  "rife-v4.8" -> Just RIFE48
  "rife-anime" -> Just RIFEAnime
  _ -> Nothing

-- | Convert factor to integer multiplier
factorToInt :: InterpolationFactor -> Int
factorToInt = case _ of
  Factor2x -> 2
  Factor4x -> 4
  Factor8x -> 8
  Factor16x -> 16

-- | Parse integer to factor
intToFactor :: Int -> Maybe InterpolationFactor
intToFactor = case _ of
  2 -> Just Factor2x
  4 -> Just Factor4x
  8 -> Just Factor8x
  16 -> Just Factor16x
  _ -> Nothing

--------------------------------------------------------------------------------
-- Default Presets
--------------------------------------------------------------------------------

-- | Default interpolation presets
defaultPresets :: InterpolationPresets
defaultPresets = Obj.fromFoldable
  [ Tuple "fast" fastPreset
  , Tuple "balanced" balancedPreset
  , Tuple "quality" qualityPreset
  , Tuple "anime" animePreset
  , Tuple "slowmo-2x" slowmo2xPreset
  , Tuple "slowmo-4x" slowmo4xPreset
  ]

fastPreset :: InterpolationPreset
fastPreset =
  { name: "Fast"
  , description: "Quick interpolation with minimal quality loss"
  , model: RIFE47
  , factor: Factor2x
  , ensemble: false
  , fastMode: true
  }

balancedPreset :: InterpolationPreset
balancedPreset =
  { name: "Balanced"
  , description: "Good balance of speed and quality"
  , model: RIFE47
  , factor: Factor2x
  , ensemble: false
  , fastMode: false
  }

qualityPreset :: InterpolationPreset
qualityPreset =
  { name: "High Quality"
  , description: "Best quality with ensemble mode"
  , model: RIFE48
  , factor: Factor2x
  , ensemble: true
  , fastMode: false
  }

animePreset :: InterpolationPreset
animePreset =
  { name: "Anime"
  , description: "Optimized for animation and cartoon content"
  , model: RIFEAnime
  , factor: Factor2x
  , ensemble: false
  , fastMode: false
  }

slowmo2xPreset :: InterpolationPreset
slowmo2xPreset =
  { name: "Slow Motion 2x"
  , description: "Double frame count for 2x slowdown"
  , model: RIFE47
  , factor: Factor2x
  , ensemble: false
  , fastMode: false
  }

slowmo4xPreset :: InterpolationPreset
slowmo4xPreset =
  { name: "Slow Motion 4x"
  , description: "Quadruple frame count for 4x slowdown"
  , model: RIFE47
  , factor: Factor4x
  , ensemble: true
  , fastMode: false
  }

-- | Get preset by name
getPreset :: String -> Maybe InterpolationPreset
getPreset name = Obj.lookup name defaultPresets
