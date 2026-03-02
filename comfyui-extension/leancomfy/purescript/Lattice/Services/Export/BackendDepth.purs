-- | Lattice.Services.Export.BackendDepth - Backend depth/normal service
-- |
-- | Calls the Python backend endpoints (/lattice/depth, /lattice/normal) for
-- | real AI-powered depth estimation using DepthAnything V3 and normal map
-- | generation using algebraic or NormalCrafter methods.
-- |
-- | Source: ui/src/services/export/backendDepthService.ts

module Lattice.Services.Export.BackendDepth
  ( -- * Types
    DepthModel(..)
  , NormalMethod(..)
  , DepthGenerationOptions
  , DepthGenerationResult
  , NormalGenerationOptions
  , NormalGenerationResult
  , DepthMetadata
  , NormalMetadata
  , AvailabilityResult
    -- * Service Handle
  , BackendDepthService
  , createService
  , getDefaultService
    -- * Generation Functions
  , generateDepth
  , generateNormal
  , generateDepthAndNormal
  , checkAvailability
    -- * Utility Functions
  , canvasToBase64
  , CanvasHandle
  , BlobHandle
  , base64ToBlob
  , base64ToDataUrl
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Depth estimation model options
data DepthModel
  = DA3Large         -- DA3-LARGE-1.1
  | DA3Giant         -- DA3-GIANT-1.1
  | DA3NestedGiant   -- DA3NESTED-GIANT-LARGE-1.1

derive instance Generic DepthModel _
instance Show DepthModel where show = genericShow
instance Eq DepthModel where eq = genericEq

-- | Normal map generation method
data NormalMethod
  = MethodAlgebraic    -- Algebraic normal computation from depth
  | MethodNormalCrafter -- NormalCrafter AI method

derive instance Generic NormalMethod _
instance Show NormalMethod where show = genericShow
instance Eq NormalMethod where eq = genericEq

-- | Depth generation options
type DepthGenerationOptions =
  { model :: DepthModel
  , returnConfidence :: Boolean
  , returnIntrinsics :: Boolean
  }

-- | Depth metadata
type DepthMetadata =
  { model :: String
  , width :: Int
  , height :: Int
  , depthMin :: Maybe Number
  , depthMax :: Maybe Number
  }

-- | Depth generation result
type DepthGenerationResult =
  { status :: String              -- "success" | "error"
  , depth :: String               -- base64 encoded PNG (grayscale)
  , confidence :: Maybe String    -- base64 encoded PNG (optional)
  , intrinsics :: Maybe (Array (Array Number))  -- Camera intrinsics matrix
  , fallback :: Boolean
  , message :: Maybe String
  , metadata :: Maybe DepthMetadata
  }

-- | Normal generation options
type NormalGenerationOptions =
  { method :: NormalMethod
  , depthModel :: DepthModel
  }

-- | Normal metadata
type NormalMetadata =
  { method :: String
  , width :: Int
  , height :: Int
  }

-- | Normal generation result
type NormalGenerationResult =
  { status :: String              -- "success" | "error"
  , normal :: String              -- base64 encoded PNG (RGB normal map)
  , depth :: Maybe String         -- base64 depth map used (if generated)
  , fallback :: Boolean
  , message :: Maybe String
  , metadata :: Maybe NormalMetadata
  }

-- | Availability check result
type AvailabilityResult =
  { depthAvailable :: Boolean
  , normalAvailable :: Boolean
  , fallbackOnly :: Boolean
  }

--------------------------------------------------------------------------------
-- FFI Types
--------------------------------------------------------------------------------

-- | Opaque service handle
foreign import data BackendDepthService :: Type

-- | Opaque canvas handle
foreign import data CanvasHandle :: Type

-- | Opaque blob handle
foreign import data BlobHandle :: Type

--------------------------------------------------------------------------------
-- Service Management
--------------------------------------------------------------------------------

-- | Create a new backend depth service
foreign import createServiceImpl :: Maybe String -> Effect BackendDepthService

createService :: Maybe String -> Effect BackendDepthService
createService = createServiceImpl

-- | Get the default service instance
foreign import getDefaultService :: Effect BackendDepthService

--------------------------------------------------------------------------------
-- Generation Functions
--------------------------------------------------------------------------------

-- | Generate depth map from image
foreign import generateDepthImpl
  :: BackendDepthService
  -> String              -- imageBase64
  -> DepthGenerationOptions
  -> EffectFnAff DepthGenerationResult

generateDepth
  :: BackendDepthService
  -> String
  -> DepthGenerationOptions
  -> Aff DepthGenerationResult
generateDepth service imageBase64 options =
  fromEffectFnAff (generateDepthImpl service imageBase64 options)

-- | Generate normal map from image or depth
foreign import generateNormalImpl
  :: BackendDepthService
  -> Maybe String        -- imageBase64
  -> Maybe String        -- depthBase64
  -> NormalGenerationOptions
  -> EffectFnAff NormalGenerationResult

generateNormal
  :: BackendDepthService
  -> Maybe String
  -> Maybe String
  -> NormalGenerationOptions
  -> Aff NormalGenerationResult
generateNormal service imageBase64 depthBase64 options =
  fromEffectFnAff (generateNormalImpl service imageBase64 depthBase64 options)

-- | Generate both depth and normal maps
foreign import generateDepthAndNormalImpl
  :: BackendDepthService
  -> String              -- imageBase64
  -> DepthGenerationOptions
  -> NormalGenerationOptions
  -> EffectFnAff { depth :: DepthGenerationResult, normal :: NormalGenerationResult }

generateDepthAndNormal
  :: BackendDepthService
  -> String
  -> DepthGenerationOptions
  -> NormalGenerationOptions
  -> Aff { depth :: DepthGenerationResult, normal :: NormalGenerationResult }
generateDepthAndNormal service imageBase64 depthOpts normalOpts =
  fromEffectFnAff (generateDepthAndNormalImpl service imageBase64 depthOpts normalOpts)

-- | Check if backend depth services are available
foreign import checkAvailabilityImpl
  :: BackendDepthService
  -> EffectFnAff AvailabilityResult

checkAvailability :: BackendDepthService -> Aff AvailabilityResult
checkAvailability service = fromEffectFnAff (checkAvailabilityImpl service)

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Convert canvas to base64 string (no data URL prefix)
foreign import canvasToBase64 :: CanvasHandle -> Effect String

-- | Convert base64 string to blob
foreign import base64ToBlobImpl :: String -> String -> Effect BlobHandle

base64ToBlob :: String -> String -> Effect BlobHandle
base64ToBlob = base64ToBlobImpl

-- | Convert base64 string to data URL
foreign import base64ToDataUrl :: String -> String -> String

--------------------------------------------------------------------------------
-- Default Options
--------------------------------------------------------------------------------

-- | Default depth generation options
defaultDepthOptions :: DepthGenerationOptions
defaultDepthOptions =
  { model: DA3Large
  , returnConfidence: false
  , returnIntrinsics: false
  }

-- | Default normal generation options
defaultNormalOptions :: NormalGenerationOptions
defaultNormalOptions =
  { method: MethodAlgebraic
  , depthModel: DA3Large
  }
