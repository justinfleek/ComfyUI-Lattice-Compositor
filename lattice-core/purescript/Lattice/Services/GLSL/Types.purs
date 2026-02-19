-- | Lattice.Services.GLSL.Types - GLSL shader engine types
-- |
-- | Pure types for WebGL shader processing.
-- | Shadertoy-compatible uniforms for easy shader authoring.
-- |
-- | Source: ui/src/services/glsl/GLSLEngine.ts (types section)

module Lattice.Services.GLSL.Types
  ( -- * Uniform Types
    ShaderUniforms
  , Vec2
  , Vec3
  , Vec4
    -- * Result Types
  , ShaderCompileResult
    -- * Configuration
  , EdgeMode(..)
  , GLSLEngineOptions
    -- * Defaults
  , defaultUniforms
  , defaultOptions
    -- * Conversion
  , edgeModeToString
  , stringToEdgeMode
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Vector Types
--------------------------------------------------------------------------------

-- | 2D vector
type Vec2 = { x :: Number, y :: Number }

-- | 3D vector (also used for resolution: width, height, pixelAspectRatio)
type Vec3 = { x :: Number, y :: Number, z :: Number }

-- | 4D vector (used for mouse: xy = position, zw = click position)
type Vec4 = { x :: Number, y :: Number, z :: Number, w :: Number }

--------------------------------------------------------------------------------
-- Uniform Types
--------------------------------------------------------------------------------

-- | Shadertoy-compatible shader uniforms
type ShaderUniforms =
  { iResolution :: Vec3        -- width, height, pixelAspectRatio
  , iTime :: Number            -- Shader playback time (seconds)
  , iTimeDelta :: Number       -- Time since last frame
  , iFrame :: Int              -- Frame number
  , iMouse :: Vec4             -- xy = position, zw = click position
  , iDate :: Vec4              -- year, month, day, seconds
  , iSampleRate :: Number      -- Audio sample rate (44100)
  }

--------------------------------------------------------------------------------
-- Result Types
--------------------------------------------------------------------------------

-- | Shader compilation result
type ShaderCompileResult =
  { success :: Boolean
  , error :: Maybe String
  , errorLine :: Maybe Int
  }

--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------

-- | Edge handling mode for texture sampling
data EdgeMode
  = EdgeClamp    -- Clamp to edge
  | EdgeWrap     -- Repeat/tile
  | EdgeMirror   -- Mirror repeat

derive instance Eq EdgeMode
derive instance Ord EdgeMode
derive instance Generic EdgeMode _
instance Show EdgeMode where show = genericShow

-- | GLSL engine options
type GLSLEngineOptions =
  { preserveDrawingBuffer :: Boolean
  , alpha :: Boolean
  , premultipliedAlpha :: Boolean
  }

--------------------------------------------------------------------------------
-- Defaults
--------------------------------------------------------------------------------

-- | Default shader uniforms
defaultUniforms :: Int -> Int -> Int -> Number -> ShaderUniforms
defaultUniforms width height frame time =
  { iResolution: { x: toNum width, y: toNum height, z: 1.0 }
  , iTime: time
  , iTimeDelta: 1.0 / 60.0
  , iFrame: frame
  , iMouse: { x: 0.0, y: 0.0, z: 0.0, w: 0.0 }
  , iDate: { x: 2025.0, y: 1.0, z: 1.0, w: 0.0 }
  , iSampleRate: 44100.0
  }
  where
    toNum :: Int -> Number
    toNum n = toNumber n

foreign import toNumber :: Int -> Number

-- | Default engine options
defaultOptions :: GLSLEngineOptions
defaultOptions =
  { preserveDrawingBuffer: true
  , alpha: true
  , premultipliedAlpha: false
  }

--------------------------------------------------------------------------------
-- Conversion Functions
--------------------------------------------------------------------------------

-- | Convert edge mode to string
edgeModeToString :: EdgeMode -> String
edgeModeToString = case _ of
  EdgeClamp -> "clamp"
  EdgeWrap -> "wrap"
  EdgeMirror -> "mirror"

-- | Parse string to edge mode
stringToEdgeMode :: String -> Maybe EdgeMode
stringToEdgeMode = case _ of
  "clamp" -> Just EdgeClamp
  "wrap" -> Just EdgeWrap
  "mirror" -> Just EdgeMirror
  _ -> Nothing
