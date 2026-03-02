-- | Lattice.Services.GLSL.Engine - Shader configuration types
-- |
-- | Pure types representing shader configurations. Actual WebGL rendering
-- | is handled by the Haskell backend or a separate renderer concern.
-- |
-- | This module provides shader configuration that can be sent to the backend
-- | via the Bridge for GPU-accelerated processing.
-- |
-- | Source: ui/src/services/glsl/GLSLEngine.ts (engine section)

module Lattice.Services.GLSL.Engine
  ( -- * Engine Configuration
    GLSLEngineConfig
  , defaultEngineConfig
    -- * Shader Requests
  , ShaderCompileRequest(..)
  , ShaderRenderRequest(..)
    -- * Shader Configuration
  , ShaderConfig
  , mkShaderConfig
    -- * Re-exports
  , module Lattice.Services.GLSL.Types
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.String (length, take) as String
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

import Lattice.Services.GLSL.Types
  ( ShaderUniforms
  , ShaderCompileResult
  , GLSLEngineOptions
  , defaultOptions
  )
import Lattice.Services.GLSL.Library (glslLibrary, shaderHeader, shaderFooter)

-- | Engine configuration - pure representation of GLSL engine settings
-- |
-- | This replaces the opaque GLSLEngine handle. Instead of managing
-- | WebGL context directly, we configure shader processing that will
-- | be executed by the backend.
type GLSLEngineConfig =
  { options :: GLSLEngineOptions
  , includeLibrary :: Boolean
  , header :: String
  , footer :: String
  , library :: String
  }

-- | Default engine configuration
defaultEngineConfig :: GLSLEngineConfig
defaultEngineConfig =
  { options: defaultOptions
  , includeLibrary: true
  , header: shaderHeader
  , footer: shaderFooter
  , library: glslLibrary
  }

-- | Request to compile a shader
-- |
-- | Send this to the backend via Bridge to compile shader code.
-- | The backend will return a ShaderCompileResult.
data ShaderCompileRequest = ShaderCompileRequest
  { fragmentSource :: String
  , includeLibrary :: Boolean
  , header :: String
  , footer :: String
  , library :: String
  }

derive instance Eq ShaderCompileRequest
derive instance Generic ShaderCompileRequest _

instance Show ShaderCompileRequest where
  show (ShaderCompileRequest r) =
    let preview = if String.length r.fragmentSource <= 50
                  then r.fragmentSource
                  else String.take 50 r.fragmentSource <> "..."
    in "ShaderCompileRequest { fragmentSource: " <> show preview <> " }"

-- | Request to render a frame using a shader
-- |
-- | Send this to the backend via Bridge to render.
-- | The backend will perform the GPU rendering and return the result.
data ShaderRenderRequest = ShaderRenderRequest
  { shaderSource :: String
  , uniforms :: ShaderUniforms
  , inputCanvasData :: Maybe String  -- Base64-encoded input image
  , width :: Int
  , height :: Int
  }

derive instance Eq ShaderRenderRequest
derive instance Generic ShaderRenderRequest _

instance Show ShaderRenderRequest where
  show (ShaderRenderRequest r) =
    "ShaderRenderRequest { width: " <> show r.width <> ", height: " <> show r.height <> " }"

-- | Shader configuration - complete configuration for a shader
-- |
-- | This is a pure data structure that fully describes a shader setup.
type ShaderConfig =
  { source :: String
  , header :: String
  , footer :: String
  , library :: String
  , includeLibrary :: Boolean
  , uniforms :: ShaderUniforms
  }

-- | Create a shader config with default header/footer/library
mkShaderConfig :: String -> Boolean -> ShaderUniforms -> ShaderConfig
mkShaderConfig source includeLib uniforms =
  { source
  , header: shaderHeader
  , footer: shaderFooter
  , library: glslLibrary
  , includeLibrary: includeLib
  , uniforms
  }
