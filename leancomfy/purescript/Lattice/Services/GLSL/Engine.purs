-- | Lattice.Services.GLSL.Engine - WebGL shader engine
-- |
-- | GPU-accelerated image processing using WebGL shaders.
-- | Shadertoy-compatible uniform system for easy shader authoring.
-- |
-- | Acknowledgement: Inspired by Jovi/Amorano's Jovi_GLSL
-- |
-- | Source: ui/src/services/glsl/GLSLEngine.ts (engine section)

module Lattice.Services.GLSL.Engine
  ( -- * Engine
    GLSLEngine
  , createEngine
  , disposeEngine
  , getEngine
    -- * Availability
  , isWebGLAvailable
  , isContextLost
    -- * Shader Management
  , compileShader
  , setShader
    -- * Rendering
  , render
  , CanvasElement
  , renderWithUniforms
    -- * Uniforms
  , setUniforms
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Maybe (Maybe(..))

import Lattice.Services.GLSL.Types
  ( ShaderUniforms
  , ShaderCompileResult
  , GLSLEngineOptions
  , defaultOptions
  )
import Lattice.Services.GLSL.Library (glslLibrary, shaderHeader, shaderFooter)

--------------------------------------------------------------------------------
-- FFI Types
--------------------------------------------------------------------------------

-- | Opaque WebGL engine handle
foreign import data GLSLEngine :: Type

-- | Opaque canvas handle
foreign import data CanvasElement :: Type

--------------------------------------------------------------------------------
-- FFI Imports
--------------------------------------------------------------------------------

-- | Check if WebGL is available
foreign import isWebGLAvailableImpl :: Effect Boolean

-- | Create a new GLSL engine
foreign import createEngineImpl :: GLSLEngineOptions -> Effect GLSLEngine

-- | Dispose of engine resources
foreign import disposeEngineImpl :: GLSLEngine -> Effect Unit

-- | Check if context is lost
foreign import isContextLostImpl :: GLSLEngine -> Effect Boolean

-- | Compile a shader
foreign import compileShaderImpl
  :: GLSLEngine
  -> String    -- fragment source
  -> String    -- header
  -> String    -- footer
  -> String    -- library
  -> Boolean   -- include library
  -> Effect ShaderCompileResult

-- | Set shader (compile if changed)
foreign import setShaderImpl
  :: GLSLEngine
  -> String    -- fragment source
  -> String    -- header
  -> String    -- footer
  -> String    -- library
  -> Boolean   -- include library
  -> Effect ShaderCompileResult

-- | Set uniforms
foreign import setUniformsImpl
  :: GLSLEngine
  -> ShaderUniforms
  -> Effect Unit

-- | Render with current shader
foreign import renderImpl
  :: GLSLEngine
  -> String    -- input canvas ID
  -> Int       -- width
  -> Int       -- height
  -> EffectFnAff CanvasElement

-- | Render with uniforms
foreign import renderWithUniformsImpl
  :: GLSLEngine
  -> String    -- input canvas ID
  -> Int       -- width
  -> Int       -- height
  -> ShaderUniforms
  -> EffectFnAff CanvasElement

-- | Get singleton instance
foreign import getEngineImpl :: Effect GLSLEngine

--------------------------------------------------------------------------------
-- Public API
--------------------------------------------------------------------------------

-- | Check if WebGL is available in the browser
isWebGLAvailable :: Effect Boolean
isWebGLAvailable = isWebGLAvailableImpl

-- | Create a new GLSL engine with options
createEngine :: GLSLEngineOptions -> Effect GLSLEngine
createEngine = createEngineImpl

-- | Dispose of engine resources
disposeEngine :: GLSLEngine -> Effect Unit
disposeEngine = disposeEngineImpl

-- | Get the singleton GLSL engine instance
getEngine :: Effect GLSLEngine
getEngine = getEngineImpl

-- | Check if WebGL context is lost
isContextLost :: GLSLEngine -> Effect Boolean
isContextLost = isContextLostImpl

-- | Compile a shader from fragment source
-- | Returns compilation result with error info if failed
compileShader :: GLSLEngine -> String -> Boolean -> Effect ShaderCompileResult
compileShader engine fragmentSource includeLibrary =
  compileShaderImpl engine fragmentSource shaderHeader shaderFooter glslLibrary includeLibrary

-- | Set the shader to use (compiles only if source changed)
setShader :: GLSLEngine -> String -> Boolean -> Effect ShaderCompileResult
setShader engine fragmentSource includeLibrary =
  setShaderImpl engine fragmentSource shaderHeader shaderFooter glslLibrary includeLibrary

-- | Set uniforms on the current shader
setUniforms :: GLSLEngine -> ShaderUniforms -> Effect Unit
setUniforms = setUniformsImpl

-- | Render using the current shader
-- | Input is canvas element ID, returns output canvas
render :: GLSLEngine -> String -> Int -> Int -> Aff CanvasElement
render engine inputCanvasId width height =
  fromEffectFnAff (renderImpl engine inputCanvasId width height)

-- | Render with specified uniforms
renderWithUniforms :: GLSLEngine -> String -> Int -> Int -> ShaderUniforms -> Aff CanvasElement
renderWithUniforms engine inputCanvasId width height uniforms =
  fromEffectFnAff (renderWithUniformsImpl engine inputCanvasId width height uniforms)
