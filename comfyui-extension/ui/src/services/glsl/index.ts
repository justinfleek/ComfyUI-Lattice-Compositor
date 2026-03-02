/**
 * GLSL Shader System - Index
 *
 * GPU-accelerated shader effects for Lattice Compositor.
 * Inspired by Jovi_GLSL with Shadertoy-compatible uniforms.
 */

export {
  disposeGLSLEngine,
  type EdgeMode,
  GLSL_LIBRARY,
  GLSLEngine,
  type GLSLEngineOptions,
  getGLSLEngine,
  type ShaderCompileResult,
  type ShaderUniforms,
} from "./GLSLEngine";

export {
  ALL_SHADER_EFFECTS,
  BLUR_EFFECTS,
  COLOR_EFFECTS,
  DISTORT_EFFECTS,
  disposeShaderEffectProcessor,
  GENERATE_EFFECTS,
  getShaderEffectProcessor,
  type ShaderEffectDefinition,
  ShaderEffectProcessor,
  STYLIZE_EFFECTS,
  TRANSITION_EFFECTS,
} from "./ShaderEffects";
