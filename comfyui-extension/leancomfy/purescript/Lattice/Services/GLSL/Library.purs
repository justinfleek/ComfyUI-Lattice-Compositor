-- | Lattice.Services.GLSL.Library - GLSL shader library
-- |
-- | Built-in GLSL functions and shader templates.
-- | Pure data - GLSL source code as strings.
-- |
-- | Source: ui/src/services/glsl/GLSLEngine.ts (library section)

module Lattice.Services.GLSL.Library
  ( -- * Shader Templates
    defaultVertexShader
  , shaderHeader
  , shaderFooter
    -- * Library Functions
  , glslLibrary
    -- * Category-specific
  , mathUtilities
  , noiseFunctions
  , colorSpaceConversions
  , textureSampling
  , blurFunctions
  , distortionFunctions
  , shapeFunctions
  , gradientFunctions
  ) where

import Prelude

--------------------------------------------------------------------------------
-- Shader Templates
--------------------------------------------------------------------------------

-- | Default vertex shader
defaultVertexShader :: String
defaultVertexShader = """
attribute vec2 a_position;
attribute vec2 a_texCoord;
varying vec2 v_texCoord;
varying vec2 fragCoord;
uniform vec3 iResolution;

void main() {
  gl_Position = vec4(a_position, 0.0, 1.0);
  v_texCoord = a_texCoord;
  fragCoord = a_texCoord * iResolution.xy;
}
"""

-- | Fragment shader header with Shadertoy-compatible uniforms
shaderHeader :: String
shaderHeader = """
precision highp float;

// Shadertoy-compatible uniforms
uniform vec3 iResolution;      // viewport resolution (pixels)
uniform float iTime;           // shader playback time (seconds)
uniform float iTimeDelta;      // render time (seconds)
uniform int iFrame;            // frame number
uniform vec4 iMouse;           // mouse pixel coords
uniform vec4 iDate;            // year, month, day, time in seconds
uniform float iSampleRate;     // sound sample rate
uniform sampler2D iChannel0;   // input texture

// Texture coordinate from vertex shader
varying vec2 v_texCoord;
varying vec2 fragCoord;
"""

-- | Fragment shader footer
shaderFooter :: String
shaderFooter = """
void main() {
  vec4 fragColor;
  mainImage(fragColor, fragCoord);
  gl_FragColor = fragColor;
}
"""

--------------------------------------------------------------------------------
-- Complete GLSL Library
--------------------------------------------------------------------------------

-- | Complete GLSL utility library
glslLibrary :: String
glslLibrary = mathUtilities
  <> noiseFunctions
  <> colorSpaceConversions
  <> textureSampling
  <> blurFunctions
  <> distortionFunctions
  <> shapeFunctions
  <> gradientFunctions

--------------------------------------------------------------------------------
-- Math Utilities
--------------------------------------------------------------------------------

mathUtilities :: String
mathUtilities = """
// Math constants and utilities
#define PI 3.14159265359
#define TAU 6.28318530718
#define E 2.71828182846

float map(float value, float min1, float max1, float min2, float max2) {
  return min2 + (value - min1) * (max2 - min2) / (max1 - min1);
}

float saturate(float x) {
  return clamp(x, 0.0, 1.0);
}

vec3 saturate3(vec3 x) {
  return clamp(x, 0.0, 1.0);
}
"""

--------------------------------------------------------------------------------
-- Noise Functions
--------------------------------------------------------------------------------

noiseFunctions :: String
noiseFunctions = """
// Noise functions
float hash(float n) {
  return fract(sin(n) * 43758.5453123);
}

float hash2(vec2 p) {
  return fract(sin(dot(p, vec2(12.9898, 78.233))) * 43758.5453);
}

vec2 hash22(vec2 p) {
  p = vec2(dot(p, vec2(127.1, 311.7)), dot(p, vec2(269.5, 183.3)));
  return -1.0 + 2.0 * fract(sin(p) * 43758.5453123);
}

float noise(vec2 p) {
  vec2 i = floor(p);
  vec2 f = fract(p);
  f = f * f * (3.0 - 2.0 * f);
  float a = hash2(i);
  float b = hash2(i + vec2(1.0, 0.0));
  float c = hash2(i + vec2(0.0, 1.0));
  float d = hash2(i + vec2(1.0, 1.0));
  return mix(mix(a, b, f.x), mix(c, d, f.x), f.y);
}

// Simplex noise helpers
vec3 mod289(vec3 x) { return x - floor(x * (1.0 / 289.0)) * 289.0; }
vec2 mod289_2(vec2 x) { return x - floor(x * (1.0 / 289.0)) * 289.0; }
vec3 permute(vec3 x) { return mod289(((x * 34.0) + 1.0) * x); }

float snoise(vec2 v) {
  const vec4 C = vec4(0.211324865405187, 0.366025403784439, -0.577350269189626, 0.024390243902439);
  vec2 i = floor(v + dot(v, C.yy));
  vec2 x0 = v - i + dot(i, C.xx);
  vec2 i1 = (x0.x > x0.y) ? vec2(1.0, 0.0) : vec2(0.0, 1.0);
  vec4 x12 = x0.xyxy + C.xxzz;
  x12.xy -= i1;
  i = mod289_2(i);
  vec3 p = permute(permute(i.y + vec3(0.0, i1.y, 1.0)) + i.x + vec3(0.0, i1.x, 1.0));
  vec3 m = max(0.5 - vec3(dot(x0, x0), dot(x12.xy, x12.xy), dot(x12.zw, x12.zw)), 0.0);
  m = m * m;
  m = m * m;
  vec3 x = 2.0 * fract(p * C.www) - 1.0;
  vec3 h = abs(x) - 0.5;
  vec3 ox = floor(x + 0.5);
  vec3 a0 = x - ox;
  m *= 1.79284291400159 - 0.85373472095314 * (a0 * a0 + h * h);
  vec3 g;
  g.x = a0.x * x0.x + h.x * x0.y;
  g.yz = a0.yz * x12.xz + h.yz * x12.yw;
  return 130.0 * dot(m, g);
}

float fbm(vec2 p, int octaves) {
  float value = 0.0;
  float amplitude = 0.5;
  float frequency = 1.0;
  for (int i = 0; i < 8; i++) {
    if (i >= octaves) break;
    value += amplitude * snoise(p * frequency);
    frequency *= 2.0;
    amplitude *= 0.5;
  }
  return value;
}
"""

--------------------------------------------------------------------------------
-- Color Space Conversions
--------------------------------------------------------------------------------

colorSpaceConversions :: String
colorSpaceConversions = """
// RGB to HSV
vec3 rgb2hsv(vec3 c) {
  vec4 K = vec4(0.0, -1.0 / 3.0, 2.0 / 3.0, -1.0);
  vec4 p = mix(vec4(c.bg, K.wz), vec4(c.gb, K.xy), step(c.b, c.g));
  vec4 q = mix(vec4(p.xyw, c.r), vec4(c.r, p.yzx), step(p.x, c.r));
  float d = q.x - min(q.w, q.y);
  float e = 1.0e-10;
  return vec3(abs(q.z + (q.w - q.y) / (6.0 * d + e)), d / (q.x + e), q.x);
}

// HSV to RGB
vec3 hsv2rgb(vec3 c) {
  vec4 K = vec4(1.0, 2.0 / 3.0, 1.0 / 3.0, 3.0);
  vec3 p = abs(fract(c.xxx + K.xyz) * 6.0 - K.www);
  return c.z * mix(K.xxx, clamp(p - K.xxx, 0.0, 1.0), c.y);
}

// Luminance calculation
float luminance(vec3 c) {
  return dot(c, vec3(0.299, 0.587, 0.114));
}
"""

--------------------------------------------------------------------------------
-- Texture Sampling
--------------------------------------------------------------------------------

textureSampling :: String
textureSampling = """
// Texture sampling with edge modes
vec4 sampleClamp(sampler2D tex, vec2 uv) {
  return texture2D(tex, clamp(uv, 0.0, 1.0));
}

vec4 sampleWrap(sampler2D tex, vec2 uv) {
  return texture2D(tex, fract(uv));
}

vec4 sampleMirror(sampler2D tex, vec2 uv) {
  vec2 m = mod(uv, 2.0);
  m = mix(m, 2.0 - m, step(1.0, m));
  return texture2D(tex, m);
}
"""

--------------------------------------------------------------------------------
-- Blur Functions
--------------------------------------------------------------------------------

blurFunctions :: String
blurFunctions = """
// Gaussian blur
vec4 blur(sampler2D tex, vec2 uv, vec2 resolution, float radius) {
  vec4 color = vec4(0.0);
  float total = 0.0;
  vec2 texelSize = 1.0 / resolution;
  for (float x = -4.0; x <= 4.0; x += 1.0) {
    for (float y = -4.0; y <= 4.0; y += 1.0) {
      float weight = exp(-(x*x + y*y) / (2.0 * radius * radius));
      color += texture2D(tex, uv + vec2(x, y) * texelSize * radius) * weight;
      total += weight;
    }
  }
  return color / total;
}

vec4 directionalBlur(sampler2D tex, vec2 uv, vec2 direction, float strength) {
  vec4 color = vec4(0.0);
  for (float i = -4.0; i <= 4.0; i += 1.0) {
    float weight = exp(-abs(i) * 0.5);
    color += texture2D(tex, uv + direction * i * strength) * weight;
  }
  return color / 9.0;
}
"""

--------------------------------------------------------------------------------
-- Distortion Functions
--------------------------------------------------------------------------------

distortionFunctions :: String
distortionFunctions = """
// Barrel distortion
vec2 barrel(vec2 uv, float amount) {
  vec2 cc = uv - 0.5;
  float dist = dot(cc, cc);
  return uv + cc * dist * amount;
}

vec2 pincushion(vec2 uv, float amount) {
  return barrel(uv, -amount);
}

vec2 swirl(vec2 uv, vec2 center, float angle, float radius) {
  vec2 tc = uv - center;
  float dist = length(tc);
  float percent = (radius - dist) / radius;
  if (percent > 0.0) {
    float theta = percent * percent * angle;
    float s = sin(theta);
    float c = cos(theta);
    tc = vec2(tc.x * c - tc.y * s, tc.x * s + tc.y * c);
  }
  return center + tc;
}
"""

--------------------------------------------------------------------------------
-- Shape Functions
--------------------------------------------------------------------------------

shapeFunctions :: String
shapeFunctions = """
// Shape SDFs
float circle(vec2 uv, vec2 center, float radius) {
  return smoothstep(radius, radius - 0.01, length(uv - center));
}

float rectangle(vec2 uv, vec2 center, vec2 size) {
  vec2 d = abs(uv - center) - size;
  return 1.0 - smoothstep(0.0, 0.01, max(d.x, d.y));
}

float roundedRect(vec2 uv, vec2 center, vec2 size, float radius) {
  vec2 d = abs(uv - center) - size + radius;
  return 1.0 - smoothstep(0.0, 0.01, min(max(d.x, d.y), 0.0) + length(max(d, 0.0)) - radius);
}

float line(vec2 uv, vec2 a, vec2 b, float thickness) {
  vec2 pa = uv - a, ba = b - a;
  float h = clamp(dot(pa, ba) / dot(ba, ba), 0.0, 1.0);
  return smoothstep(thickness, thickness - 0.01, length(pa - ba * h));
}
"""

--------------------------------------------------------------------------------
-- Gradient Functions
--------------------------------------------------------------------------------

gradientFunctions :: String
gradientFunctions = """
// Gradient functions
vec3 linearGradient(vec2 uv, vec2 start, vec2 end, vec3 colorA, vec3 colorB) {
  vec2 dir = normalize(end - start);
  float t = dot(uv - start, dir) / length(end - start);
  return mix(colorA, colorB, clamp(t, 0.0, 1.0));
}

vec3 radialGradient(vec2 uv, vec2 center, float radius, vec3 colorA, vec3 colorB) {
  float t = length(uv - center) / radius;
  return mix(colorA, colorB, clamp(t, 0.0, 1.0));
}

vec3 angularGradient(vec2 uv, vec2 center, vec3 colorA, vec3 colorB) {
  float angle = atan(uv.y - center.y, uv.x - center.x);
  float t = (angle + PI) / TAU;
  return mix(colorA, colorB, t);
}
"""
