-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // gpu // webgpu // shader
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- WGSL shaders as pure PureScript strings.
--
-- Shaders are PURE DATA — deterministic, composable, auditable.
-- No runtime shader compilation from external files.
-- Same shader = same GPU behavior (always).
--
-- PROOF REFERENCE:
-- PBR BRDF mathematics: proofs/Hydrogen/Material/BRDF.lean
-- - fresnel_schlick
-- - ggx_distribution  
-- - smith_geometry
-- - cook_torrance
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Shader
  ( -- WGSL Source type
    WGSLSource(..)
    -- Basic (unlit) shaders
  , basicVertexShader
  , basicFragmentShader
    -- PBR shaders
  , pbrVertexShader
  , pbrFragmentShader
    -- Shadow mapping shaders
  , shadowVertexShader
  , shadowFragmentShader
    -- GPU picking shaders
  , pickVertexShader
  , pickFragmentShader
    -- SDF text shaders
  , sdfTextVertexShader
  , sdfTextFragmentShader
    -- Skybox shaders
  , skyboxVertexShader
  , skyboxFragmentShader
    -- Wireframe shaders
  , wireframeVertexShader
  , wireframeFragmentShader
    -- Fullscreen quad (post-processing)
  , fullscreenVertexShader
  , tonemapFragmentShader
    -- Shader utilities
  , combineShaderSource
  , shaderSourceToString
  ) where

import Prelude
  ( class Eq
  , class Semigroup
  , (<>)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- WGSL SOURCE TYPE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WGSL shader source code.
-- | Pure data wrapper for type safety.
newtype WGSLSource = WGSLSource String

derive instance eqWGSLSource :: Eq WGSLSource

instance semigroupWGSLSource :: Semigroup WGSLSource where
  append (WGSLSource a) (WGSLSource b) = WGSLSource (a <> "\n" <> b)

-- | Extract the raw WGSL string.
shaderSourceToString :: WGSLSource -> String
shaderSourceToString (WGSLSource s) = s

-- | Combine multiple shader source fragments.
combineShaderSource :: Array WGSLSource -> WGSLSource
combineShaderSource sources = foldl combineTwoSources emptySource sources
  where
    emptySource :: WGSLSource
    emptySource = WGSLSource ""
    
    combineTwoSources :: WGSLSource -> WGSLSource -> WGSLSource
    combineTwoSources (WGSLSource a) (WGSLSource b) = 
      case a of
        "" -> WGSLSource b
        _ -> WGSLSource (a <> "\n" <> b)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BASIC (UNLIT) SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Basic vertex shader — transforms vertices with model-view-projection.
basicVertexShader :: WGSLSource
basicVertexShader = WGSLSource
  """
struct FrameUniforms {
  viewProjection: mat4x4<f32>,
  cameraPosition: vec3<f32>,
  time: f32,
}

struct ObjectUniforms {
  model: mat4x4<f32>,
  normalMatrix: mat3x3<f32>,
}

@group(0) @binding(0) var<uniform> frame: FrameUniforms;
@group(2) @binding(0) var<uniform> object: ObjectUniforms;

struct VertexInput {
  @location(0) position: vec3<f32>,
  @location(1) normal: vec3<f32>,
  @location(2) uv: vec2<f32>,
}

struct VertexOutput {
  @builtin(position) clipPosition: vec4<f32>,
  @location(0) worldPosition: vec3<f32>,
  @location(1) worldNormal: vec3<f32>,
  @location(2) uv: vec2<f32>,
}

@vertex
fn main(input: VertexInput) -> VertexOutput {
  var output: VertexOutput;
  
  let worldPos = object.model * vec4<f32>(input.position, 1.0);
  output.clipPosition = frame.viewProjection * worldPos;
  output.worldPosition = worldPos.xyz;
  output.worldNormal = object.normalMatrix * input.normal;
  output.uv = input.uv;
  
  return output;
}
"""

-- | Basic fragment shader — flat color, no lighting.
basicFragmentShader :: WGSLSource
basicFragmentShader = WGSLSource
  """
struct MaterialUniforms {
  color: vec4<f32>,
}

@group(1) @binding(0) var<uniform> material: MaterialUniforms;

struct FragmentInput {
  @location(0) worldPosition: vec3<f32>,
  @location(1) worldNormal: vec3<f32>,
  @location(2) uv: vec2<f32>,
}

@fragment
fn main(input: FragmentInput) -> @location(0) vec4<f32> {
  return material.color;
}
"""

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PBR SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PBR vertex shader — same as basic, but passes tangent for normal mapping.
pbrVertexShader :: WGSLSource
pbrVertexShader = WGSLSource
  """
struct FrameUniforms {
  viewProjection: mat4x4<f32>,
  cameraPosition: vec3<f32>,
  time: f32,
}

struct ObjectUniforms {
  model: mat4x4<f32>,
  normalMatrix: mat3x3<f32>,
}

@group(0) @binding(0) var<uniform> frame: FrameUniforms;
@group(2) @binding(0) var<uniform> object: ObjectUniforms;

struct VertexInput {
  @location(0) position: vec3<f32>,
  @location(1) normal: vec3<f32>,
  @location(2) uv: vec2<f32>,
  @location(3) tangent: vec4<f32>,
}

struct VertexOutput {
  @builtin(position) clipPosition: vec4<f32>,
  @location(0) worldPosition: vec3<f32>,
  @location(1) worldNormal: vec3<f32>,
  @location(2) uv: vec2<f32>,
  @location(3) worldTangent: vec3<f32>,
  @location(4) worldBitangent: vec3<f32>,
}

@vertex
fn main(input: VertexInput) -> VertexOutput {
  var output: VertexOutput;
  
  let worldPos = object.model * vec4<f32>(input.position, 1.0);
  output.clipPosition = frame.viewProjection * worldPos;
  output.worldPosition = worldPos.xyz;
  output.worldNormal = normalize(object.normalMatrix * input.normal);
  output.uv = input.uv;
  
  // Tangent space for normal mapping
  output.worldTangent = normalize(object.normalMatrix * input.tangent.xyz);
  output.worldBitangent = cross(output.worldNormal, output.worldTangent) * input.tangent.w;
  
  return output;
}
"""

-- | PBR fragment shader — Cook-Torrance BRDF with metallic-roughness workflow.
-- | 
-- | Implements:
-- | - GGX/Trowbridge-Reitz normal distribution function
-- | - Smith-Schlick geometry function (height-correlated)
-- | - Fresnel-Schlick approximation
-- | - Energy conservation
-- |
-- | PROOF REFERENCE: proofs/Hydrogen/Material/BRDF.lean
pbrFragmentShader :: WGSLSource
pbrFragmentShader = WGSLSource
  """
const PI: f32 = 3.14159265359;

struct FrameUniforms {
  viewProjection: mat4x4<f32>,
  cameraPosition: vec3<f32>,
  time: f32,
}

struct MaterialUniforms {
  baseColor: vec4<f32>,
  emissive: vec3<f32>,
  metallic: f32,
  roughness: f32,
  emissiveIntensity: f32,
  _padding: vec2<f32>,
}

struct Light {
  position: vec3<f32>,
  lightType: u32,
  color: vec3<f32>,
  intensity: f32,
  direction: vec3<f32>,
  range: f32,
  innerConeAngle: f32,
  outerConeAngle: f32,
  _padding: vec2<f32>,
}

struct LightUniforms {
  ambientColor: vec3<f32>,
  numLights: u32,
  lights: array<Light, 16>,
}

@group(0) @binding(0) var<uniform> frame: FrameUniforms;
@group(1) @binding(0) var<uniform> material: MaterialUniforms;
@group(3) @binding(0) var<uniform> lighting: LightUniforms;

struct FragmentInput {
  @location(0) worldPosition: vec3<f32>,
  @location(1) worldNormal: vec3<f32>,
  @location(2) uv: vec2<f32>,
  @location(3) worldTangent: vec3<f32>,
  @location(4) worldBitangent: vec3<f32>,
}

// GGX/Trowbridge-Reitz normal distribution function
// D(h) = α² / (π * ((n·h)² * (α² - 1) + 1)²)
fn distributionGGX(NdotH: f32, roughness: f32) -> f32 {
  let a = roughness * roughness;
  let a2 = a * a;
  let denom = NdotH * NdotH * (a2 - 1.0) + 1.0;
  return a2 / (PI * denom * denom);
}

// Smith-Schlick geometry function (single direction)
// G1(v) = n·v / (n·v * (1 - k) + k)
// where k = α/2 for direct lighting
fn geometrySchlickGGX(NdotV: f32, roughness: f32) -> f32 {
  let r = roughness + 1.0;
  let k = (r * r) / 8.0;
  return NdotV / (NdotV * (1.0 - k) + k);
}

// Smith geometry function (combined)
// G(l, v, h) = G1(l) * G1(v)
fn geometrySmith(NdotV: f32, NdotL: f32, roughness: f32) -> f32 {
  let ggx1 = geometrySchlickGGX(NdotV, roughness);
  let ggx2 = geometrySchlickGGX(NdotL, roughness);
  return ggx1 * ggx2;
}

// Fresnel-Schlick approximation
// F(h, v) = F0 + (1 - F0) * (1 - h·v)⁵
fn fresnelSchlick(cosTheta: f32, F0: vec3<f32>) -> vec3<f32> {
  return F0 + (1.0 - F0) * pow(clamp(1.0 - cosTheta, 0.0, 1.0), 5.0);
}

// Calculate light attenuation based on distance
fn lightAttenuation(distance: f32, range: f32) -> f32 {
  if (range <= 0.0) {
    return 1.0; // Directional light
  }
  let attenuation = clamp(1.0 - pow(distance / range, 4.0), 0.0, 1.0);
  return attenuation * attenuation / (distance * distance + 1.0);
}

// Main PBR calculation
fn calculatePBR(
  N: vec3<f32>,
  V: vec3<f32>,
  L: vec3<f32>,
  baseColor: vec3<f32>,
  metallic: f32,
  roughness: f32,
  lightColor: vec3<f32>,
  lightIntensity: f32,
) -> vec3<f32> {
  let H = normalize(V + L);
  
  let NdotV = max(dot(N, V), 0.001);
  let NdotL = max(dot(N, L), 0.0);
  let NdotH = max(dot(N, H), 0.0);
  let HdotV = max(dot(H, V), 0.0);
  
  // Dialectric F0 = 0.04, metal F0 = baseColor
  let F0 = mix(vec3<f32>(0.04), baseColor, metallic);
  
  // Cook-Torrance BRDF
  let D = distributionGGX(NdotH, roughness);
  let G = geometrySmith(NdotV, NdotL, roughness);
  let F = fresnelSchlick(HdotV, F0);
  
  // Specular contribution
  let numerator = D * G * F;
  let denominator = 4.0 * NdotV * NdotL + 0.0001;
  let specular = numerator / denominator;
  
  // Energy conservation: diffuse + specular must not exceed 1
  let kS = F;
  let kD = (vec3<f32>(1.0) - kS) * (1.0 - metallic);
  
  // Lambertian diffuse
  let diffuse = kD * baseColor / PI;
  
  // Final radiance
  let radiance = lightColor * lightIntensity;
  return (diffuse + specular) * radiance * NdotL;
}

@fragment
fn main(input: FragmentInput) -> @location(0) vec4<f32> {
  let N = normalize(input.worldNormal);
  let V = normalize(frame.cameraPosition - input.worldPosition);
  
  let baseColor = material.baseColor.rgb;
  let metallic = material.metallic;
  let roughness = max(material.roughness, 0.04); // Avoid division by zero
  
  // Start with ambient
  var Lo = lighting.ambientColor * baseColor;
  
  // Accumulate light contributions
  for (var i: u32 = 0u; i < lighting.numLights; i = i + 1u) {
    let light = lighting.lights[i];
    
    var L: vec3<f32>;
    var attenuation: f32 = 1.0;
    
    // Light type: 0 = directional, 1 = point, 2 = spot
    if (light.lightType == 0u) {
      // Directional light
      L = normalize(-light.direction);
    } else {
      // Point or spot light
      let lightVec = light.position - input.worldPosition;
      let distance = length(lightVec);
      L = lightVec / distance;
      attenuation = lightAttenuation(distance, light.range);
      
      // Spot light cone attenuation
      if (light.lightType == 2u) {
        let theta = dot(L, normalize(-light.direction));
        let epsilon = light.innerConeAngle - light.outerConeAngle;
        let spotAttenuation = clamp((theta - light.outerConeAngle) / epsilon, 0.0, 1.0);
        attenuation = attenuation * spotAttenuation;
      }
    }
    
    Lo = Lo + calculatePBR(N, V, L, baseColor, metallic, roughness, light.color, light.intensity * attenuation);
  }
  
  // Add emissive
  Lo = Lo + material.emissive * material.emissiveIntensity;
  
  return vec4<f32>(Lo, material.baseColor.a);
}
"""

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SHADOW MAPPING SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shadow map vertex shader — renders depth from light's perspective.
shadowVertexShader :: WGSLSource
shadowVertexShader = WGSLSource
  """
struct LightViewUniforms {
  lightViewProjection: mat4x4<f32>,
}

struct ObjectUniforms {
  model: mat4x4<f32>,
  normalMatrix: mat3x3<f32>,
}

@group(0) @binding(0) var<uniform> lightView: LightViewUniforms;
@group(2) @binding(0) var<uniform> object: ObjectUniforms;

struct VertexInput {
  @location(0) position: vec3<f32>,
}

struct VertexOutput {
  @builtin(position) position: vec4<f32>,
}

@vertex
fn main(input: VertexInput) -> VertexOutput {
  var output: VertexOutput;
  let worldPos = object.model * vec4<f32>(input.position, 1.0);
  output.position = lightView.lightViewProjection * worldPos;
  return output;
}
"""

-- | Shadow map fragment shader — empty, only depth is written.
shadowFragmentShader :: WGSLSource
shadowFragmentShader = WGSLSource
  """
@fragment
fn main() {
  // Depth is written automatically by the depth attachment
}
"""

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- GPU PICKING SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Picking vertex shader — same as basic transform.
pickVertexShader :: WGSLSource
pickVertexShader = WGSLSource
  """
struct FrameUniforms {
  viewProjection: mat4x4<f32>,
  cameraPosition: vec3<f32>,
  time: f32,
}

struct ObjectUniforms {
  model: mat4x4<f32>,
  normalMatrix: mat3x3<f32>,
}

@group(0) @binding(0) var<uniform> frame: FrameUniforms;
@group(2) @binding(0) var<uniform> object: ObjectUniforms;

struct VertexInput {
  @location(0) position: vec3<f32>,
}

@vertex
fn main(input: VertexInput) -> @builtin(position) vec4<f32> {
  let worldPos = object.model * vec4<f32>(input.position, 1.0);
  return frame.viewProjection * worldPos;
}
"""

-- | Picking fragment shader — outputs object ID as color.
pickFragmentShader :: WGSLSource
pickFragmentShader = WGSLSource
  """
struct PickUniforms {
  objectId: u32,
  _padding: vec3<u32>,
}

@group(1) @binding(0) var<uniform> pick: PickUniforms;

@fragment
fn main() -> @location(0) vec4<u32> {
  // Encode object ID in RGBA (supports up to 2^32 objects)
  let r = pick.objectId & 0xFFu;
  let g = (pick.objectId >> 8u) & 0xFFu;
  let b = (pick.objectId >> 16u) & 0xFFu;
  let a = (pick.objectId >> 24u) & 0xFFu;
  return vec4<u32>(r, g, b, a);
}
"""

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SDF TEXT SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SDF text vertex shader — transforms glyph quads.
sdfTextVertexShader :: WGSLSource
sdfTextVertexShader = WGSLSource
  """
struct FrameUniforms {
  viewProjection: mat4x4<f32>,
  cameraPosition: vec3<f32>,
  time: f32,
}

struct TextUniforms {
  model: mat4x4<f32>,
  color: vec4<f32>,
  outlineColor: vec4<f32>,
  outlineWidth: f32,
  softness: f32,
  _padding: vec2<f32>,
}

@group(0) @binding(0) var<uniform> frame: FrameUniforms;
@group(1) @binding(0) var<uniform> text: TextUniforms;

struct VertexInput {
  @location(0) position: vec3<f32>,
  @location(1) uv: vec2<f32>,
}

struct VertexOutput {
  @builtin(position) clipPosition: vec4<f32>,
  @location(0) uv: vec2<f32>,
}

@vertex
fn main(input: VertexInput) -> VertexOutput {
  var output: VertexOutput;
  let worldPos = text.model * vec4<f32>(input.position, 1.0);
  output.clipPosition = frame.viewProjection * worldPos;
  output.uv = input.uv;
  return output;
}
"""

-- | SDF text fragment shader — renders signed distance field glyphs.
-- | Supports anti-aliasing and outlines.
sdfTextFragmentShader :: WGSLSource
sdfTextFragmentShader = WGSLSource
  """
struct TextUniforms {
  model: mat4x4<f32>,
  color: vec4<f32>,
  outlineColor: vec4<f32>,
  outlineWidth: f32,
  softness: f32,
  _padding: vec2<f32>,
}

@group(1) @binding(0) var<uniform> text: TextUniforms;
@group(1) @binding(1) var fontAtlas: texture_2d<f32>;
@group(1) @binding(2) var fontSampler: sampler;

struct FragmentInput {
  @location(0) uv: vec2<f32>,
}

@fragment
fn main(input: FragmentInput) -> @location(0) vec4<f32> {
  let distance = textureSample(fontAtlas, fontSampler, input.uv).r;
  
  // SDF threshold (0.5 = edge)
  let edge = 0.5;
  
  // Anti-aliasing width based on screen-space derivatives
  let screenPxDistance = fwidth(distance) * text.softness;
  
  // Fill alpha
  let fillAlpha = smoothstep(edge - screenPxDistance, edge + screenPxDistance, distance);
  
  // Outline
  let outlineEdge = edge - text.outlineWidth;
  let outlineAlpha = smoothstep(outlineEdge - screenPxDistance, outlineEdge + screenPxDistance, distance);
  
  // Blend fill and outline
  let outlineBlend = outlineAlpha - fillAlpha;
  let color = mix(text.outlineColor.rgb, text.color.rgb, fillAlpha);
  let alpha = max(fillAlpha * text.color.a, outlineBlend * text.outlineColor.a);
  
  return vec4<f32>(color, alpha);
}
"""

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SKYBOX SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Skybox vertex shader — renders at infinite distance.
skyboxVertexShader :: WGSLSource
skyboxVertexShader = WGSLSource
  """
struct FrameUniforms {
  viewProjection: mat4x4<f32>,
  cameraPosition: vec3<f32>,
  time: f32,
}

@group(0) @binding(0) var<uniform> frame: FrameUniforms;

struct VertexInput {
  @location(0) position: vec3<f32>,
}

struct VertexOutput {
  @builtin(position) clipPosition: vec4<f32>,
  @location(0) localPosition: vec3<f32>,
}

@vertex
fn main(input: VertexInput) -> VertexOutput {
  var output: VertexOutput;
  
  // Remove translation from view matrix (skybox stays at camera)
  var viewNoTranslation = frame.viewProjection;
  viewNoTranslation[3] = vec4<f32>(0.0, 0.0, 0.0, 1.0);
  
  let clipPos = viewNoTranslation * vec4<f32>(input.position, 1.0);
  
  // Set z = w so depth is always at far plane
  output.clipPosition = vec4<f32>(clipPos.xy, clipPos.w, clipPos.w);
  output.localPosition = input.position;
  
  return output;
}
"""

-- | Skybox fragment shader — samples cubemap.
skyboxFragmentShader :: WGSLSource
skyboxFragmentShader = WGSLSource
  """
@group(1) @binding(0) var skyboxTexture: texture_cube<f32>;
@group(1) @binding(1) var skyboxSampler: sampler;

struct FragmentInput {
  @location(0) localPosition: vec3<f32>,
}

@fragment
fn main(input: FragmentInput) -> @location(0) vec4<f32> {
  let color = textureSample(skyboxTexture, skyboxSampler, normalize(input.localPosition));
  return color;
}
"""

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- WIREFRAME SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Wireframe vertex shader — basic transform.
wireframeVertexShader :: WGSLSource
wireframeVertexShader = WGSLSource
  """
struct FrameUniforms {
  viewProjection: mat4x4<f32>,
  cameraPosition: vec3<f32>,
  time: f32,
}

struct ObjectUniforms {
  model: mat4x4<f32>,
  normalMatrix: mat3x3<f32>,
}

@group(0) @binding(0) var<uniform> frame: FrameUniforms;
@group(2) @binding(0) var<uniform> object: ObjectUniforms;

struct VertexInput {
  @location(0) position: vec3<f32>,
  @location(1) barycentric: vec3<f32>,
}

struct VertexOutput {
  @builtin(position) clipPosition: vec4<f32>,
  @location(0) barycentric: vec3<f32>,
}

@vertex
fn main(input: VertexInput) -> VertexOutput {
  var output: VertexOutput;
  let worldPos = object.model * vec4<f32>(input.position, 1.0);
  output.clipPosition = frame.viewProjection * worldPos;
  output.barycentric = input.barycentric;
  return output;
}
"""

-- | Wireframe fragment shader — renders edges using barycentric coordinates.
wireframeFragmentShader :: WGSLSource
wireframeFragmentShader = WGSLSource
  """
struct WireframeUniforms {
  lineColor: vec4<f32>,
  fillColor: vec4<f32>,
  lineWidth: f32,
  _padding: vec3<f32>,
}

@group(1) @binding(0) var<uniform> wireframe: WireframeUniforms;

struct FragmentInput {
  @location(0) barycentric: vec3<f32>,
}

@fragment
fn main(input: FragmentInput) -> @location(0) vec4<f32> {
  // Calculate distance to nearest edge using barycentric coordinates
  let bary = input.barycentric;
  let d = min(min(bary.x, bary.y), bary.z);
  
  // Anti-aliased edge
  let lineWidthPx = wireframe.lineWidth;
  let derivative = fwidth(d);
  let edge = smoothstep(0.0, derivative * lineWidthPx, d);
  
  // Blend line and fill
  return mix(wireframe.lineColor, wireframe.fillColor, edge);
}
"""

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- FULLSCREEN QUAD / POST-PROCESSING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fullscreen vertex shader — generates a fullscreen triangle.
fullscreenVertexShader :: WGSLSource
fullscreenVertexShader = WGSLSource
  """
struct VertexOutput {
  @builtin(position) position: vec4<f32>,
  @location(0) uv: vec2<f32>,
}

@vertex
fn main(@builtin(vertex_index) vertexIndex: u32) -> VertexOutput {
  var output: VertexOutput;
  
  // Generate fullscreen triangle (covers entire screen with single triangle)
  // Vertex 0: (-1, -1), UV (0, 1)
  // Vertex 1: (3, -1),  UV (2, 1)
  // Vertex 2: (-1, 3),  UV (0, -1)
  let x = f32((vertexIndex & 1u) << 2u) - 1.0;
  let y = f32((vertexIndex & 2u) << 1u) - 1.0;
  
  output.position = vec4<f32>(x, y, 0.0, 1.0);
  output.uv = vec2<f32>((x + 1.0) * 0.5, (1.0 - y) * 0.5);
  
  return output;
}
"""

-- | Tonemap fragment shader — converts HDR to LDR with ACES filmic curve.
tonemapFragmentShader :: WGSLSource
tonemapFragmentShader = WGSLSource
  """
struct TonemapUniforms {
  exposure: f32,
  gamma: f32,
  _padding: vec2<f32>,
}

@group(0) @binding(0) var<uniform> tonemap: TonemapUniforms;
@group(0) @binding(1) var hdrTexture: texture_2d<f32>;
@group(0) @binding(2) var hdrSampler: sampler;

struct FragmentInput {
  @location(0) uv: vec2<f32>,
}

// ACES filmic tone mapping curve
// Attempt to approximate the ACES RRT (Reference Rendering Transform)
fn acesFilm(x: vec3<f32>) -> vec3<f32> {
  let a = 2.51;
  let b = 0.03;
  let c = 2.43;
  let d = 0.59;
  let e = 0.14;
  return clamp((x * (a * x + b)) / (x * (c * x + d) + e), vec3<f32>(0.0), vec3<f32>(1.0));
}

@fragment
fn main(input: FragmentInput) -> @location(0) vec4<f32> {
  var hdrColor = textureSample(hdrTexture, hdrSampler, input.uv).rgb;
  
  // Apply exposure
  hdrColor = hdrColor * tonemap.exposure;
  
  // Tone mapping
  let mapped = acesFilm(hdrColor);
  
  // Gamma correction
  let gammaCorrected = pow(mapped, vec3<f32>(1.0 / tonemap.gamma));
  
  return vec4<f32>(gammaCorrected, 1.0);
}
"""


